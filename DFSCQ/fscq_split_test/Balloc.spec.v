Require Import Arith.
Require Import Pred PredCrash.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Array.
Require Import List ListUtils.
Require Import Bool.
Require Import Nomega.
Require Import Idempotent.
Require Import Psatz.
Require Import Rec.
Require Import NArith.
Require Import Log.
Require Import RecArrayUtils.
Require Import LogRecArray.
Require Import ListPred.
Require Import GenSepN.
Require Import WordAuto.
Require Import FSLayout.
Require Import AsyncDisk.
Require Import Cache.
Require Import Rec.

Import ListUtils.

Import ListNotations.

Set Implicit Arguments.


(* Bitmap allocator *)

Module Type AllocSig.

  Parameter xparams : Type.
  Parameter BMPStart : xparams -> addr.
  Parameter BMPLen   : xparams -> addr.
  Parameter xparams_ok : xparams -> Prop.

End AllocSig.

Module Type WordBMapSig.
  Parameter word_size : addr.
  Parameter word_size_ok : Nat.divide word_size valulen.
  Theorem word_size_nonzero : word_size <> 0.
End WordBMapSig.

Module BmpWordSig (Sig : AllocSig) (WBSig : WordBMapSig) <: RASig.
  Import Sig.
  Definition xparams := xparams.
  Definition RAStart := BMPStart.
  Definition RALen := BMPLen.
  Definition xparams_ok := xparams_ok.
  Definition itemtype := Rec.WordF WBSig.word_size.
  Definition items_per_val := valulen / WBSig.word_size.

  Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
End BmpWordSig.

Module BmpWord (Sig : AllocSig) (WBSig : WordBMapSig).
  Module BmpSig := BmpWordSig Sig WBSig.
  Module Bmp := LogRecArray BmpSig.
  Module Defs := Bmp.Defs.

  Import Sig.

  Definition state := word Defs.itemsz.
  Definition full := wones Defs.itemsz.
  Definition state_dec := weq full.
  Definition bit := word 1.
  Definition avail : bit := $0.
  Definition inuse : bit := $1.

  Definition Avail (b : bit) : Prop := b = avail.
  Definition HasAvail (s : state) : Prop := s <> full.

  Definition bits {sz} (s : word sz) : list bit.
    apply (@Rec.of_word (Rec.ArrayF (Rec.WordF 1) sz)).
    cbn. rewrite Nat.mul_1_r.
    exact s.

  Lemma bits_length : forall sz (w : word sz), length (bits w) = sz.

  Lemma bits_cons : forall sz b (w : word sz),
    bits (WS b w) = (WS b WO) :: bits w.

  Definition has_avail (s : state) := if state_dec s then false else true.
  Definition avail_nonzero s i := if (addr_eq_dec i 0) then (has_avail (s ^| wone _)) else has_avail s.

(*
  Lemma HasAvail_has_0 : forall s, HasAvail s -> {i | i < length (bits s) /\ forall d, selN (bits s) i d = avail}.
*)

  Definition ifind_byte (s : state) : option (addr * bit) :=
    ifind_list (fun (b : bit) (_ : addr) => if weq b avail then true else false) (bits s) 0.

  Definition set_bit {sz} (s : word sz) (b : bit) (index : nat) : word sz.
    set (f := @Rec.word_updN (Rec.WordF 1) sz index).
    cbn in *.
    refine (eq_rect (sz * 1) word _ sz (Nat.mul_1_r _)).
    refine (f _ b).
    rewrite Nat.mul_1_r.
    exact s.

  Lemma bits_of_word : forall sz (w : word sz),
    w = eq_rect _ word (@Rec.to_word (Rec.ArrayF (Rec.WordF 1) sz) (bits w)) sz (Nat.mul_1_r sz).

  Lemma bits_set_avail : forall sz (s : word sz) v n, n < sz ->
    bits (set_bit s v n) = updN (bits s) n v.

  Definition free lxp xp bn ms :=
    let index := (bn / Defs.itemsz) in
    let^ (ms, s) <- Bmp.get lxp xp index ms;
    let s' := set_bit s avail (bn mod Defs.itemsz) in
    ms <- Bmp.put lxp xp index s' ms;
    Ret ms.

  (* Get the index of a byte with an available block *)
  Definition ifind_avail_nonzero lxp xp ms :=
    let^ (ms, r) <- Bmp.ifind lxp xp avail_nonzero ms;
    match r with
    | None => Ret ^(ms, None)
    | Some (bn, nonfull) =>
      match ifind_byte (if addr_eq_dec bn 0 then (nonfull ^| wone _) else nonfull) with
      | None =>
        (* won't happen *) Ret ^(ms, None)
      | Some (i, _) =>
        Ret ^(ms, Some (bn, i, nonfull))
      end
    end.

  Definition alloc lxp xp ms :=
    let^ (ms, r) <- ifind_avail_nonzero lxp xp ms;
    match r with
    | None =>
        Ret ^(ms, None)
    | Some (bn, index, s) =>
      let s' := set_bit s inuse index in
        ms <- Bmp.put lxp xp bn s' ms;
        Ret ^(ms, Some (bn * Defs.itemsz + index))
    end.

  Fixpoint bits_to_freelist (l : list bit) (start : addr) : list addr :=
    match l with
    | nil => nil
    | b :: l' =>
      let freelist' := bits_to_freelist l' (S start) in
      if (weq b inuse) then freelist' else
      if (addr_eq_dec start 0) then freelist' else start :: freelist'
    end.

  Definition word_to_freelist {sz} (b : word sz) (start : addr) : list addr :=
    bits_to_freelist (bits b) start.

  Fixpoint itemlist_to_freelist' {sz} (bs : list (word sz)) (start : addr) : list addr :=
    match bs with
    | nil => nil
    | b :: bs' => (word_to_freelist b start) ++ (itemlist_to_freelist' bs' (start + sz))
    end.

  Definition itemlist_to_freelist {sz} bs := @itemlist_to_freelist' sz bs 0.

  Definition get_free_blocks lxp xp ms :=
    let^ (ms, r) <- Bmp.read lxp xp (BMPLen xp) ms;
    Ret ^(ms, itemlist_to_freelist r).

  Definition steal lxp xp bn ms :=
    let index := (bn / Defs.itemsz) in
    let^ (ms, s) <- Bmp.get lxp xp index ms;
    let s' := set_bit s inuse (bn mod Defs.itemsz) in
    ms <- Bmp.put lxp xp index s' ms;
    Ret ms.

  Definition init lxp xp ms :=
    ms <- Bmp.init lxp xp ms;
    Ret ms.

  (* init with no free objects *)
  Definition init_nofree lxp xp ms :=
    ms <- Bmp.init lxp xp ms;
    ms <- Bmp.write lxp xp (repeat full ((BMPLen xp) * BmpSig.items_per_val)) ms;
    Ret ms.

  Definition to_bits {sz} (l : list (word sz)) : list bit :=
    concat (map (@bits sz) l).

  Lemma to_bits_length : forall sz (l : list (word sz)),
    length (to_bits l) = length l * sz.

  Opaque Nat.div Nat.modulo.
  Local Hint Resolve WBSig.word_size_nonzero.
  Local Hint Extern 1 (0 < _) => apply Nat.neq_0_lt_0.

  Definition freelist_bmap_equiv freelist (bmap : list bit) :=
    Forall (fun a => a < length bmap) freelist /\
    forall a, (In a freelist <-> Avail (selN bmap a inuse)).

  Definition rep V FP xp (freelist : list addr) (freepred : @pred _ addr_eq_dec V) :=
    (exists blist, Bmp.rep xp blist *
     [[ NoDup freelist ]] *
     [[ freelist_bmap_equiv freelist (to_bits blist) ]] *
     [[ freepred <=p=> listpred (fun a => exists v, a |-> v * [[ FP v ]]) freelist ]] )%pred.

  Lemma freelist_bmap_equiv_remove_ok : forall bmap freelist a,
    freelist_bmap_equiv freelist bmap ->
    a < length bmap ->
    freelist_bmap_equiv (remove addr_eq_dec a freelist) (updN bmap a inuse).

  Lemma to_bits_updN_set_avail : forall (l : list state) bn v d,
    bn / Defs.itemsz < length l ->
    to_bits (updN l (bn / Defs.itemsz) (set_bit (selN l (bn / Defs.itemsz) d) v (bn mod Defs.itemsz))) =
    updN (to_bits l) bn v.

  Lemma freelist_bmap_equiv_add_ok : forall bmap freelist a,
    freelist_bmap_equiv freelist bmap ->
    a < length bmap ->
    freelist_bmap_equiv (a :: freelist) (updN bmap a avail).

  Lemma is_avail_in_freelist : forall a bmap freelist,
    freelist_bmap_equiv freelist bmap ->
    Avail (selN bmap a inuse) ->
    a < length bmap ->
    In a freelist.

  Lemma bits_len_rewrite : forall xp, BmpSig.RALen xp * BmpSig.items_per_val * Defs.itemsz = BMPLen xp * valulen.

  Lemma bmap_rep_length_ok1 : forall F xp blist d a,
    a < length (to_bits blist) ->
    (F * Bmp.rep xp blist)%pred d ->
    a < BMPLen xp * valulen.

  Lemma bmap_rep_length_ok2 : forall F xp bmap d a,
    (F * Bmp.rep xp bmap)%pred d ->
    a < BMPLen xp * valulen ->
    a / Defs.itemsz < length bmap.

  Lemma bits_rep_bit : forall n x, bits (rep_bit n x) = repeat x n.

  Lemma to_bits_set_bit : forall sz i ii (bytes : list (word sz)) v d,
    i < length bytes ->
    ii < sz ->
    to_bits (updN bytes i (set_bit (selN bytes i d) v ii)) =
    updN (to_bits bytes) (i * sz + ii) v.

  Lemma bound_offset : forall a b c n,
    a < b -> c < n ->
    a * n + c < b * n.

  Theorem selN_to_bits : forall sz n l d,
    sz <> 0 ->
    selN (to_bits l) n d = selN (bits (selN l (n / sz) (rep_bit sz d))) (n mod sz) d.

  Lemma avail_nonzero_is_avail : forall bmap i ii b d d',
    i < length bmap ->
    ifind_byte (selN bmap i d') = Some (ii, b) ->
    Avail (selN (to_bits bmap) (i * Defs.itemsz + ii) d).

  Lemma bits_wor_wone : forall sz (w : word (S sz)),
    bits (w ^| wone _) = inuse :: bits (wtl w).

  Lemma avail_nonzero_first_is_avail : forall bmap ii b d d',
    length bmap > 0 ->
    ifind_byte (selN bmap 0 d' ^| wone _) = Some (ii, b) ->
    Avail (selN (to_bits bmap) ii d).

  Lemma ifind_byte_first_not_zero : forall (w : state) b,
    ifind_byte (w ^| wone _) = Some (0, b) -> False.

  Local Hint Resolve avail_nonzero_is_avail avail_nonzero_first_is_avail ifind_byte_first_not_zero.

  Lemma avail_item0 : forall n d, n < Defs.itemsz -> Avail (selN (bits Bmp.Defs.item0) n d).

  Lemma freelist_bmap_equiv_init_ok : forall xp,
    freelist_bmap_equiv (seq 0 (BMPLen xp * valulen))
      (to_bits (repeat Bmp.Defs.item0 (BmpSig.RALen xp * BmpSig.items_per_val))).

  Lemma bits_to_freelist_bound: forall l start,
    let freelist := bits_to_freelist l start in
    forall x, In x freelist -> start <= x < start + (length l).

  Lemma bits_to_freelist_nodup : forall l start,
    NoDup (bits_to_freelist l start).

  Lemma bits_to_freelist_no_zero : forall l start,
    let freelist := bits_to_freelist l start in
    ~In 0 freelist.

  Lemma bits_to_freelist_spec : forall l start,
    let freelist := bits_to_freelist l start in
    forall i, (start + i <> 0) -> In (start + i) freelist <-> selN l i inuse = avail.

  Lemma itemlist_to_freelist'_bound: forall sz (bs : list (word sz)) start,
    let freelist := itemlist_to_freelist' bs start in
    forall x, In x freelist -> start <= x < start + length (to_bits bs) /\ x > 0.

  Lemma itemlist_to_freelist'_spec: forall sz (bs : list (word sz)) start,
    let freelist := itemlist_to_freelist' bs start in
    forall i, (start + i <> 0) -> In (start + i) freelist <-> selN (to_bits bs) i inuse = avail.
(* TODO move this *)
  Lemma nodup_app: forall T (l1 l2 : list T),
    NoDup l1 -> NoDup l2 ->
    (forall x, In x l1 -> ~In x l2) ->
    (forall x, In x l2 -> ~In x l1) ->
    NoDup (l1 ++ l2).

  Lemma itemlist_to_freelist'_nodup : forall sz (bs : list (word sz)) start,
    let freelist := itemlist_to_freelist' bs start in
    NoDup freelist.

  Lemma itemlist_to_freelist'_no_zero : forall sz (bs : list (word sz)) start,
    let freelist := itemlist_to_freelist' bs start in
    ~In 0 freelist.

  Lemma itemlist_to_freelist_bound: forall sz (bs : list (word sz)),
    let freelist := itemlist_to_freelist bs in
    forall x, In x freelist -> x < length (to_bits bs).

  Lemma itemlist_to_freelist_spec: forall sz (bs : list (word sz)),
    let freelist := itemlist_to_freelist bs in
    forall i, i <> 0 -> In i freelist <-> selN (to_bits bs) i inuse = avail.

  Lemma itemlist_to_freelist_nodup: forall sz bs,
    let freelist := @itemlist_to_freelist sz bs in
    NoDup freelist.

  Lemma itemlist_to_freelist_no_zero: forall sz bs,
    let freelist := @itemlist_to_freelist sz bs in
    ~In 0 freelist.

  Lemma freelist_bmap_equiv_itemlist_to_freelist_spec: forall sz (bs : list (word sz)) freelist,
    NoDup freelist ->
    freelist_bmap_equiv freelist (to_bits bs) ->
    permutation addr_eq_dec (itemlist_to_freelist bs) (remove addr_eq_dec 0 freelist).

  Hint Extern 0 (okToUnify (listpred ?prd _ ) (listpred ?prd _)) => constructor : okToUnify.

  Theorem init_ok : forall V FP lxp xp ms,
    {< F Fm m0 sm m bl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (BMPStart xp) bl) ]]] *
          [[ xparams_ok xp /\ BMPStart xp <> 0 /\ length bl = BMPLen xp ]]
    POST:hm' RET:ms exists m' freelist freepred,
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp freelist freepred) ]]] *
          [[ forall bn, bn < (BMPLen xp) * valulen -> In bn freelist ]] *
          [[ forall dl, length dl = ((BMPLen xp) * valulen)%nat ->
               Forall FP dl ->
               arrayN (@ptsto _ _ _) 0 dl =p=> freepred ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} init lxp xp ms.

  Lemma full_eq_repeat : full = rep_bit Defs.itemsz inuse.

  Lemma ifind_byte_inb : forall x n b,
    ifind_byte x = Some (n, b) ->
    n < Defs.itemsz.

  Theorem init_nofree_ok : forall V FP lxp xp ms,
    {< F Fm m0 sm m bl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (BMPStart xp) bl) ]]] *
          [[ xparams_ok xp /\ BMPStart xp <> 0 /\ length bl = BMPLen xp ]]
    POST:hm' RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp nil emp) ]]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} init_nofree lxp xp ms.

  Theorem get_free_blocks_ok : forall V FP lxp xp ms,
    {<F Fm m0 sm m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred) ]]]
    POST:hm' RET:^(ms, r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
          [[ ~In 0 r ]] * [[ NoDup r ]] *
          [[ permutation addr_eq_dec r (remove addr_eq_dec 0 freelist) ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} get_free_blocks lxp xp ms.

  Theorem steal_ok : forall V FP lxp xp bn ms,
    {< F Fm m0 sm m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred) ]]] *
          [[ In bn freelist ]]
    POST:hm' RET:ms exists m' freepred',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp (remove addr_eq_dec bn freelist) freepred') ]]] *
          [[ freepred =p=> freepred' * (exists v, bn |-> v * [[ FP v ]]) ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} steal lxp xp bn ms.

  Theorem alloc_ok : forall V FP lxp xp ms,
    {< F Fm m0 sm m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred) ]]]
    POST:hm' RET:^(ms,r)
          [[ r = None ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm'
       \/ exists bn m' freepred',
          [[ r = Some bn ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp (remove addr_eq_dec bn freelist) freepred') ]]] *
          [[ freepred =p=> freepred' * (exists v, bn |-> v * [[ FP v ]]) ]] *
          [[ bn <> 0 /\ bn < (BMPLen xp) * valulen ]] *
          [[ In bn freelist ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} alloc lxp xp ms.


  Theorem free_ok : forall V FP lxp xp bn ms,
    {< F Fm m0 sm m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[ bn < (BMPLen xp) * valulen ]] *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred) ]]] *
          [[ exists mx Fx, (Fx * freepred * bn |->?)%pred mx ]]
    POST:hm' RET:ms exists m' freepred',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp (bn :: freelist) freepred') ]]] *
          [[ forall v, FP v -> bn |-> v * freepred =p=> freepred' ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} free lxp xp bn ms.

  Hint Extern 1 ({{_}} Bind (init _ _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_}} Bind (init_nofree _ _ _) _) => apply init_nofree_ok : prog.
  Hint Extern 1 ({{_}} Bind (get_free_blocks _ _ _) _) => apply get_free_blocks_ok : prog.
  Hint Extern 1 ({{_}} Bind (steal _ _ _ _) _) => apply steal_ok : prog.
  Hint Extern 1 ({{_}} Bind (alloc _ _ _) _) => apply alloc_ok : prog.
  Hint Extern 1 ({{_}} Bind (free _ _ _ _) _) => apply free_ok : prog.
  Hint Extern 0 (okToUnify (rep _ _ _ _) (rep _ _ _ _)) => constructor : okToUnify.


  Lemma rep_impl_bn_ok: forall F V FP xp freelist freepred m bn,
    (F * @rep V FP xp freelist freepred)%pred (list2nmem m) ->
    In bn freelist -> 
    bn < (Sig.BMPLen xp) * valulen.

  Lemma rep_impl_NoDup: forall F V FP xp freelist freepred m,
    (F * @rep V FP xp freelist freepred)%pred (list2nmem m) ->
    NoDup freelist.


  Lemma xform_rep : forall V FP xp l p,
    crash_xform (@rep V FP xp l p) <=p=> @rep V FP xp l p.

  Lemma xform_rep_rawpred : forall xp FP l p,
    (forall a, crash_xform (exists v, a |-> v * [[ FP v ]]) =p=> exists v, a |-> v * [[ FP v ]]) ->
    crash_xform (rep FP xp l p) =p=> rep FP xp l p * [[ crash_xform p =p=> p ]].


End BmpWord.

Module ByteBmap <: WordBMapSig.
  Import Rec.

  Definition word_size := 8.
  Definition type := ArrayF (WordF 1) word_size.

  Theorem word_size_ok : Nat.divide word_size valulen.

  Theorem word_size_nonzero : word_size <> 0.

End ByteBmap.

Module BmapAlloc (Sig : AllocSig) := BmpWord Sig ByteBmap.

(* BmapAlloc with a list of free items to speed up allocation *)

Module BmapAllocCache (Sig : AllocSig).

  Module Alloc := BmapAlloc Sig.
  Module Defs := Alloc.Defs.

  Definition BmapCacheType := option (list addr).

  Record memstate := mk_memstate {
    MSLog  : LOG.memstate;
    MSCache   : BmapCacheType; 
  }.

  Definition freelist0 : BmapCacheType := None.

  Definition init lxp xp fms : prog memstate :=
    fms <- Alloc.init lxp xp fms;
    Ret (mk_memstate fms freelist0 ).

  (* init with no free objects *)
  Definition init_nofree lxp xp ms :=
    fms <- Alloc.init_nofree lxp xp ms;
    Ret (mk_memstate fms freelist0).

  Definition get_free_blocks lxp xp ms :=
    match (MSCache ms) with
    | Some x => Ret ^(ms, x)
    | None =>
      let^ (fms, freelist) <- Alloc.get_free_blocks lxp xp (MSLog ms);
      Ret ^((mk_memstate fms (Some freelist)), freelist)
    end.

  Definition cache_free_block a ms :=
    match (MSCache ms) with
    | Some x => Some (a :: x)
    | None => None
    end.

  Definition alloc lxp xp (ms : memstate) :=
    let^ (ms, freelist) <- get_free_blocks lxp xp ms;
    match freelist with
    | nil =>
      Ret ^(ms, None)
    | bn :: freelist' =>
      fms <- Alloc.steal lxp xp bn (MSLog ms);
      Ret ^((mk_memstate fms (Some freelist')), Some bn)
    end.

  Definition free lxp xp bn ms :=
    fms <- Alloc.free lxp xp bn (MSLog ms);
    let cache := cache_free_block bn ms in
    Ret (mk_memstate fms cache).

  Definition steal lxp xp bn (ms:memstate) :=
    fms <- Alloc.steal lxp xp bn (MSLog ms) ;
    Ret (mk_memstate fms freelist0).

  Definition cache_rep (freelist : list addr) cache :=
    forall cfreelist, cache = Some cfreelist ->
    ~In 0 cfreelist /\ NoDup cfreelist /\
    permutation addr_eq_dec (remove addr_eq_dec 0 freelist) cfreelist.

  Definition rep V FP xp freelist (freepred : @pred _ addr_eq_dec V) ms :=
    (Alloc.rep FP xp freelist freepred *
    [[ cache_rep freelist (MSCache ms) ]])%pred.

  Fact cache_rep_freelist0: forall freelist, cache_rep freelist freelist0.

  Hint Resolve cache_rep_freelist0.

  Lemma cache_rep_remove_cons: forall freelist n cache',
    cache_rep freelist (Some (n :: cache')) ->
    cache_rep (remove addr_eq_dec n freelist) (Some cache').

  Lemma cache_rep_add_cons: forall freelist x cache,
    cache_rep freelist (Some cache) ->
    x <> 0 -> ~In x cache ->
    cache_rep (x :: freelist) (Some (x :: cache)).

  Lemma cache_rep_in: forall bn freelist cache,
    cache_rep freelist (Some cache) ->
    bn <> 0 ->
    In bn freelist <-> In bn cache.

  Lemma cache_rep_none: forall freelist,
    cache_rep freelist None.

  Hint Resolve cache_rep_none.

  Ltac apply_cache_rep := match goal with
    | Hm: MSCache _ = _, H: cache_rep _ _ |- _ =>
      rewrite ?Hm in *; specialize (H _ eq_refl) as ?; intuition
    end.

  Theorem init_ok : forall V FP lxp xp ms,
    {< F Fm m0 sm m bl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (Sig.BMPStart xp) bl) ]]] *
          [[ Sig.xparams_ok xp /\ Sig.BMPStart xp <> 0 /\ length bl = Sig.BMPLen xp ]]
    POST:hm' RET:ms exists m' freepred freelist,
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp freelist freepred ms) ]]] *
          [[ forall bn, bn < (Sig.BMPLen xp) * valulen -> In bn freelist ]] *
          [[ forall dl, length dl = ((Sig.BMPLen xp) * valulen)%nat ->
               Forall FP dl ->
               arrayN (@ptsto _ _ _) 0 dl =p=> freepred ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} init lxp xp ms.

  Theorem init_nofree_ok : forall V FP lxp xp ms,
    {< F Fm m0 sm m bl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (Sig.BMPStart xp) bl) ]]] *
          [[ Sig.xparams_ok xp /\ Sig.BMPStart xp <> 0 /\ length bl = Sig.BMPLen xp ]]
    POST:hm' RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp nil emp ms) ]]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} init_nofree lxp xp ms.

  Theorem get_free_blocks_ok : forall V FP lxp xp (ms:memstate),
    {< F Fm m0 sm m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred ms) ]]]
    POST:hm' RET:^(ms, r)
          [[ MSCache ms = Some r ]] *
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm' *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred ms) ]]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} get_free_blocks lxp xp ms.

  Hint Extern 0 ({{ _ }} Bind (get_free_blocks _ _ _) _) => apply get_free_blocks_ok : prog.

  Theorem alloc_ok : forall V FP lxp xp ms,
    {< F Fm m0 sm m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred ms) ]]]
    POST:hm' RET:^(ms,r)
          [[ r = None ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm'
       \/ exists bn m' freepred',
          [[ r = Some bn ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp (remove addr_eq_dec bn freelist) freepred' ms) ]]] *
          [[ freepred =p=> freepred' * (exists v, bn |-> v * [[ FP v ]]) ]] *
          [[ bn <> 0 /\ bn < (Sig.BMPLen xp) * valulen ]] *
          [[ In bn freelist ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} alloc lxp xp ms.

  Theorem free_ok : forall V FP lxp xp bn ms,
    {< F Fm m0 sm m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm *
          [[ bn <> 0 ]] *
          [[ bn < (Sig.BMPLen xp) * valulen ]] *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred ms) ]]] *
          [[ exists mx Fx, (Fx * freepred * bn |->?)%pred mx ]]
    POST:hm' RET:ms exists m' freepred',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp (bn :: freelist) freepred' ms) ]]] *
          [[ forall v, FP v -> bn |-> v * freepred =p=> freepred' ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} free lxp xp bn ms.

  Theorem steal_ok : forall V FP lxp xp bn (ms:memstate),
    {< F Fm m0 sm m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred ms)]]] *
          [[ In bn freelist /\ bn < (Sig.BMPLen xp) * valulen ]]
    POST:hm' RET:ms exists m' freepred',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
          [[[ m' ::: (Fm * @rep V FP xp (remove addr_eq_dec bn freelist) freepred' ms) ]]] *
          [[ freepred =p=> freepred' * (exists v, bn |-> v * [[ FP v ]]) ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} steal lxp xp bn ms.

  Hint Extern 1 ({{_}} Bind (init _ _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_}} Bind (init_nofree _ _ _) _) => apply init_nofree_ok : prog.
  Hint Extern 1 ({{_}} Bind (steal _ _ _ _) _) => apply steal_ok : prog.
  Hint Extern 1 ({{_}} Bind (alloc _ _ _) _) => apply alloc_ok : prog.
  Hint Extern 1 ({{_}} Bind (free _ _ _ _) _) => apply free_ok : prog.
  Hint Extern 0 (okToUnify (rep _ _ _ _ _) (rep _ _ _ _ _)) => constructor : okToUnify.

  Lemma xform_rep : forall V FP xp l ms p,
    crash_xform (@rep V FP xp l ms p) <=p=> @rep V FP xp l ms p.

  Lemma xform_rep_rawpred : forall xp FP l ms p,
    (forall a, crash_xform (exists v, a |-> v * [[ FP v ]]) =p=> exists v, a |-> v * [[ FP v ]]) ->
    crash_xform (rep FP xp l p ms) =p=> (rep FP xp l p ms) * [[ crash_xform p =p=> p ]].

  Lemma rep_clear_mscache_ok : forall V FP bxps frees freepred lms cm,
    @rep V FP bxps frees freepred (mk_memstate lms cm) =p=>
    @rep V FP bxps frees freepred (mk_memstate lms freelist0).

  Lemma rep_ignore_mslog_ok: forall V (FP : V -> _) xp freelist freepred log log' cache,
    rep FP xp freelist freepred (mk_memstate log cache) =
    rep FP xp freelist freepred (mk_memstate log' cache).

  Lemma rep_clear_cache: forall V FP xp freelist freepred ms mslog,
    @rep V FP xp freelist freepred ms =p=>
    rep FP xp freelist freepred (mk_memstate mslog freelist0).

  Hint Extern 0 (okToUnify (rep _ ?xp _ _ _) (rep _ ?xp _ _ _)) => apply rep_ignore_mslog_ok : okToUnify.

End BmapAllocCache.


(* Specialize for actual on-disk-block allocation *)

Module BALLOC.

  Module Sig <: AllocSig.
    Definition xparams := balloc_xparams.
    Definition BMPStart := BmapStart.
    Definition BMPLen := BmapNBlocks.

    (* should return an address that fits in addrlen (goodSize addrlen _).
       valulen * valulen supports about 2^48 bytes of disk space *)
    Definition xparams_ok xp := (BmapNBlocks xp) <= valulen * valulen.
  End Sig.

  Module Alloc := BmapAlloc Sig.
  Module Defs := Alloc.Defs.

  Definition alloc lxp xp ms :=
    r <- Alloc.alloc lxp xp ms;
    Ret r.

  Definition free lxp xp bn ms :=
    r <- Alloc.free lxp xp bn ms;
    Ret r.

  Definition steal lxp xp bn ms :=
    r <- Alloc.steal lxp xp bn ms;
    Ret r.

  Definition init lxp xp ms :=
    r <- Alloc.init lxp xp ms;
    Ret r.

  Definition init_nofree lxp xp ms :=
    r <- Alloc.init_nofree lxp xp ms;
    Ret r.

  Definition bn_valid xp bn := bn <> 0 /\ bn < (BmapNBlocks xp) * valulen.

  Definition FP (x : valuset) := True.

  Definition rep xp (freeblocks : list addr) :=
    ( exists freepred, freepred * Alloc.rep FP xp freeblocks freepred)%pred.

  Definition smrep (freeblocks : list addr) : @pred _ addr_eq_dec bool :=
    (listpred (fun a => a |->?) freeblocks)%pred.

  Lemma listpred_seq_smrep: forall F xp fp m l freelist,
    (F * Alloc.rep FP xp freelist fp)%pred m ->
    (LOG.arrayP 0 l =p=> fp) ->
    listpred (fun a => a |->?) (seq 0 (length l)) =p=> smrep freelist.

  Theorem init_ok : forall lxp xp ms,
    {< F Fm Fs m0 sm m bl dl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) 0 dl
                        * arrayN (@ptsto _ _ _) (BmapStart xp) bl) ]]] *
          [[ (Fs * listpred (fun a => a |->?) (seq 0 (length dl)))%pred sm ]] *
          [[ (BmapNBlocks xp) <= valulen * valulen /\ BmapStart xp <> 0 ]] *
          [[ length bl = BmapNBlocks xp /\ length dl = ((BmapNBlocks xp) * valulen)%nat ]]
    POST:hm' RET:ms exists m' freeblocks,
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
          [[[ m' ::: (Fm * rep xp freeblocks) ]]] *
          [[ (Fs * smrep freeblocks)%pred sm ]] *
          [[ forall bn, bn < (BmapNBlocks xp) * valulen -> In bn freeblocks ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} init lxp xp ms.

  Theorem init_nofree_ok : forall lxp xp ms,
    {< F Fs Fm m0 sm m bl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (BmapStart xp) bl) ]]] *
          [[ Fs sm ]] *
          [[ (BmapNBlocks xp) <= valulen * valulen /\ BmapStart xp <> 0 ]] *
          [[ length bl = BmapNBlocks xp ]]
    POST:hm' RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
          [[[ m' ::: (Fm * rep xp nil) ]]] *
          [[ (Fs * smrep nil)%pred sm ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} init_nofree lxp xp ms.

  Theorem steal_ok : forall lxp xp bn ms,
    {< F Fm Fs m0 sm m freeblocks,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * rep xp freeblocks) ]]] *
          [[ (Fs * smrep freeblocks)%pred sm ]] *
          [[ bn_valid xp bn /\ In bn freeblocks ]]
    POST:hm' RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
          [[[ m' ::: (Fm * bn |->? * rep xp (remove addr_eq_dec bn freeblocks)) ]]] *
          [[ (Fs * bn |->? * smrep (remove addr_eq_dec bn freeblocks))%pred sm ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} steal lxp xp bn ms.


  Theorem alloc_ok : forall lxp xp ms,
    {< F Fm Fs m0 sm m freeblocks,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: (Fm * rep xp freeblocks) ]]] *
           [[ (Fs * smrep freeblocks)%pred sm ]]
    POST:hm' RET:^(ms, r)
           [[ r = None ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm'
        \/ exists bn m',
           [[ r = Some bn ]] * [[ bn_valid xp bn ]] *
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
           [[[ m' ::: (Fm * bn |->? * rep xp (remove addr_eq_dec bn freeblocks)) ]]] *
           [[ (Fs * bn |->? * smrep (remove addr_eq_dec bn freeblocks))%pred sm ]] *
           [[ In bn freeblocks ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} alloc lxp xp ms.

  Theorem free_ok : forall lxp xp bn ms,
    {< F Fm Fs m0 sm m freeblocks,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[ bn_valid xp bn ]] *
           [[[ m ::: (Fm * rep xp freeblocks * bn |->?) ]]] *
           [[ (Fs * bn |->? * smrep freeblocks)%pred sm ]]
    POST:hm' RET:ms exists m',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
           [[[ m' ::: (Fm * rep xp (bn :: freeblocks)) ]]] *
           [[ (Fs * smrep (bn :: freeblocks))%pred sm ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} free lxp xp bn ms.


  Hint Extern 1 ({{_}} Bind (init _ _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_}} Bind (init_nofree _ _ _) _) => apply init_nofree_ok : prog.
  Hint Extern 1 ({{_}} Bind (steal _ _ _ _) _) => apply steal_ok : prog.
  Hint Extern 1 ({{_}} Bind (alloc _ _ _) _) => apply alloc_ok : prog.
  Hint Extern 1 ({{_}} Bind (free _ _ _ _) _) => apply free_ok : prog.
  Hint Extern 0 (okToUnify (rep ?xp _) (rep ?xp _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (smrep ?l) (smrep ?l)) => constructor : okToUnify.


  Lemma sep_star_reorder_helper : forall a b c d : (@pred _ addr_eq_dec valuset),
    ((a * b) * (c * d)) =p=> d * (a * b * c).

  Lemma smrep_cons: forall l a b,
    smrep l * a |-> b =p=> smrep (a :: l).

  Definition freevec lxp xp l ms :=
    let^ (ms) <- ForN i < length l
    Hashmap hm
    Ghost [ F Fm Fs crash m0 freeblocks sm ]
    Loopvar [ ms ]
    Invariant
      exists m', LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm *
      [[[ m' ::: (Fm * rep xp (rev (firstn i l) ++ freeblocks)) *
                       listpred (fun a => a |->?) (skipn i l) ]]] *
      [[ (Fs * smrep (rev (firstn i l) ++ freeblocks) *
                       listpred (fun a => a |->?) (skipn i l))%pred sm ]]
    OnCrash crash
    Begin
      ms <- free lxp xp (selN l i 0) ms;
      Ret ^(ms)
    Rof ^(ms);
    Ret ms.


  Theorem freevec_ok : forall lxp xp l ms,
    {< F Fm Fs m0 sm m freeblocks,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[ Forall (bn_valid xp) l ]] *
           [[[ m ::: (Fm * rep xp freeblocks * listpred (fun a => a |->?) l ) ]]] *
           [[ (Fs * listpred (fun a => a |->?) l * smrep freeblocks)%pred sm ]]
    POST:hm' RET:ms exists m',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
           [[[ m' ::: (Fm * rep xp (rev l ++ freeblocks)) ]]] *
           [[ (Fs * smrep (rev l ++ freeblocks))%pred sm ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} freevec lxp xp l ms.

  Hint Extern 1 ({{_}} Bind (freevec _ _ _ _) _) => apply freevec_ok : prog.


  Lemma xparams_ok_goodSize : forall xp a,
    Sig.xparams_ok xp ->
    a < (BmapNBlocks xp) * valulen ->
    goodSize addrlen a.

  Lemma bn_valid_goodSize : forall F l m xp a,
    (F * rep xp l)%pred m ->
    bn_valid xp a ->
    goodSize addrlen a.

  Lemma bn_valid_goodSize_pimpl : forall l xp,
    rep xp l <=p=> [[ forall a, bn_valid xp a -> goodSize addrlen a ]] * rep xp l.

  Lemma bn_valid_facts : forall xp bn,
    bn_valid xp bn -> bn <> 0 /\ bn < (BmapNBlocks xp) * valulen.

  Theorem bn_valid_roundtrip' : forall xp a,
    Sig.xparams_ok xp ->
    bn_valid xp a ->
    bn_valid xp (# (natToWord addrlen a)).

  Theorem bn_valid_roundtrip : forall xp a F l m,
    (F * rep xp l)%pred m ->
    bn_valid xp a ->
    bn_valid xp (# (natToWord addrlen a)).

  Lemma bn_valid_switch : forall xp1 xp2,
    BmapNBlocks xp1 = BmapNBlocks xp2 ->
    bn_valid xp1 = bn_valid xp2.

  Definition items_per_val := Alloc.BmpSig.items_per_val.


  Theorem xform_rep : forall xp l,
    crash_xform (rep xp l) =p=> rep xp l.

End BALLOC.


Module BALLOCC.

  Module Sig <: AllocSig.
    Definition xparams := balloc_xparams.
    Definition BMPStart := BmapStart.
    Definition BMPLen := BmapNBlocks.

    (* should return an address that fits in addrlen (goodSize addrlen _).
       valulen * valulen supports about 2^48 bytes of disk space *)
    Definition xparams_ok xp := (BmapNBlocks xp) <= valulen * valulen.
  End Sig.

  Module Alloc := BmapAllocCache Sig.
  Module Defs := Alloc.Defs.

  Definition BmapCacheType := Alloc.BmapCacheType.
  Definition MSLog := Alloc.MSLog.
  Definition MSCache := Alloc.MSCache.
  Definition upd_memstate lms ms := Alloc.mk_memstate lms (Alloc.MSCache ms).
  Definition mk_memstate lms cms := Alloc.mk_memstate lms cms.

  Definition alloc lxp xp ms :=
    r <- Alloc.alloc lxp xp ms;
    Ret r.

  Definition free lxp xp bn ms :=
    r <- Alloc.free lxp xp bn ms;
    Ret r.

  Definition steal lxp xp bn ms :=
    r <- Alloc.steal lxp xp bn ms;
    Ret r.

  Definition init lxp xp ms :=
    r <- Alloc.init lxp xp ms;
    Ret r.

  Definition init_nofree lxp xp ms :=
    r <- Alloc.init_nofree lxp xp ms;
    Ret r.

  Definition bn_valid xp bn := bn <> 0 /\ bn < (BmapNBlocks xp) * valulen.

  Definition FP (x : valuset) := True.

  Definition rep xp (freeblocks : list addr) ms :=
    ( exists freepred, freepred * Alloc.rep FP xp freeblocks freepred ms)%pred.

  Definition smrep (freeblocks : list addr) : @pred _ addr_eq_dec bool :=
    (listpred (fun a => a |->?) freeblocks)%pred.

  Lemma listpred_seq_smrep: forall F xp fp ms m l freelist,
    (F * Alloc.rep FP xp freelist fp ms)%pred m ->
    (LOG.arrayP 0 l =p=> fp) ->
    listpred (fun a => a |->?) (seq 0 (length l)) =p=> smrep freelist.

  Lemma rep_ignore_mslog_ok: forall bxps frees lms lms' cm,
    rep bxps frees (mk_memstate lms cm) =p=>
    rep bxps frees (mk_memstate lms' cm).

  Lemma rep_clear_mscache_ok : forall bxps frees lms cm,
    rep bxps frees (mk_memstate lms cm) =p=>
    rep bxps frees (mk_memstate lms Alloc.freelist0).

  Theorem init_ok : forall lxp xp ms,
    {< F Fm Fs m0 sm m bl dl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) 0 dl
                        * arrayN (@ptsto _ _ _) (BmapStart xp) bl) ]]] *
          [[ (Fs * listpred (fun a => a |->?) (seq 0 (length dl)))%pred sm ]] *
          [[ (BmapNBlocks xp) <= valulen * valulen /\ BmapStart xp <> 0 ]] *
          [[ length bl = BmapNBlocks xp /\ length dl = ((BmapNBlocks xp) * valulen)%nat ]]
    POST:hm' RET:ms exists m' freeblocks,
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
          [[[ m' ::: (Fm * rep xp freeblocks ms) ]]] *
          [[ (Fs * smrep freeblocks)%pred sm ]] *
          [[ forall bn, bn < (BmapNBlocks xp) * valulen -> In bn freeblocks ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} init lxp xp ms.

  Theorem init_nofree_ok : forall lxp xp ms,
    {< F Fm Fs m0 sm m bl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (BmapStart xp) bl) ]]] *
          [[ Fs sm ]] *
          [[ (BmapNBlocks xp) <= valulen * valulen /\ BmapStart xp <> 0 ]] *
          [[ length bl = BmapNBlocks xp ]]
    POST:hm' RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
          [[ (Fs * smrep nil)%pred sm ]] *
          [[[ m' ::: (Fm * rep xp nil ms) ]]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} init_nofree lxp xp ms.

  Theorem steal_ok : forall lxp xp bn ms,
    {< F Fm Fs m0 sm m freeblocks,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm *
          [[[ m ::: (Fm * rep xp freeblocks ms) ]]] *
          [[ (Fs * smrep freeblocks)%pred sm ]] *
          [[ bn_valid xp bn /\ In bn freeblocks ]]
    POST:hm' RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
          [[[ m' ::: (Fm * bn |->? * 
           rep xp (remove addr_eq_dec bn freeblocks) ms) ]]] *
          [[ (Fs * bn |->? * smrep (remove addr_eq_dec bn freeblocks))%pred sm ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} steal lxp xp bn ms.


  Theorem alloc_ok : forall lxp xp ms,
    {< F Fm Fs m0 sm m freeblocks,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm *
           [[[ m ::: (Fm * rep xp freeblocks ms) ]]] *
           [[ (Fs * smrep freeblocks)%pred sm ]]
    POST:hm' RET:^(ms, r)
           [[ r = None ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm'
        \/ exists bn m',
           [[ r = Some bn ]] * [[ bn_valid xp bn ]] *
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
           [[[ m' ::: (Fm * bn |->? * 
            rep xp (remove addr_eq_dec bn freeblocks) ms) ]]] *
           [[ (Fs * bn |->? * smrep (remove addr_eq_dec bn freeblocks))%pred sm ]] *
           [[ In bn freeblocks ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} alloc lxp xp ms.

  Theorem free_ok : forall lxp xp bn ms,
    {< F Fm Fs m0 sm m freeblocks,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm *
           [[ bn_valid xp bn ]] *
           [[[ m ::: (Fm * rep xp freeblocks ms* bn |->?) ]]] *
           [[ (Fs * bn |->? * smrep freeblocks)%pred sm ]]
    POST:hm' RET:ms exists m',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
           [[[ m' ::: (Fm * rep xp (bn :: freeblocks) ms) ]]] *
           [[ (Fs * smrep (bn :: freeblocks))%pred sm ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} free lxp xp bn ms.


  Hint Extern 1 ({{_}} Bind (init _ _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_}} Bind (init_nofree _ _ _) _) => apply init_nofree_ok : prog.
  Hint Extern 1 ({{_}} Bind (steal _ _ _ _) _) => apply steal_ok : prog.
  Hint Extern 1 ({{_}} Bind (alloc _ _ _) _) => apply alloc_ok : prog.
  Hint Extern 1 ({{_}} Bind (free _ _ _ _) _) => apply free_ok : prog.
  Hint Extern 0 (okToUnify (rep ?xp _ _) (rep ?xp _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (smrep ?l) (smrep ?l)) => constructor : okToUnify.

  Lemma sep_star_reorder_helper : forall a b c d : (@pred _ addr_eq_dec valuset),
    ((a * b) * (c * d)) =p=> d * (a * b * c).

  Lemma smrep_cons: forall l a b,
    smrep l * a |-> b =p=> smrep (a :: l).

  Definition freevec lxp xp l ms :=
    let^ (ms) <- ForN i < length l
    Hashmap hm
    Ghost [ F Fm Fs crash m0 sm freeblocks ]
    Loopvar [ ms ]
    Invariant
      exists m', LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm *
      [[[ m' ::: (Fm * rep xp (rev (firstn i l) ++ freeblocks) ms) *
                       listpred (fun a => a |->?) (skipn i l) ]]] *
      [[ (Fs * smrep (rev (firstn i l) ++ freeblocks) *
                       listpred (fun a => a |->?) (skipn i l))%pred sm ]]
    OnCrash crash
    Begin
      ms <- free lxp xp (selN l i 0) ms;
      Ret ^(ms)
    Rof ^(ms);
    Ret ms.


  Theorem freevec_ok : forall lxp xp l ms,
    {< F Fs Fm m0 sm m freeblocks,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm hm *
           [[ Forall (bn_valid xp) l ]] *
           [[[ m ::: (Fm * rep xp freeblocks ms * listpred (fun a => a |->?) l ) ]]] *
           [[ (Fs * listpred (fun a => a |->?) l * smrep freeblocks)%pred sm ]]
    POST:hm' RET:ms exists m',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm hm' *
           [[[ m' ::: (Fm * rep xp (rev l ++ freeblocks) ms) ]]] *
           [[ (Fs * smrep (rev l ++ freeblocks))%pred sm ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} freevec lxp xp l ms.

  Hint Extern 1 ({{_}} Bind (freevec _ _ _ _) _) => apply freevec_ok : prog.


  Lemma xparams_ok_goodSize : forall xp a,
    Sig.xparams_ok xp ->
    a < (BmapNBlocks xp) * valulen ->
    goodSize addrlen a.

  Lemma bn_valid_goodSize : forall F l m ms xp a,
    (F * rep xp l ms)%pred m ->
    bn_valid xp a ->
    goodSize addrlen a.

  Lemma bn_valid_goodSize_pimpl : forall l xp ms,
    rep xp l ms <=p=> [[ forall a, bn_valid xp a -> goodSize addrlen a ]] * rep xp l ms.

  Lemma bn_valid_facts : forall xp bn,
    bn_valid xp bn -> bn <> 0 /\ bn < (BmapNBlocks xp) * valulen.

  Theorem bn_valid_roundtrip' : forall xp a,
    Sig.xparams_ok xp ->
    bn_valid xp a ->
    bn_valid xp (# (natToWord addrlen a)).

  Theorem bn_valid_roundtrip : forall xp a F l ms m,
    (F * rep xp l ms)%pred m ->
    bn_valid xp a ->
    bn_valid xp (# (natToWord addrlen a)).

  Lemma bn_valid_switch : forall xp1 xp2,
    BmapNBlocks xp1 = BmapNBlocks xp2 ->
    bn_valid xp1 = bn_valid xp2.

  Definition items_per_val := Alloc.Alloc.BmpSig.items_per_val.


  Theorem xform_rep : forall xp l ms,
    crash_xform (rep xp l ms) =p=> rep xp l ms.


End BALLOCC.


(* Specialize for inode allocation *)

Module IAlloc.

  Module Sig <: AllocSig.
    Definition xparams     := fs_xparams.
    Definition BMPStart xp := BmapStart (FSXPInodeAlloc xp).
    Definition BMPLen   xp := BmapNBlocks (FSXPInodeAlloc xp).

    (* should return an address that fits in addrlen (goodSize addrlen _).
       valulen * valulen supports about 2^48 inodes *)
    Definition xparams_ok xp := (BMPLen xp) <= valulen * valulen.
  End Sig.

  Module Alloc := BmapAllocCache Sig.
  Module Defs := Alloc.Defs.

  Definition BmapCacheType := Alloc.BmapCacheType.
  Definition MSLog := Alloc.MSLog.
  Definition MSCache := Alloc.MSCache.
  Definition mk_memstate := Alloc.mk_memstate.

  Definition init := Alloc.init.

  Definition alloc := Alloc.alloc.

  Definition free := Alloc.free.

  Definition rep := Alloc.rep.

  Definition ino_valid xp ino := ino < (Sig.BMPLen xp) * valulen.

  Definition init_ok := Alloc.init_ok.

  Definition alloc_ok := Alloc.alloc_ok.

  Definition free_ok := Alloc.free_ok.

  Definition items_per_val := Alloc.Alloc.BmpSig.items_per_val.

  Hint Extern 1 ({{_}} Bind (init _ _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_}} Bind (alloc _ _ _) _) => apply alloc_ok : prog.
  Hint Extern 1 ({{_}} Bind (free _ _ _ _) _) => apply free_ok : prog.
  Hint Extern 0 (okToUnify (rep _ ?xp _ _ _) (rep _ ?xp _ _ _)) => constructor : okToUnify.

  Definition xform_rep := Alloc.xform_rep.

  Lemma xparams_ok_goodSize : forall xp ino,
    Sig.xparams_ok xp ->
    ino_valid xp ino ->
    goodSize addrlen ino.

  Lemma ino_valid_goodSize : forall V FP F l m xp a prd allocc,
    (F * @rep V FP xp l prd allocc)%pred m ->
    ino_valid xp a ->
    goodSize addrlen a.

  Lemma ino_valid_goodSize_pimpl : forall V FP l xp p allocc,
    @rep V FP xp l p allocc <=p=> [[ forall a, ino_valid xp a -> goodSize addrlen a ]] * rep FP xp l p allocc.

  Theorem ino_valid_roundtrip' : forall xp a,
    Sig.xparams_ok xp ->
    ino_valid xp a ->
    ino_valid xp (# (natToWord addrlen a)).

  Theorem ino_valid_roundtrip : forall V FP xp a F l m p allocc,
    (F * @rep V FP xp l p allocc)%pred m ->
    ino_valid xp a ->
    ino_valid xp (# (natToWord addrlen a)).

  Lemma rep_clear_cache: forall V FP xp freelist freepred ms mslog,
    @rep V FP xp freelist freepred ms =p=>
    rep FP xp freelist freepred (mk_memstate mslog Alloc.freelist0).

  Hint Extern 0 (okToUnify (rep _ ?xp _ _ _) _) => unfold rep; trivial with okToUnify : okToUnify.
  Hint Extern 0 (okToUnify _ (rep _ ?xp _ _ _)) => unfold rep; trivial with okToUnify : okToUnify.

End IAlloc.