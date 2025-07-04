Require Import Arith.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Classes.SetoidTactics.
Require Import Pred PredCrash.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Word.
Require Import Rec.
Require Import Array.
Require Import WordAuto.
Require Import Cache.
Require Import FSLayout.
Require Import Rounding.
Require Import List ListUtils.
Require Import Psatz.
Require Import AsyncDisk.
Require Import RecArrayUtils.
Require Import AsyncRecArray.

Import ListNotations.

Set Implicit Arguments.


Module PaddedLog.

  Module DescSig <: RASig.

    Definition xparams := log_xparams.
    Definition RAStart := LogDescriptor.
    Definition RALen := LogDescLen.
    Definition xparams_ok (xp : xparams) := goodSize addrlen ((RAStart xp) + (RALen xp)).

    Definition itemtype := Rec.WordF addrlen.
    Definition items_per_val := valulen / addrlen.

    Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).

  End DescSig.


  Module DataSig <: RASig.

    Definition xparams := log_xparams.
    Definition RAStart := LogData.
    Definition RALen := LogLen.
    Definition xparams_ok (xp : xparams) := goodSize addrlen ((RAStart xp) + (RALen xp)).

    Definition itemtype := Rec.WordF valulen.
    Definition items_per_val := 1.

    Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).

  End DataSig.

  Module Desc := AsyncRecArray DescSig.
  Module Data := AsyncRecArray DataSig.
  Module DescDefs := Desc.Defs.
  Module DataDefs := Data.Defs.


  (************* Log header *)
  Module Hdr.
    Definition header_type := Rec.RecF ([("ndesc", Rec.WordF addrlen);
                                         ("ndata", Rec.WordF addrlen)]).
    Definition header := Rec.data header_type.
    Definition hdr := (nat * nat)%type.
    Definition mk_header (len : hdr) : header := ($ (fst len), ($ (snd len), tt)).

    Theorem hdrsz_ok : Rec.len header_type <= valulen.
    Local Hint Resolve hdrsz_ok.

    Lemma plus_minus_header : Rec.len header_type + (valulen - Rec.len header_type) = valulen.

    Definition hdr2val (h : header) : valu.
      set (zext (Rec.to_word h) (valulen - Rec.len header_type)) as r.
      rewrite plus_minus_header in r.
      refine r.

    Definition val2hdr (v : valu) : header.
      apply Rec.of_word.
      rewrite <- plus_minus_header in v.
      refine (split1 _ _ v).

    Arguments hdr2val: simpl never.

    Lemma val2hdr2val : forall h,
      val2hdr (hdr2val h) = h.

    Arguments val2hdr: simpl never.
    Opaque val2hdr.  (* for some reason "simpl never" doesn't work *)


    Definition xparams := log_xparams.
    Definition LAHdr := LogHeader.

    Inductive state : Type :=
    | Synced : hdr -> state
    | Unsync : hdr -> hdr -> state
    .

    Definition state_goodSize st :=
      match st with
      | Synced n => goodSize addrlen (fst n) /\ goodSize addrlen (snd n)
      | Unsync n o => goodSize addrlen (fst n) /\ goodSize addrlen (snd n) /\
                      goodSize addrlen (fst o) /\ goodSize addrlen (snd o)
      end.

    Definition rep xp state : @rawpred :=
      ([[ state_goodSize state ]] *
      match state with
      | Synced n =>
         (LAHdr xp) |-> (hdr2val (mk_header n), nil)
      | Unsync n o =>
         (LAHdr xp) |-> (hdr2val (mk_header n), [hdr2val (mk_header o)]%list)
      end)%pred.

    Definition xform_rep_synced : forall xp n,
      crash_xform (rep xp (Synced n)) =p=> rep xp (Synced n).

    Definition xform_rep_unsync : forall xp n o,
      crash_xform (rep xp (Unsync n o)) =p=> rep xp (Synced n) \/ rep xp (Synced o).

    Definition read T xp cs rx : prog T := Eval compute_rec in
      let^ (cs, v) <- BUFCACHE.read (LAHdr xp) cs;
      rx ^(cs, (# ((val2hdr v) :-> "ndesc"), # ((val2hdr v) :-> "ndata"))).

    Definition write T xp n cs rx : prog T :=
      cs <- BUFCACHE.write (LAHdr xp) (hdr2val (mk_header n)) cs;
      rx cs.

    Definition sync T xp cs rx : prog T :=
      cs <- BUFCACHE.sync (LAHdr xp) cs;
      rx cs.

    Local Hint Unfold rep state_goodSize : hoare_unfold.

    Theorem write_ok : forall xp n cs,
    {< F d old,
    PRE            BUFCACHE.rep cs d *
                   [[ goodSize addrlen (fst n) /\ goodSize addrlen (snd n) ]] *
                   [[ (F * rep xp (Synced old))%pred d ]]
    POST RET: cs
                   exists d', BUFCACHE.rep cs d' *
                   [[ (F * rep xp (Unsync n old))%pred d' ]]
    XCRASH  exists cs' d', BUFCACHE.rep cs' d' * [[ (F * rep xp (Unsync n old))%pred d' ]]
    >} write xp n cs.

    Theorem read_ok : forall xp cs,
    {< F d n,
    PRE            BUFCACHE.rep cs d *
                   [[ (F * rep xp (Synced n))%pred d ]]
    POST RET: ^(cs, r)
                   BUFCACHE.rep cs d *
                   [[ (F * rep xp (Synced n))%pred d ]] *
                   [[ r = n ]]
    CRASH exists cs', BUFCACHE.rep cs' d
    >} read xp cs.

    Theorem sync_ok : forall xp cs,
    {< F d n old,
    PRE            BUFCACHE.rep cs d *
                   [[ (F * rep xp (Unsync n old))%pred d ]]
    POST RET: cs
                   exists d', BUFCACHE.rep cs d' *
                   [[ (F * rep xp (Synced n))%pred d' ]]
    XCRASH  exists cs' d', BUFCACHE.rep cs' d' *
                   [[ (F * rep xp (Unsync n old))%pred d' ]]
    >} sync xp cs.

    Hint Extern 1 ({{_}} progseq (write _ _ _) _) => apply write_ok : prog.
    Hint Extern 1 ({{_}} progseq (read _ _) _) => apply read_ok : prog.
    Hint Extern 1 ({{_}} progseq (sync _ _) _) => apply sync_ok : prog.

  End Hdr.


  (****************** Log contents and states *)

  Definition entry := (addr * valu)%type.
  Definition contents := list entry.

  Inductive state :=
  (* The log is synced on disk *)
  | Synced (l: contents)
  (* The log has been truncated; but the length (0) is unsynced *)
  | Truncated (old: contents)
  (* The log is being extended; only the content has been updated (unsynced) *)
  | ExtendedUnsync (old: contents)
  (* The log has been extended; the new contents are synced but the length is unsynced *)
  | Extended (old: contents) (new: contents).

  Definition ent_addr (e : entry) := addr2w (fst e).
  Definition ent_valu (e : entry) := snd e.

  Definition ndesc_log (log : contents) := (divup (length log) DescSig.items_per_val).

  Fixpoint log_nonzero (log : contents) : list entry :=
    match log with
    | (0, _) :: rest => log_nonzero rest
    | e :: rest => e :: log_nonzero rest
    | nil => nil
    end.

  Definition vals_nonzero (log : contents) := map ent_valu (log_nonzero log).

  Fixpoint nonzero_addrs (al : list addr) : nat :=
    match al with
    | 0 :: rest => nonzero_addrs rest
    | e :: rest => S (nonzero_addrs rest)
    | nil => 0
    end.

  Fixpoint combine_nonzero (al : list addr) (vl : list valu) : contents :=
    match al, vl with
    | 0 :: al', v :: vl' => combine_nonzero al' vl
    | a :: al', v :: vl' => (a, v) :: (combine_nonzero al' vl')
    | _, _ => nil
    end.

  Definition ndata_log (log : contents) := nonzero_addrs (map fst log) .

  Definition addr_valid (e : entry) := goodSize addrlen (fst e).

  Definition entry_valid (ent : entry) := fst ent <> 0 /\ addr_valid ent.

  Definition rep_contents xp (log : contents) : rawpred :=
    ( [[ Forall addr_valid log ]] *
     Desc.array_rep xp 0 (Desc.Synced (map ent_addr log)) *
     Data.array_rep xp 0 (Data.Synced (vals_nonzero log)) *
     Desc.avail_rep xp (ndesc_log log) (LogDescLen xp - (ndesc_log log)) *
     Data.avail_rep xp (ndata_log log) (LogLen xp - (ndata_log log))
     )%pred.

  Definition padded_addr (al : list addr) :=
    setlen al (roundup (length al) DescSig.items_per_val) 0.

  Definition padded_log (log : contents) :=
    setlen log (roundup (length log) DescSig.items_per_val) (0, $0).

  Definition rep_inner xp (st : state) : rawpred :=
  (match st with
  | Synced l =>
       Hdr.rep xp (Hdr.Synced (ndesc_log l, ndata_log l)) *
       rep_contents xp l

  | Truncated old =>
       Hdr.rep xp (Hdr.Unsync (0, 0) (ndesc_log old, ndata_log old)) *
       rep_contents xp old

  | ExtendedUnsync old =>
       Hdr.rep xp (Hdr.Synced (ndesc_log old, ndata_log old)) *
       rep_contents xp old

  | Extended old new =>
       Hdr.rep xp (Hdr.Unsync (ndesc_log old + ndesc_log new, ndata_log old + ndata_log new)
                              (ndesc_log old, ndata_log old)) *
       rep_contents xp ((padded_log old) ++ new) *
       [[ Forall entry_valid new ]]
  end)%pred.

  Definition xparams_ok xp := 
    DescSig.xparams_ok xp /\ DataSig.xparams_ok xp /\
    (LogLen xp) = DescSig.items_per_val * (LogDescLen xp).

  Definition rep xp st (hm : hashmap) :=
    ([[ xparams_ok xp ]] * rep_inner xp st)%pred.

  Local Hint Unfold rep rep_inner rep_contents xparams_ok: hoare_unfold.

  Definition avail T xp cs rx : prog T :=
    let^ (cs, nr) <- Hdr.read xp cs;
    let '(ndesc, ndata) := nr in
    rx ^(cs, ((LogLen xp) - ndesc * DescSig.items_per_val)).

  Definition read T xp cs rx : prog T :=
    let^ (cs, nr) <- Hdr.read xp cs;
    let '(ndesc, ndata) := nr in
    let^ (cs, wal) <- Desc.read_all xp ndesc cs;
    let al := map (@wordToNat addrlen) wal in
    let^ (cs, vl) <- Data.read_all xp ndata cs;
    rx ^(cs, combine_nonzero al vl).

  (* this is an evil hint *)
  Remove Hints Forall_nil.

  Lemma Forall_True : forall A (l : list A),
    Forall (fun _ : A => True) l.
  Hint Resolve Forall_True.

  Lemma combine_nonzero_ok : forall l,
    combine_nonzero (map fst l) (vals_nonzero l) = log_nonzero l.

  Lemma combine_nonzero_nil : forall a,
    combine_nonzero a nil = nil.
  Local Hint Resolve combine_nonzero_nil.

  Lemma combine_nonzero_app_zero : forall a b,
    combine_nonzero (a ++ [0]) b = combine_nonzero a b.

  Lemma combine_nonzero_app_zeros : forall n a b,
    combine_nonzero (a ++ repeat 0 n) b = combine_nonzero a b.

  Local Hint Resolve roundup_ge DescDefs.items_per_val_gt_0.

  Lemma combine_nonzero_padded_addr : forall a b,
    combine_nonzero (padded_addr a) b = combine_nonzero a b.

  Lemma map_fst_repeat : forall A B n (a : A) (b : B),
    map fst (repeat (a, b) n) = repeat a n.

  Lemma map_entaddr_repeat_0 : forall n b,
    map ent_addr (repeat (0, b) n) = repeat $0 n.

  Lemma combine_nonzero_padded_log : forall l b,
    combine_nonzero (map fst (padded_log l)) b = combine_nonzero (map fst l) b.

  Lemma addr_valid_padded : forall l,
    Forall addr_valid l -> Forall addr_valid (padded_log l).

  Lemma padded_addr_valid : forall l,
    Forall addr_valid (padded_log l) ->
    Forall addr_valid l.

  Local Hint Resolve addr_valid_padded padded_addr_valid.

  Lemma map_wordToNat_ent_addr : forall l,
    Forall addr_valid l ->
    (map (@wordToNat _) (map ent_addr l)) = map fst l.

  Lemma combine_nonzero_padded_wordToNat : forall l,
    Forall addr_valid l ->
    combine_nonzero (map (@wordToNat _) (map ent_addr (padded_log l))) (vals_nonzero l) = log_nonzero l.

  Lemma vals_nonzero_addrs : forall l,
    length (vals_nonzero l) = nonzero_addrs (map fst l).

  Lemma log_nonzero_addrs : forall l,
    length (log_nonzero l) = nonzero_addrs (map fst l).

  Lemma desc_ipack_padded : forall l,
    DescDefs.ipack (map ent_addr l) = DescDefs.ipack (map ent_addr (padded_log l)).

  Local Hint Resolve combine_nonzero_padded_wordToNat.

  Lemma desc_padding_synced_piff : forall xp a l,
    Desc.array_rep xp a (Desc.Synced (map ent_addr (padded_log l)))
    <=p=> Desc.array_rep xp a (Desc.Synced (map ent_addr l)).

  Lemma desc_padding_unsync_piff : forall xp a l,
    Desc.array_rep xp a (Desc.Unsync (map ent_addr (padded_log l)))
    <=p=> Desc.array_rep xp a (Desc.Unsync (map ent_addr l)).

  Lemma goodSize_ndesc : forall l,
    goodSize addrlen (length l) -> goodSize addrlen (ndesc_log l).
  Local Hint Resolve goodSize_ndesc.

  Lemma padded_log_length: forall l,
    length (padded_log l) = roundup (length l) DescSig.items_per_val.

  Lemma nonzero_addrs_app_zero : forall a,
    nonzero_addrs (a ++ [0]) = nonzero_addrs a.

  Lemma nonzero_addrs_app_zeros : forall n a,
    nonzero_addrs (a ++ repeat 0 n) = nonzero_addrs a.

  Lemma nonzero_addrs_padded_log : forall l,
    nonzero_addrs (map fst (padded_log l)) = nonzero_addrs (map fst l).

  Lemma vals_nonzero_length : forall l,
    length (vals_nonzero l) <= length l.

  Lemma ndata_log_goodSize : forall l,
    goodSize addrlen (length l) -> goodSize addrlen (ndata_log l).
  Local Hint Resolve ndata_log_goodSize.


  Arguments Desc.array_rep : simpl never.
  Arguments Data.array_rep : simpl never.
  Arguments Desc.avail_rep : simpl never.
  Arguments Data.avail_rep : simpl never.
  Arguments divup : simpl never.
  Hint Extern 0 (okToUnify (Hdr.rep _ _) (Hdr.rep _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (Desc.array_rep _ _ _) (Desc.array_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (Data.array_rep _ _ _) (Data.array_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (Desc.avail_rep _ _ _) (Desc.avail_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (Data.avail_rep _ _ _) (Data.avail_rep _ _ _)) => constructor : okToUnify.


  Definition avail_ok : forall xp cs,
    {< F l d,
    PRE:hm
          BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced l) hm)%pred d ]]
    POST:hm' RET: ^(cs, r)
          BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced l) hm')%pred d ]] *
          [[ r = (LogLen xp) - roundup (length l) DescSig.items_per_val ]]
    CRASH:hm' exists cs',
          BUFCACHE.rep cs' d *
          [[ (F * rep xp (Synced l) hm')%pred d ]]
    >} avail xp cs.

  Definition read_ok : forall xp cs,
    {< F l d,
    PRE:hm
          BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced l) hm)%pred d ]]
    POST:hm' RET: ^(cs, r)
          BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced l) hm')%pred d ]] *
          [[ r = log_nonzero l ]]
    CRASH:hm' exists cs',
          BUFCACHE.rep cs' d *
          [[ (F * rep xp (Synced l) hm')%pred d ]]
    >} read xp cs.


  Lemma goodSize_0 : forall sz, goodSize sz 0.

  Lemma ndesc_log_nil : ndesc_log nil = 0.

  Lemma ndata_log_nil : ndata_log nil = 0.

  Local Hint Resolve goodSize_0.


  Definition trunc T xp cs rx : prog T :=
    cs <- Hdr.write xp (0, 0) cs;
    cs <- Hdr.sync xp cs;
    rx cs.

  Local Hint Resolve Forall_nil.

  Lemma helper_sep_star_reorder : forall (a b c d : rawpred),
    a * b * c * d =p=> (a * c) * (b * d).

  Lemma helper_add_sub_0 : forall a b,
    a <= b -> a + (b - a) + 0 = b.

  Lemma helper_trunc_ok : forall xp l,
    Desc.array_rep xp 0 (Desc.Synced (map ent_addr l)) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero l)) *
    Desc.avail_rep xp (ndesc_log l) (LogDescLen xp - ndesc_log l) *
    Data.avail_rep xp (ndata_log l) (LogLen xp - ndata_log l) *
    Hdr.rep xp (Hdr.Synced (0, 0))
    =p=>
    Hdr.rep xp (Hdr.Synced (ndesc_log [], ndata_log [])) *
    Desc.array_rep xp 0 (Desc.Synced []) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero [])) *
    Desc.avail_rep xp (ndesc_log []) (LogDescLen xp - ndesc_log []) *
    Data.avail_rep xp (ndata_log []) (LogLen xp - ndata_log []).

  Definition trunc_ok : forall xp cs,
    {< F l d,
    PRE:hm
          BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced l) hm)%pred d ]]
    POST:hm' RET: cs  exists d',
          BUFCACHE.rep cs d' *
          [[ (F * rep xp (Synced nil) hm')%pred d' ]]
    XCRASH:hm' exists cs' d',
          BUFCACHE.rep cs' d' * [[ (F * (rep xp (Truncated l) hm'))%pred d' ]]
    >} trunc xp cs.

  Definition loglen_valid xp ndesc ndata :=
    ndesc <= LogDescLen xp  /\ ndata <= LogLen xp.

  Definition loglen_invalid xp ndesc ndata :=
    ndesc > LogDescLen xp \/ ndata > LogLen xp.

  Definition loglen_valid_dec xp ndesc ndata :
    {loglen_valid xp ndesc ndata} + {loglen_invalid xp ndesc ndata }.

  Remove Hints goodSize_0.

  Definition entry_valid_ndata : forall l,
    Forall entry_valid l -> ndata_log l = length l.

  Lemma loglen_valid_desc_valid : forall xp old new,
    DescSig.xparams_ok xp ->
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    Desc.items_valid xp (ndesc_log old) (map ent_addr new).
  Local Hint Resolve loglen_valid_desc_valid.


  Lemma loglen_valid_data_valid : forall xp old new,
    DataSig.xparams_ok xp ->
    Forall entry_valid new ->
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    Data.items_valid xp (ndata_log old) (map ent_valu new).
  Local Hint Resolve loglen_valid_data_valid.

  Lemma helper_loglen_desc_valid_extend : forall xp new old,
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    ndesc_log new + (LogDescLen xp - ndesc_log old - ndesc_log new) 
      = LogDescLen xp - ndesc_log old.

  Lemma helper_loglen_data_valid_extend : forall xp new old,
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    ndata_log new + (LogLen xp - ndata_log old - ndata_log new) 
      = LogLen xp - ndata_log old.

  Lemma helper_loglen_data_valid_extend_entry_valid : forall xp new old,
    Forall entry_valid new ->
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    length new + (LogLen xp - ndata_log old - ndata_log new) 
      = LogLen xp - ndata_log old.

  Lemma padded_desc_valid : forall xp st l,
    Desc.items_valid xp st (map ent_addr l)
    -> Desc.items_valid xp st (map ent_addr (padded_log l)).

  Lemma mul_le_mono_helper : forall a b,
    b > 0 -> a <= a * b.

  Lemma loglen_valid_goodSize_l : forall xp a b,
    loglen_valid xp a b -> DescSig.xparams_ok xp -> DataSig.xparams_ok xp ->
    goodSize addrlen a.

  Lemma loglen_valid_goodSize_r : forall xp a b,
    loglen_valid xp a b -> DescSig.xparams_ok xp -> DataSig.xparams_ok xp ->
    goodSize addrlen b.

  Lemma ent_valid_addr_valid : forall l,
    Forall entry_valid l -> Forall addr_valid l.
  Local Hint Resolve ent_valid_addr_valid.
  Local Hint Resolve Forall_append DescDefs.items_per_val_not_0.

  Lemma helper_add_sub : forall a b,
    a <= b -> a + (b - a) = b.


  Lemma nonzero_addrs_app : forall a b,
    nonzero_addrs (a ++ b) = nonzero_addrs a + nonzero_addrs b.

  Lemma ndata_log_app : forall a b,
    ndata_log (a ++ b) = ndata_log a + ndata_log b.

  Lemma ndesc_log_padded_log : forall l,
    ndesc_log (padded_log l) = ndesc_log l.

  Lemma ndesc_log_app : forall a b,
    length a = roundup (length a) DescSig.items_per_val ->
    ndesc_log (a ++ b) = ndesc_log a + ndesc_log b.

  Lemma ndesc_log_padded_app : forall a b,
    ndesc_log (padded_log a ++ b) = ndesc_log a + ndesc_log b.

  Lemma ndata_log_padded_log : forall a,
    ndata_log (padded_log a) = ndata_log a.


  Lemma ndata_log_padded_app : forall a b,
    ndata_log (padded_log a ++ b) = ndata_log a + ndata_log b.

  Lemma vals_nonzero_app : forall a b,
    vals_nonzero (a ++ b) = vals_nonzero a ++ vals_nonzero b.

  Lemma log_nonzero_repeat_0 : forall n,
    log_nonzero (repeat (0, $0) n) = nil.

  Lemma log_nonzero_app : forall a b,
    log_nonzero (a ++ b) = log_nonzero a ++ log_nonzero b.

  Lemma vals_nonzero_padded_log : forall l,
    vals_nonzero (padded_log l) = vals_nonzero l.

  Lemma entry_valid_vals_nonzero : forall l,
    Forall entry_valid l ->
    log_nonzero l = l.

  Lemma nonzero_addrs_entry_valid : forall l,
    Forall entry_valid l ->
    nonzero_addrs (map fst l) = length l.

  Lemma extend_ok_helper : forall F xp old new,
    Forall entry_valid new ->
    Data.array_rep xp (ndata_log old) (Data.Synced (map ent_valu new)) *
    Desc.array_rep xp 0 (Desc.Synced (map ent_addr old)) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero old)) *
    Desc.avail_rep xp (ndesc_log old + divup (length (map ent_addr new)) DescSig.items_per_val)
      (LogDescLen xp - ndesc_log old - ndesc_log new) *
    Data.avail_rep xp (ndata_log old + divup (length (map ent_valu new)) DataSig.items_per_val)
      (LogLen xp - ndata_log old - ndata_log new) *
    Desc.array_rep xp (ndesc_log old) (Desc.Synced (map ent_addr (padded_log new))) * F
    =p=>
    Desc.array_rep xp 0 (Desc.Synced (map ent_addr (padded_log old ++ new))) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero (padded_log old ++ new))) *
    Desc.avail_rep xp (ndesc_log (padded_log old ++ new)) 
                      (LogDescLen xp - ndesc_log (padded_log old ++ new)) *
    Data.avail_rep xp (ndata_log (padded_log old ++ new))
                      (LogLen xp - ndata_log (padded_log old ++ new)) * F.

  Lemma nonzero_addrs_bound : forall l,
    nonzero_addrs l <= length l.

  Lemma extend_ok_synced_hdr_helper : forall xp old new,
    Hdr.rep xp (Hdr.Synced (ndesc_log old + ndesc_log new, ndata_log old + ndata_log new))
    =p=>
    Hdr.rep xp (Hdr.Synced (ndesc_log (padded_log old ++ new),
                            ndata_log (padded_log old ++ new))).

  Local Hint Resolve extend_ok_synced_hdr_helper.

  Lemma nonzero_addrs_roundup : forall B (l : list (addr * B)) n,
    n > 0 ->
    nonzero_addrs (map fst l) <= (divup (length l) n) * n.

  Lemma loglen_invalid_overflow : forall xp old new,
    LogLen xp = DescSig.items_per_val * LogDescLen xp ->
    loglen_invalid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    length (padded_log old ++ new) > LogLen xp.

  Hint Rewrite Desc.array_rep_avail Data.array_rep_avail
     padded_log_length divup_mul divup_1 map_length
     ndesc_log_padded_log nonzero_addrs_padded_log using auto: extend_crash.
  Hint Unfold roundup ndata_log : extend_crash.

  Ltac extend_crash :=
     repeat (autorewrite with extend_crash; autounfold with extend_crash; simpl);
     setoid_rewrite <- Desc.avail_rep_merge at 3;
     [ setoid_rewrite <- Data.avail_rep_merge at 3 | ];
     [ cancel
     | apply helper_loglen_data_valid_extend_entry_valid; auto
     | apply helper_loglen_desc_valid_extend; auto ].


  Definition extend T xp log cs rx : prog T :=
    let^ (cs, nr) <- Hdr.read xp cs;
    let '(ndesc, ndata) := nr in
    let '(nndesc, nndata) := ((ndesc_log log), (ndata_log log)) in
    If (loglen_valid_dec xp (ndesc + nndesc) (ndata + nndata)) {
        (* synced *)
      cs <- Desc.write_aligned xp ndesc (map ent_addr log) cs;
       (* extended unsync *)
      cs <- Data.write_aligned xp ndata (map ent_valu log) cs;
      cs <- Desc.sync_aligned xp ndesc nndesc cs;
      cs <- Data.sync_aligned xp ndata nndata cs;
      cs <- Hdr.write xp (ndesc + nndesc, ndata + nndata) cs;
      cs <- Hdr.sync xp cs;
       (* synced*)
      rx ^(cs, true)
    } else {
      rx ^(cs, false)
    }.


  Definition extend_ok : forall xp new cs,
    {< F old d,
    PRE:hm
          BUFCACHE.rep cs d *
          [[ Forall entry_valid new ]] *
          [[ (F * rep xp (Synced old) hm)%pred d ]]
    POST:hm' RET: ^(cs, r) exists d',
          BUFCACHE.rep cs d' * (
          [[ r = true /\
             (F * rep xp (Synced ((padded_log old) ++ new)) hm')%pred d' ]] \/
          [[ r = false /\ length ((padded_log old) ++ new) > LogLen xp /\
             (F * rep xp (Synced old) hm')%pred d' ]])
    XCRASH:hm' exists cs' d',
          BUFCACHE.rep cs' d' * (
          [[ (F * rep xp (Synced old) hm')%pred d' ]] \/
          [[  (F * rep xp (Extended old new) hm')%pred d' ]])
    >} extend xp new cs.


  Hint Extern 1 ({{_}} progseq (avail _ _) _) => apply avail_ok : prog.
  Hint Extern 1 ({{_}} progseq (read _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (trunc _ _) _) => apply trunc_ok : prog.
  Hint Extern 1 ({{_}} progseq (extend _ _ _) _) => apply extend_ok : prog.

  Lemma log_nonzero_padded_log : forall l,
    log_nonzero (padded_log l) = log_nonzero l.

  Lemma log_nonzero_padded_app : forall l new,
    Forall entry_valid new ->
    log_nonzero l ++ new = log_nonzero (padded_log l ++ padded_log new).

  Lemma log_nonzero_app_padded : forall l new,
    Forall entry_valid new ->
    log_nonzero l ++ new = log_nonzero (l ++ padded_log new).

  Theorem rep_synced_length_ok : forall F xp l d hm,
    (F * rep xp (Synced l) hm)%pred d -> length l <= LogLen xp.

  Lemma xform_rep_synced : forall xp l hm,
    crash_xform (rep xp (Synced l) hm) =p=> rep xp (Synced l) hm.

  Lemma xform_rep_truncated : forall xp l hm,
    crash_xform (rep xp (Truncated l) hm) =p=>
      rep xp (Synced l) hm \/ rep xp (Synced nil) hm.

  Lemma xform_rep_extended_unsync : forall xp l hm,
    crash_xform (rep xp (ExtendedUnsync l) hm) =p=> rep xp (Synced l) hm.


  Theorem rep_extended_facts' : forall xp d old new hm,
    (rep xp (Extended old new) hm)%pred d ->
    Forall entry_valid new /\
    LogLen xp >= ndata_log old + ndata_log new /\ LogDescLen xp >= ndesc_log old + ndesc_log new.

  Theorem rep_extended_facts : forall xp old new hm,
    rep xp (Extended old new) hm =p=>
    (rep xp (Extended old new) hm *
      [[ LogLen xp >= ndata_log old + ndata_log new ]] *
      [[ LogDescLen xp >= ndesc_log old + ndesc_log new ]] *
      [[ Forall entry_valid new ]] )%pred.

  Lemma helper_sep_star_distr: forall AT AEQ V (a b c d : @pred AT AEQ V),
    a * b * c * d =p=> (c * a) * (d * b).

  Lemma helper_add_sub_add : forall a b c,
    b >= c + a -> a + (b - (c + a)) = b - c.

  Lemma xform_rep_extended_helper : forall xp old new,
    Forall entry_valid new ->
    LogLen xp >= ndata_log old + ndata_log new ->
    LogDescLen xp >= ndesc_log old + ndesc_log new ->
    Desc.array_rep xp 0 (Desc.Synced (map ent_addr (padded_log old ++ new))) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero (padded_log old ++ new))) *
    Desc.avail_rep xp (ndesc_log (padded_log old ++ new)) (LogDescLen xp - ndesc_log (padded_log old ++ new)) *
    Data.avail_rep xp (ndata_log (padded_log old ++ new)) (LogLen xp - ndata_log (padded_log old ++ new))
    =p=>
    Desc.array_rep xp 0 (Desc.Synced (map ent_addr old)) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero old)) *
    Desc.avail_rep xp (ndesc_log old) (LogDescLen xp - ndesc_log old) *
    Data.avail_rep xp (ndata_log old) (LogLen xp - ndata_log old).

  Lemma xform_rep_extended : forall xp old new hm,
    crash_xform (rep xp (Extended old new) hm) =p=>
       rep xp (Synced old) hm \/
       rep xp (Synced ((padded_log old) ++ new)) hm.

  Lemma rep_synced_app_pimpl : forall xp old new hm,
    rep xp (Synced (padded_log old ++ new)) hm =p=>
    rep xp (Synced (padded_log old ++ padded_log new)) hm.

End PaddedLog.


Module DLog.

  Definition entry := (addr * valu)%type.
  Definition contents := list entry.

  Inductive state :=
  (* The log is synced on disk *)
  | Synced (navail : nat) (l: contents)
  (* The log has been truncated; but the length (0) is unsynced *)
  | Truncated  (old: contents)
  (* The log is being extended; only the content has been updated (unsynced) *)
  | ExtendedUnsync (old: contents)
  (* The log has been extended; the new contents are synced but the length is unsynced *)
  | Extended  (old: contents) (new: contents).

  Definition rep_common l padded : rawpred :=
      ([[ l = PaddedLog.log_nonzero padded /\
         length padded = roundup (length padded) PaddedLog.DescSig.items_per_val ]])%pred.

  Definition rep xp st hm :=
    (match st with
    | Synced navail l =>
          exists padded, rep_common l padded *
          [[ navail = (LogLen xp) - (length padded) ]] *
          PaddedLog.rep xp (PaddedLog.Synced padded) hm
    | Truncated l =>
          exists padded, rep_common l padded *
          PaddedLog.rep xp (PaddedLog.Truncated padded) hm
    | ExtendedUnsync l =>
          exists padded, rep_common l padded *
          PaddedLog.rep xp (PaddedLog.ExtendedUnsync padded) hm
    | Extended l new =>
          exists padded, rep_common l padded *
          PaddedLog.rep xp (PaddedLog.Extended padded new) hm
    end)%pred.

  Local Hint Unfold rep rep_common : hoare_unfold.

  Section UnifyProof.
  Hint Extern 0 (okToUnify (PaddedLog.rep _ _ _) (PaddedLog.rep _ _ _)) => constructor : okToUnify.

  Definition read T xp cs rx : prog T :=
    r <- PaddedLog.read xp cs;
    rx r.

  Definition read_ok : forall xp cs,
    {< F l d nr,
    PRE:hm    BUFCACHE.rep cs d *
              [[ (F * rep xp (Synced nr l) hm)%pred d ]]
    POST:hm' RET: ^(cs, r)
              BUFCACHE.rep cs d *
              [[ r = l /\ (F * rep xp (Synced nr l) hm')%pred d ]]
    CRASH:hm' exists cs',
              BUFCACHE.rep cs' d *
              [[ (F * rep xp (Synced nr l) hm')%pred d ]]
    >} read xp cs.

  Definition trunc T xp cs rx : prog T :=
    cs <- PaddedLog.trunc xp cs;
    rx cs.

  Definition trunc_ok : forall xp cs,
    {< F l d nr,
    PRE:hm    BUFCACHE.rep cs d *
              [[ (F * rep xp (Synced nr l) hm)%pred d ]]
    POST:hm' RET: cs exists d',
              BUFCACHE.rep cs d' *
              [[ (F * rep xp (Synced (LogLen xp) nil) hm')%pred d' ]]
    XCRASH:hm' exists cs d',
              BUFCACHE.rep cs d' *
              [[ (F * rep xp (Truncated l) hm')%pred d' ]]
    >} trunc xp cs.


  Definition avail T xp cs rx : prog T :=
    r <- PaddedLog.avail xp cs;
    rx r.

  Definition avail_ok : forall xp cs,
    {< F l d nr,
    PRE:hm
          BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced nr l) hm)%pred d ]]
    POST:hm' RET: ^(cs, r)
          BUFCACHE.rep cs d *
          [[ (F * rep xp (Synced nr l) hm')%pred d ]] *
          [[ r = nr ]]
    CRASH:hm' exists cs',
          BUFCACHE.rep cs' d *
          [[ (F * rep xp (Synced nr l) hm')%pred d ]]
    >} avail xp cs.

  End UnifyProof.

  Local Hint Resolve PaddedLog.DescDefs.items_per_val_gt_0.

  Lemma extend_length_ok' : forall l new,
    length l = roundup (length l) PaddedLog.DescSig.items_per_val ->
    length (l ++ PaddedLog.padded_log new)
      = roundup (length (l ++ PaddedLog.padded_log new)) PaddedLog.DescSig.items_per_val.

  Lemma extend_length_ok : forall l new,
    length l = roundup (length l) PaddedLog.DescSig.items_per_val ->
    length (PaddedLog.padded_log l ++ PaddedLog.padded_log new)
      = roundup (length (PaddedLog.padded_log l ++ PaddedLog.padded_log new)) PaddedLog.DescSig.items_per_val.

  Lemma helper_extend_length_ok : forall xp padded new F d hm,
    length padded = roundup (length padded) PaddedLog.DescSig.items_per_val
    -> length (PaddedLog.padded_log padded ++ new) > LogLen xp
    -> (F * PaddedLog.rep xp (PaddedLog.Synced padded) hm)%pred d
    -> length new > LogLen xp - length padded.

  Local Hint Resolve extend_length_ok helper_extend_length_ok PaddedLog.log_nonzero_padded_app.

  Definition extend T xp new cs rx : prog T :=
    r <- PaddedLog.extend xp new cs;
    rx r.

  Definition rounded n := roundup n PaddedLog.DescSig.items_per_val.

  Definition entries_valid l := Forall PaddedLog.entry_valid l.

  Lemma extend_navail_ok : forall xp padded new, 
    length padded = roundup (length padded) PaddedLog.DescSig.items_per_val ->
    LogLen xp - length padded - rounded (length new)
    = LogLen xp - length (PaddedLog.padded_log padded ++ PaddedLog.padded_log new).

  Local Hint Resolve extend_navail_ok PaddedLog.rep_synced_app_pimpl.

  Definition extend_ok : forall xp new cs,
    {< F old d nr,
    PRE:hm
          BUFCACHE.rep cs d * [[ entries_valid new ]] *
          [[ (F * rep xp (Synced nr old) hm)%pred d ]]
    POST:hm' RET: ^(cs, r) exists d',
          BUFCACHE.rep cs d' * (
          [[ r = true /\
            (F * rep xp (Synced (nr - (rounded (length new))) (old ++ new)) hm')%pred d' ]] \/
          [[ r = false /\ length new > nr /\
            (F * rep xp (Synced nr old) hm')%pred d' ]])
    XCRASH:hm' exists cs' d',
          BUFCACHE.rep cs' d' * (
          [[ (F * rep xp (Synced nr old) hm')%pred d' ]] \/
          [[ (F * rep xp (Extended old new) hm')%pred d' ]])
    >} extend xp new cs.

  Hint Extern 1 ({{_}} progseq (avail _ _) _) => apply avail_ok : prog.
  Hint Extern 1 ({{_}} progseq (read _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (trunc _ _) _) => apply trunc_ok : prog.
  Hint Extern 1 ({{_}} progseq (extend _ _ _) _) => apply extend_ok : prog.


  (* ExtendedUnsync is actually a redundent state, it is equivalent to Synced *)
  Lemma extend_unsynced_synced : forall xp l hm,
    rep xp (ExtendedUnsync l) hm =p=> exists na, rep xp (Synced na l) hm.

  Lemma synced_extend_unsynced : forall xp l na hm,
    rep xp (Synced na l) hm =p=> rep xp (ExtendedUnsync l) hm.


  Lemma xform_rep_synced : forall xp na l hm,
    crash_xform (rep xp (Synced na l) hm) =p=> rep xp (Synced na l) hm.

  Lemma xform_rep_truncated : forall xp l hm,
    crash_xform (rep xp (Truncated l) hm) =p=> exists na,
      rep xp (Synced na l) hm \/ rep xp (Synced (LogLen xp) nil) hm.

  Lemma xform_rep_extended_unsync : forall xp l hm,
    crash_xform (rep xp (ExtendedUnsync l) hm) =p=> exists na, rep xp (Synced na l) hm.

  Lemma xform_rep_extended : forall xp old new hm,
    crash_xform (rep xp (Extended old new) hm) =p=>
       (exists na, rep xp (Synced na old) hm) \/
       (exists na, rep xp (Synced na (old ++ new)) hm).

End DLog.
