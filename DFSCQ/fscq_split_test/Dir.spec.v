Require Import Coq.Strings.String.
Require Import Mem.
Require Import Prog.
Require Import List.
Require Import Word.
Require Import Rec.
Require Import BFile.
Require Import BasicProg.
Require Import Log.
Require Import Hoare.
Require Import Pred PredCrash.
Require Import Omega.
Require Import Rec.
Require Import Array.
Require Import ListPred.
Require Import GenSepN.
Require Import BFile.
Require Import FileRecArray.
Require Import Bool.
Require Import SepAuto.
Require Import Log.
Require Import Cache.
Require Import ListUtils.
Require Import AsyncDisk.
Require Import Errno.
Require Import DestructVarname.
Import ListNotations.
Require HexString.

Set Implicit Arguments.



Module DIR.

  Definition filename_len := (HexString.to_nat "0x400" (* 1024 *) - addrlen - addrlen).
  Definition filename := word filename_len.


  Module DentSig <: FileRASig.

    Definition itemtype : Rec.type := Rec.RecF
        ([("name",  Rec.WordF filename_len);
          ("inum",  Rec.WordF addrlen);
          ("valid", Rec.WordF 1);
          ("isdir", Rec.WordF 1);
          ("unused", Rec.WordF (addrlen - 2))
         ]).

    Definition items_per_val := valulen / (Rec.len itemtype).

    Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).

  End DentSig.

  Module Dent := FileRecArray DentSig.


  (*************  dirent accessors  *)

  Definition dent := Dent.Defs.item.
  Definition dent0 := Dent.Defs.item0.

  Fact resolve_selN_dent0 : forall l i d,
    d = dent0 -> selN l i d = selN l i dent0.

  Hint Rewrite resolve_selN_dent0 using reflexivity : defaults.


  Definition bit2bool bit := if (bit_dec bit) then false else true.
  Definition bool2bit bool : word 1 := if (bool_dec bool true) then $1 else $0.

  Definition DEIsDir (de : dent) := Eval compute_rec in de :-> "isdir".
  Definition DEValid (de : dent) := Eval compute_rec in de :-> "valid".
  Definition DEName  (de : dent) := Eval compute_rec in de :-> "name".
  Definition DEInum  (de : dent) := Eval compute_rec in # (de :-> "inum").
  Definition mk_dent (name : filename) inum isdir : dent := Eval cbn in
      dent0 :=> "valid" := $1 :=>
                "name" := name :=>
                "inum" := $ inum :=>
                "isdir" := bool2bit isdir.

  Definition is_dir   (de : dent) := bit2bool (DEIsDir de).
  Definition is_valid (de : dent) := bit2bool (DEValid de).
  Definition name_is  (n : filename) (de : dent) :=
      if (weq n (DEName de)) then true else false.


  (*************  rep invariant  *)

  Definition dmatch (de: dent) : @pred filename (@weq filename_len) (addr * bool) :=
    if bool_dec (is_valid de) false then emp
    else (DEName de) |-> (DEInum de, is_dir de) * [[ DEInum de <> 0 ]].

  Definition rep f dmap :=
    exists delist,
    (Dent.rep f delist)%pred (list2nmem (BFILE.BFData f)) /\
    listpred dmatch delist dmap.

  Definition rep_macro Fm Fi m bxp ixp inum dmap ilist frees f ms sm : (@pred _ addr_eq_dec valuset) :=
    (exists flist,
    [[[ m ::: Fm * BFILE.rep bxp sm ixp flist ilist frees (BFILE.MSAllocC ms) (BFILE.MSCache ms) (BFILE.MSICache ms) (BFILE.MSDBlocks ms) ]]] *
    [[[ flist ::: Fi * inum |-> f ]]] *
    [[ rep f dmap ]])%pred.


  (*************  program  *)


  Definition lookup_f name de (_ : addr) := (is_valid de) && (name_is name de).

  Definition ifind_lookup_f lxp ixp dnum name ms :=
    Dent.ifind lxp ixp dnum (lookup_f name) ms.

  Definition ifind_invalid lxp ixp dnum ms :=
    Dent.ifind lxp ixp dnum (fun de _ => negb (is_valid de)) ms.

  Definition lookup lxp ixp dnum name ms :=
    let^ (ms, r) <- ifind_lookup_f lxp ixp dnum name ms;
    match r with
    | None => Ret ^(ms, None)
    | Some (_, de) => Ret ^(ms, Some (DEInum de, is_dir de))
    end.

  Definition readent := (filename * (addr * bool))%type.

  Definition readdir lxp ixp dnum ms :=
    let^ (ms, dents) <- Dent.readall lxp ixp dnum ms;
    let r := map (fun de => (DEName de, (DEInum de, is_dir de))) (filter is_valid dents) in
    Ret ^(ms, r).

  Definition unlink lxp ixp dnum name ms :=
    let^ (ms, r) <- ifind_lookup_f lxp ixp dnum name ms;
    match r with
    | None => Ret ^(ms, 0, Err ENOENT)
    | Some (ix, _) =>
        ms <- Dent.put lxp ixp dnum ix dent0 ms;
        Ret ^(ms, ix, OK tt)
    end.

  Definition link' lxp bxp ixp dnum name inum isdir ms :=
    let de := mk_dent name inum isdir in
    let^ (ms, r) <- ifind_invalid lxp ixp dnum ms;
    match r with
    | Some (ix, _) =>
        ms <- Dent.put lxp ixp dnum ix de ms;
        Ret ^(ms, ix+1, OK tt)
    | None =>
        let^ (ms, ok) <- Dent.extend lxp bxp ixp dnum de ms;
        Ret ^(ms, 0, ok)
    end.

  (* link without hint *)
  Definition link'' lxp bxp ixp dnum name inum isdir (ix0:addr) ms :=
    let^ (ms, ix, r0) <- link' lxp bxp ixp dnum name inum isdir ms;
    Ret ^(ms, ix, r0).

  (* link with hint *)
  Definition link lxp bxp ixp dnum name inum isdir ix0 ms :=
    let de := mk_dent name inum isdir in
    let^ (ms, len) <- BFILE.getlen lxp ixp dnum ms;
    If (lt_dec ix0 (len * Dent.RA.items_per_val)) {
      let^ (ms, res) <- Dent.get lxp ixp dnum ix0 ms;
      match (is_valid res) with
      | true =>
        let^ (ms, ix, r0) <- link' lxp bxp ixp dnum name inum isdir ms;
        Ret ^(ms, ix, r0)
      | false => 
        ms <- Dent.put lxp ixp dnum ix0 de ms;
        Ret ^(ms, ix0+1, OK tt)
      end
    } else {
(* calling extend here slows down performance drastically.
        let^ (ms, ok) <- Dent.extend lxp bxp ixp dnum de ms;
        Ret ^(ms, ix0+1, ok)  *)
      let^ (ms, ix, r0) <- link' lxp bxp ixp dnum name inum isdir ms;
      Ret ^(ms, ix, r0) 
    }.

  (*************  basic lemmas  *)


  Fact bit2bool_0 : bit2bool $0 = false.

  Fact bit2bool_1 : bit2bool $1 = true.

  Fact bit2bool_1_ne : bit2bool $1 <> false.

  Lemma bool2bit2bool : forall b,  bool2bit (bit2bool b) = b.

  Lemma lookup_f_ok: forall name de a,
    lookup_f name de a = true ->
    is_valid de = true /\ DEName de = name.

  Lemma lookup_f_nf: forall name de a,
    lookup_f name de a = false ->
    is_valid de = false \/ DEName de <> name.

  Lemma lookup_notindomain': forall l ix name,
    Forall (fun e => (lookup_f name e ix) = false) l
    -> listpred dmatch l =p=> notindomain name.

  Lemma lookup_notindomain: forall l name,
    (forall i, i < length l -> lookup_f name (selN l i dent0) i = false) ->
    listpred dmatch l =p=> notindomain name.



  Definition dmatch_ex name (de: dent) : @pred filename (@weq filename_len) (addr * bool) :=
    if (name_is name de) then emp
    else dmatch de.

  Definition dmatch_ex_same : forall de,
    dmatch_ex (DEName de) de = emp.

  Definition dmatch_ex_diff : forall name de,
    name <> (DEName de) ->
    dmatch_ex name de = dmatch de.

  Lemma dmatch_ex_ptsto : forall l name v,
    (name |-> v * listpred dmatch l) 
    =p=> (name |-> v * listpred (dmatch_ex name) l).

  Lemma lookup_ptsto: forall l name ix,
    ix < length l ->
    lookup_f name (selN l ix dent0) ix = true ->
    listpred dmatch l =p=> listpred (dmatch_ex name) l *
       (name |-> (DEInum (selN l ix dent0), is_dir (selN l ix dent0))).


  Definition readmatch (de: readent) : @pred _ (@weq filename_len) _ :=
    fst de |-> snd de.

  Lemma readmatch_ok : forall l,
    listpred dmatch l =p=> listpred readmatch
      (map (fun de => (DEName de, (DEInum de, is_dir de))) (filter is_valid l)).


  Lemma dmatch_dent0_emp :  dmatch dent0 = emp.

  Lemma listpred_dmatch_dent0_emp : forall l i dmap,
    listpred dmatch l dmap ->
    is_valid (selN l i dent0) = true ->
    i < length l ->
    listpred dmatch (updN l i dent0) (mem_except dmap (DEName (selN l i dent0))).


  Lemma dmatch_mk_dent : forall name inum isdir,
    goodSize addrlen inum ->
    dmatch (mk_dent name inum isdir) = (name |-> (inum, isdir) * [[ inum <> 0 ]])%pred.

  Lemma listpred_dmatch_mem_upd : forall l i dmap name inum isdir,
    notindomain name dmap ->
    negb (is_valid (selN l i dent0)) = true ->
    listpred dmatch l dmap ->
    i < length l -> inum <> 0 ->
    goodSize addrlen inum ->
    listpred dmatch (updN l i (mk_dent name inum isdir)) (Mem.upd dmap name (inum, isdir)).

  Lemma listpred_dmatch_repeat_dent0 : forall n,
    listpred dmatch (repeat dent0 n) <=p=> emp.

  Lemma listpred_dmatch_ext_mem_upd : forall l dmap name inum isdir,
    notindomain name dmap ->
    (forall i, i < length l -> negb (is_valid (selN l i dent0)) = false) ->
    listpred dmatch l dmap ->
    goodSize addrlen inum -> inum <> 0 ->
    listpred dmatch (l ++ @updN (Rec.data Dent.RA.itemtype) (Dent.Defs.block0) 0 (mk_dent name inum isdir))
                    (Mem.upd dmap name (inum, isdir)).

  Lemma listpred_dmatch_eq_mem : forall l m m',
    listpred dmatch l m -> listpred dmatch l m' ->
    m = m'.

  Lemma listpred_dmatch_notindomain: forall delist dmap name x,
    notindomain name dmap ->
    listpred dmatch delist (upd dmap name x) ->
    listpred dmatch delist =p=> notindomain name * name |-> x.

  Lemma dmatch_no_0_inum: forall f m, dmatch f m ->
    forall name isdir, m name = Some (0, isdir) -> False.

  Lemma listpred_dmatch_no_0_inum: forall dmap m,
    listpred dmatch dmap m ->
    forall name isdir, m name = Some (0, isdir) -> False.

  (*************  correctness theorems  *)

  Notation MSLL := BFILE.MSLL.
  Notation MSAlloc := BFILE.MSAlloc.
  Notation MSCache := BFILE.MSCache.
  Notation MSAllocC := BFILE.MSAllocC.
  Notation MSIAllocC := BFILE.MSIAllocC.
  Notation MSDBlocks := BFILE.MSDBlocks.

  Theorem lookup_ok : forall lxp bxp ixp dnum name ms,
    {< F Fm Fi m0 sm m dmap ilist frees f,
    PRE:hm LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
           rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms sm
    POST:hm' RET:^(ms',r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
           rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms' sm *
           [[ MSAlloc ms' = MSAlloc ms ]] *
           [[ MSAllocC ms' = MSAllocC ms ]] *
         ( [[ r = None /\ notindomain name dmap ]] \/
           exists inum isdir Fd,
           [[ r = Some (inum, isdir) /\ inum <> 0 /\
                   (Fd * name |-> (inum, isdir))%pred dmap ]])
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm'
    >} lookup lxp ixp dnum name ms.


  Theorem readdir_ok : forall lxp bxp ixp dnum ms,
    {< F Fm Fi m0 sm m dmap ilist frees f,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
             rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms sm
    POST:hm' RET:^(ms',r)
             LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm' *
             rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms' sm *
             [[ listpred readmatch r dmap ]] *
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSCache ms' = MSCache ms ]] *
             [[ MSAllocC ms' = MSAllocC ms ]] *
             [[ MSIAllocC ms' = MSIAllocC ms ]] *
             [[ MSDBlocks ms' = MSDBlocks ms ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm hm'
    >} readdir lxp ixp dnum ms.

  Local Hint Resolve mem_except_notindomain.

  Theorem unlink_ok : forall lxp bxp ixp dnum name ms,
    {< F Fm Fi m0 sm m dmap ilist frees,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
             exists f, rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms sm
    POST:hm' RET:^(ms', hint, r) exists m' dmap',
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
             exists f', rep_macro Fm Fi m' bxp ixp dnum dmap' ilist frees f' ms' sm *
             [[ dmap' = mem_except dmap name ]] *
             [[ notindomain name dmap' ]] *
             [[ r = OK tt -> indomain name dmap ]] *
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSAllocC ms' = MSAllocC ms ]] *
             [[ MSIAllocC ms' = MSIAllocC ms ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} unlink lxp ixp dnum name ms.

  Theorem link'_ok : forall lxp bxp ixp dnum name inum isdir ms,
    {< F Fm Fi m0 sm m dmap ilist frees,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
             exists f, rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms sm *
             [[ notindomain name dmap ]] *
             [[ goodSize addrlen inum ]] *
             [[ inum <> 0 ]]
    POST:hm' RET:^(ms', ixhint', r) exists m',
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSIAllocC ms' = MSIAllocC ms ]] *
           (([[ isError r ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm')
        \/  ([[ r = OK tt ]] *
             exists dmap' Fd ilist' frees' f',
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
             rep_macro Fm Fi m' bxp ixp dnum dmap' ilist' frees' f' ms' sm *
             [[ dmap' = Mem.upd dmap name (inum, isdir) ]] *
             [[ (Fd * name |-> (inum, isdir))%pred dmap' ]] *
             [[ (Fd dmap /\ notindomain name dmap) ]] *
             [[ BFILE.ilist_safe ilist  (BFILE.pick_balloc frees  (MSAlloc ms'))
                                 ilist' (BFILE.pick_balloc frees' (MSAlloc ms')) ]] *
             [[ BFILE.treeseq_ilist_safe dnum ilist ilist' ]] ))
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} link' lxp bxp ixp dnum name inum isdir ms.

  Hint Extern 1 ({{ _ }} Bind (link' _ _ _ _ _ _ _ _) _) => apply link'_ok : prog.

  Theorem link_ok : forall lxp bxp ixp dnum name inum isdir ixhint ms,
    {< F Fm Fi m0 sm m dmap ilist frees,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm hm *
             exists f, rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms sm *
             [[ notindomain name dmap ]] *
             [[ goodSize addrlen inum ]] *
             [[ inum <> 0 ]]
    POST:hm' RET:^(ms', ixhint', r) exists m',
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSIAllocC ms' = MSIAllocC ms ]] *
           (([[ isError r ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm')
        \/  ([[ r = OK tt ]] * 
             exists dmap' Fd ilist' frees' f',
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm hm' *
             rep_macro Fm Fi m' bxp ixp dnum dmap' ilist' frees' f' ms' sm *
             [[ dmap' = Mem.upd dmap name (inum, isdir) ]] *
             [[ (Fd * name |-> (inum, isdir))%pred dmap' ]] *
             [[ (Fd dmap /\ notindomain name dmap) ]] *
             [[ BFILE.ilist_safe ilist  (BFILE.pick_balloc frees  (MSAlloc ms'))
                                 ilist' (BFILE.pick_balloc frees' (MSAlloc ms')) ]] *
             [[ BFILE.treeseq_ilist_safe dnum ilist ilist' ]] ))
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} link lxp bxp ixp dnum name inum isdir ixhint ms.


  Hint Extern 1 ({{_}} Bind (lookup _ _ _ _ _) _) => apply lookup_ok : prog.
  Hint Extern 1 ({{_}} Bind (unlink _ _ _ _ _) _) => apply unlink_ok : prog.
  Hint Extern 1 ({{_}} Bind (link _ _ _ _ _ _ _ _ _) _) => apply link_ok : prog.
  Hint Extern 1 ({{_}} Bind (readdir _ _ _ _) _) => apply readdir_ok : prog.

  Hint Extern 0 (okToUnify (rep ?f _) (rep ?f _)) => constructor : okToUnify.


  (*************  Lemma for callers *)

  Theorem dmatch_complete : forall de m1 m2, dmatch de m1 -> dmatch de m2 -> m1 = m2.

  Lemma listpred_dmatch_eq : forall l m1 m2,
    listpred dmatch l m1
    -> listpred dmatch l m2
    -> m1 = m2.

  Lemma rep_mem_eq : forall f m1 m2,
    rep f m1 ->
    rep f m2 ->
    m1 = m2.

  Theorem bfile0_empty : rep BFILE.bfile0 empty_mem.

  Theorem rep_no_0_inum: forall f m, rep f m ->
    forall name isdir, m name = Some (0, isdir) -> False.

  Theorem crash_eq : forall f f' m1 m2,
    BFILE.file_crash f f' ->
    rep f m1 ->
    rep f' m2 ->
    m1 = m2.

  Theorem crash_rep : forall f f' m,
    BFILE.file_crash f f' ->
    rep f m ->
    rep f' m.

End DIR.