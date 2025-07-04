Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Hashmap.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Classes.SetoidTactics.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import Pred PredCrash.
Require Import Prog.
Require Import Hoare.
Require Import BasicProg.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Word.
Require Import Rec.
Require Import Array.
Require Import Eqdep_dec.
Require Import WordAuto.
Require Import Cache.
Require Import Idempotent.
Require Import ListUtils.
Require Import FSLayout.
Require Import AsyncDisk.
Require Import SepAuto.
Require Import GenSepN.
Require Import MemLog.
Require Import DiskLogHash.
Require Import MapUtils.
Require Import ListPred.
Require Import LogReplay.
Require Import DiskSet.

Import ListNotations.

Set Implicit Arguments.



Module GLog.

  Import AddrMap LogReplay ReplaySeq LogNotations.


  (************* state and rep invariant *)

  Record mstate := mk_mstate {
    MSVMap  : valumap;
    (* collapsed updates for all committed but unflushed txns,
        necessary for fast read() operation
     *)
    MSTxns  : txnlist;
    (* list of all unflushed txns, the order should match the
       second part of diskset. (first element is the latest)
    *)

    MSMLog  : MLog.mstate;
    (* lower-level states *)
  }.

  Definition memstate := (mstate * cachestate)%type.
  Definition mk_memstate vm ts ll : memstate := 
    (mk_mstate vm ts (MLog.MSInLog ll), (MLog.MSCache ll)).
  Definition mk_memstate0 := mk_mstate vmap0 nil vmap0.

  Definition MSCache (ms : memstate) := snd ms.
  Definition MSLL (ms : memstate) := MLog.mk_memstate (MSMLog (fst ms)) (snd ms).

  Definition readOnly (ms ms' : memstate) := (fst ms = fst ms').

  Lemma readOnlyLL : forall ms ms',
    MLog.readOnly (MSLL ms) (MSLL ms') ->
    MSVMap (fst ms) = MSVMap (fst ms') ->
    MSTxns (fst ms) = MSTxns (fst ms') ->
    readOnly ms ms'.

  Hint Resolve readOnlyLL.


  Inductive state :=
  | Cached   (ds : diskset)
  | Flushing (ds : diskset) (n : addr)
  | Rollback (d : diskstate)
  | Recovering (d : diskstate)
  .

  Definition vmap_match vm ts :=
    Map.Equal vm (fold_right replay_mem vmap0 ts).

  Definition ents_valid xp d ents :=
    log_valid ents d /\ length ents <= LogLen xp.

  Definition effective (ds : diskset) tslen := popn (length (snd ds) - tslen) ds.

  Definition dset_match xp ds ts :=
    Forall (ents_valid xp (fst ds)) ts /\ ReplaySeq ds ts.

  Definition rep xp st ms hm :=
  let '(vm, ts, mm) := (MSVMap ms, MSTxns ms, MSMLog ms) in
  (match st with
    | Cached ds =>
      let ds' := effective ds (length ts) in
      [[ vmap_match vm ts ]] *
      [[ dset_match xp ds' ts ]] * exists nr,
      MLog.rep xp (MLog.Synced nr (fst ds')) mm hm
    | Flushing ds n =>
      let ds' := effective ds (length ts) in
      [[ dset_match xp ds' ts /\ n <= length ts ]] *
      MLog.would_recover_either xp (nthd n ds') (selR ts n nil) hm
    | Rollback d =>
      [[ vmap_match vm ts ]] *
      [[ dset_match xp (d, nil) ts ]] *
      MLog.rep xp (MLog.Rollback d) mm hm
    | Recovering d =>
      [[ vmap_match vm ts ]] *
      [[ dset_match xp (d, nil) ts ]] *
      MLog.rep xp (MLog.Recovering d) mm hm
  end)%pred.

  Definition would_recover_any xp ds hm :=
    (exists ms n ds',
      [[ NEListSubset ds ds' ]] *
      rep xp (Flushing ds' n) ms hm)%pred.

  Local Hint Resolve nelist_subset_equal.

  Lemma sync_invariant_rep : forall xp st ms hm,
    sync_invariant (rep xp st ms hm).

  Hint Resolve sync_invariant_rep.

  Lemma sync_invariant_would_recover_any : forall xp ds hm,
    sync_invariant (would_recover_any xp ds hm).

  Hint Resolve sync_invariant_would_recover_any.

  Lemma nthd_effective : forall n ds tslen,
    nthd n (effective ds tslen) = nthd (length (snd ds) - tslen + n) ds.

  Lemma latest_effective : forall ds n,
    latest (effective ds n) = latest ds.

  Lemma effective_length : forall ds n,
    n <= (length (snd ds)) ->
    length (snd (effective ds n)) = n.

  Lemma effective_length_le : forall ds n,
    length (snd (effective ds n)) <= length (snd ds).


  Lemma cached_recover_any: forall xp ds ms hm,
    rep xp (Cached ds) ms hm =p=> would_recover_any xp ds hm.

  Lemma cached_recovering: forall xp ds ms hm,
    rep xp (Cached ds) ms hm =p=>
      exists n ms', rep xp (Recovering (nthd n ds)) ms' hm.

  Lemma flushing_recover_any: forall xp n ds ms hm,
    rep xp (Flushing ds n) ms hm =p=> would_recover_any xp ds hm.

  Lemma rollback_recover_any: forall xp d ms hm,
    rep xp (Rollback d) ms hm =p=> would_recover_any xp (d, nil) hm.

  Lemma rollback_recovering: forall xp d ms hm,
    rep xp (Rollback d) ms hm =p=> rep xp (Recovering d) ms hm.


  Lemma rep_hashmap_subset : forall xp ms hm hm',
    (exists l, hashmap_subset l hm hm')
    -> forall st, rep xp st ms hm
        =p=> rep xp st ms hm'.


  (************* program *)

  Definition read xp a (ms : memstate) :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    match Map.find a vm with
    | Some v =>  Ret ^(ms, v)
    | None =>
        let^ (mm', v) <- MLog.read xp a mm;
        Ret ^(mk_memstate vm ts mm', v)
    end.

  (* Submit a committed transaction.
     It might fail if the transaction is too big to fit into the log.
     We handle the anomaly here so that flushall() can always succeed.
     This keep the interface compatible with current Log.v, in which
     only commit() can fail, and the caller can choose to abort.
  *)
  Definition submit xp ents ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    let vm' := replay_mem ents vm in
    If (le_dec (length ents) (LogLen xp)) {
      Ret ^(mk_memstate vm' (ents :: ts) mm, true)
    } else {
      Ret ^(ms, false)
    }.

  Definition flushall_nomerge xp ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    let^ (mm) <- ForN i < length ts
    Hashmap hm
    Ghost [ F ds crash ]
    Loopvar [ mm ]
    Invariant
        exists nr,
        << F, MLog.rep: xp (MLog.Synced nr (nthd i ds)) mm hm >>
    OnCrash crash
    Begin
      (* r = false is impossible, flushall should always succeed *)
      let^ (mm, r) <- MLog.flush xp (selN ts (length ts - i - 1) nil) mm;
      Ret ^(mm)
    Rof ^(mm);
    Ret (mk_memstate vmap0 nil mm).

  Definition flushall xp ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    If (le_dec (Map.cardinal vm) (LogLen xp)) {
      let^ (mm, r) <- MLog.flush xp (Map.elements vm) mm;
      Ret (mk_memstate vmap0 nil mm)
    } else {
      ms <- flushall_nomerge xp ms;
      Ret ms
    }.

  Definition flushsync xp ms :=
    ms <- flushall xp ms;
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.apply xp mm;
    Ret (mk_memstate vm ts mm').

  Definition flushall_noop xp ms :=
    ms <- flushall xp ms;
    Ret ms.

  Definition flushsync_noop xp ms :=
    ms <- flushsync xp ms;
    Ret ms.

  Definition sync_cache xp ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.sync_cache xp mm;
    Ret (mk_memstate vm ts mm').

  Definition dwrite' (xp : log_xparams) a v ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.dwrite xp a v mm;
    Ret (mk_memstate vm ts mm').

  Definition dwrite (xp : log_xparams) a v ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    If (MapFacts.In_dec vm a) {
      ms <- flushall_noop xp ms;
      ms <- dwrite' xp a v ms;
      Ret ms
    } else {
      ms <- dwrite' xp a v ms;
      Ret ms
    }.

  Definition dwrite_vecs' (xp : log_xparams) avs ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.dwrite_vecs xp avs mm;
    Ret (mk_memstate vm ts mm').

  Definition dwrite_vecs (xp : log_xparams) avs ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    If (bool_dec (overlap (map fst avs) vm) true) {
      ms <- flushall_noop xp ms;
      ms <- dwrite_vecs' xp avs ms;
      Ret ms
    } else {
      ms <- dwrite_vecs' xp avs ms;
      Ret ms
    }.

  Definition dsync xp a ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.dsync xp a mm;
    Ret (mk_memstate vm ts mm').

  Definition dsync_vecs xp al ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.dsync_vecs xp al mm;
    Ret (mk_memstate vm ts mm').

  Definition recover xp cs :=
    mm <- MLog.recover xp cs;
    Ret (mk_memstate vmap0 nil mm).

  Definition init xp cs :=
    mm <- MLog.init xp cs;
    Ret (mk_memstate vmap0 nil mm).


  Arguments MLog.rep: simpl never.
  Hint Extern 0 (okToUnify (MLog.rep _ _ _ _) (MLog.rep _ _ _ _)) => constructor : okToUnify.



  (************* auxilary lemmas *)

  Lemma diskset_ptsto_bound_latest : forall F xp a vs ds ts,
    dset_match xp ds ts ->
    (F * a |-> vs)%pred (list2nmem ds!!) ->
    a < length (fst ds).

  Lemma diskset_vmap_find_none : forall ds ts vm a v vs xp F,
    dset_match xp ds ts ->
    vmap_match vm ts ->
    Map.find a vm = None ->
    (F * a |-> (v, vs))%pred (list2nmem ds !!) ->
    selN (fst ds) a ($0, nil) = (v, vs).

  Lemma replay_seq_replay_mem : forall ds ts xp,
    ReplaySeq ds ts ->
    Forall (ents_valid xp (fst ds)) ts ->
    replay_disk (Map.elements (fold_right replay_mem vmap0 ts)) (fst ds) = latest ds.

  Lemma diskset_vmap_find_ptsto : forall ds ts vm a w v vs F xp,
    dset_match xp ds ts ->
    vmap_match vm ts ->
    Map.find a vm = Some w ->
    (F * a |-> (v, vs))%pred (list2nmem ds !!) ->
    w = v.

  Lemma dset_match_ext : forall ents ds ts xp,
    dset_match xp ds ts ->
    log_valid ents ds!! ->
    length ents <= LogLen xp ->
    dset_match xp (pushd (replay_disk ents ds!!) ds) (ents :: ts).

  Lemma vmap_match_nil : vmap_match vmap0 nil.

  Lemma dset_match_nil : forall d xp, dset_match xp (d, nil) nil.

  Lemma dset_match_length : forall ds ts xp,
    dset_match xp ds ts -> length ts = length (snd ds).

  Lemma dset_match_log_valid_selN : forall ds ts i n xp,
    dset_match xp ds ts ->
    log_valid (selN ts i nil) (nthd n ds).

  Lemma vmap_match_find : forall ts vmap,
    vmap_match vmap ts
    -> forall a v, KIn (a, v) (Map.elements vmap)
    -> Forall (@KNoDup valu) ts
    -> exists t, In t ts /\ In a (map fst t).

  Lemma dset_match_log_valid_grouped : forall ts vmap ds xp,
    vmap_match vmap ts
    -> dset_match xp ds ts
    -> log_valid (Map.elements vmap) (fst ds).


  Lemma dset_match_ent_length_exfalso : forall xp ds ts i,
    length (selN ts i nil) > LogLen xp ->
    dset_match xp ds ts ->
    False.


  Lemma ents_valid_length_eq : forall xp d d' ts,
    Forall (ents_valid xp d ) ts ->
    length d = length d' ->
    Forall (ents_valid xp d') ts.

  Lemma dset_match_nthd_S : forall xp ds ts n,
    dset_match xp ds ts ->
    n < length ts ->
    replay_disk (selN ts (length ts - n - 1) nil) (nthd n ds) = nthd (S n) ds.

  Lemma dset_match_replay_disk_grouped : forall ts vmap ds xp,
    vmap_match vmap ts
    -> dset_match xp ds ts
    -> replay_disk (Map.elements vmap) (fst ds) = nthd (length ts) ds.

  Lemma dset_match_grouped : forall ts vmap ds xp,
    length (snd ds) > 0
    -> Map.cardinal vmap <= LogLen xp
    -> vmap_match vmap ts
    -> dset_match xp ds ts
    -> dset_match xp (fst ds, [ds !!]) [Map.elements vmap].

  Lemma recover_before_any : forall xp ds ts hm,
    dset_match xp (effective ds (length ts)) ts ->
    MLog.would_recover_before xp ds!! hm =p=>
    would_recover_any xp ds hm.

  Lemma recover_before_any_fst : forall xp ds ts hm len,
    dset_match xp (effective ds (length ts)) ts ->
    len = length ts ->
    MLog.would_recover_before xp (fst (effective ds len)) hm =p=>
    would_recover_any xp ds hm.

  Lemma synced_recover_any : forall xp ds nr ms ts hm,
    dset_match xp (effective ds (length ts)) ts ->
    MLog.rep xp (MLog.Synced nr ds!!) ms hm =p=>
    would_recover_any xp ds hm.

  Lemma recover_latest_any : forall xp ds hm ts,
    dset_match xp ds ts ->
    would_recover_any xp (ds!!, nil) hm =p=> would_recover_any xp ds hm.

  Lemma recover_latest_any_effective : forall xp ds hm ts,
    dset_match xp (effective ds (length ts)) ts ->
    would_recover_any xp (ds!!, nil) hm =p=> would_recover_any xp ds hm.

  Lemma cached_length_latest : forall F xp ds ms hm m,
    (F * rep xp (Cached ds) ms hm)%pred m ->
    length ds!! = length (fst (effective ds (length (MSTxns ms)))).

  Lemma cached_latest_cached: forall xp ds ms hm,
    rep xp (Cached (ds!!, nil)) ms hm =p=> rep xp (Cached ds) ms hm.


  (************* correctness theorems *)

  Definition init_ok : forall xp cs,
    {< F l d m,
    PRE:hm   BUFCACHE.rep cs d *
          [[ (F * arrayS (DataStart xp) m * arrayS (LogHeader xp) l)%pred d ]] *
          [[ length l = (1 + LogDescLen xp + LogLen xp) /\
             length m = (LogHeader xp) - (DataStart xp) /\
             LogDescriptor xp = LogHeader xp + 1 /\
             LogData xp = LogDescriptor xp + LogDescLen xp /\
             LogLen xp = (LogDescLen xp * PaddedLog.DescSig.items_per_val)%nat /\
             goodSize addrlen ((LogHeader xp) + length l) ]] *
          [[ sync_invariant F ]]
    POST:hm' RET: ms
          << F, rep: xp (Cached (m, nil)) ms hm' >> 
    XCRASH:hm_crash any
    >} init xp cs.


  Lemma dset_match_nthd_effective_fst : forall xp ds ts,
    dset_match xp (effective ds (length ts)) ts ->
    nthd (length (snd ds) - length ts) ds = fst (effective ds (length ts)).


  Lemma effective_pushd_comm : forall n d ds,
    effective (pushd d ds) (S n) = pushd d (effective ds n).

  Theorem read_ok: forall xp ms a,
    {< F ds vs,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[[ ds!! ::: exists F', (F' * a |-> vs) ]]]
    POST:hm' RET:^(ms', r)
      << F, rep: xp (Cached ds) ms' hm' >> * [[ r = fst vs ]] * [[ readOnly ms ms' ]]
    CRASH:hm'
      exists ms', << F, rep: xp (Cached ds) ms' hm' >>
    >} read xp a ms.


  Theorem submit_ok: forall xp ents ms,
    {< F ds,
    PRE:hm
        << F, rep: xp (Cached ds) ms hm >> *
        [[ log_valid ents ds!! ]]
    POST:hm' RET:^(ms', r)
        ([[ r = false /\ length ents > LogLen xp ]] *
         << F, rep: xp (Cached ds) ms' hm' >> *
        [[ ms' = ms ]])
     \/ ([[ r = true  ]] *
          << F, rep: xp (Cached (pushd (replay_disk ents (latest ds)) ds)) ms' hm' >>)
    CRASH:hm'
      exists ms', << F, rep: xp (Cached ds) ms' hm' >>
    >} submit xp ents ms.



  Local Hint Resolve vmap_match_nil dset_match_nil.
  Opaque MLog.flush.

  Theorem flushall_nomerge_ok: forall xp ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached (ds!!, nil)) ms' hm' >> *
      [[ MSTxns (fst ms') = nil /\ MSVMap (fst ms') = vmap0 ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} flushall_nomerge xp ms.


  Hint Extern 1 ({{_}} Bind (flushall_nomerge _ _) _) => apply flushall_nomerge_ok : prog.

  Opaque flushall_nomerge.

  Theorem flushall_ok: forall xp ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached (ds!!, nil)) ms' hm' >> *
      [[ MSTxns (fst ms') = nil /\ MSVMap (fst ms') = vmap0 ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} flushall xp ms.


  Hint Extern 1 ({{_}} Bind (init _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_}} Bind (read _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} Bind (submit _ _ _) _) => apply submit_ok : prog.
  Hint Extern 1 ({{_}} Bind (flushall _ _) _) => apply flushall_ok : prog.
  Hint Extern 0 (okToUnify (rep _ _ _ _) (rep _ _ _ _)) => constructor : okToUnify.

  Theorem flushall_noop_ok: forall xp ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached ds) ms' hm' >> *
      [[ MSTxns (fst ms') = nil /\ MSVMap (fst ms') = vmap0 ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} flushall_noop xp ms.

  Theorem flushsync_ok: forall xp ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached (ds!!, nil)) ms' hm' >> *
      [[ MSTxns (fst ms') = nil /\ MSVMap (fst ms') = vmap0 ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} flushsync xp ms.

  Hint Extern 1 ({{_}} Bind (flushsync _ _) _) => apply flushsync_ok : prog.

  Theorem flushsync_noop_ok: forall xp ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached ds) ms' hm' >> *
      [[ MSTxns (fst ms') = nil /\ MSVMap (fst ms') = vmap0 ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} flushsync_noop xp ms.

  Hint Extern 1 ({{_}} Bind (flushall_noop _ _) _) => apply flushall_noop_ok : prog.
  Hint Extern 1 ({{_}} Bind (flushsync_noop _ _) _) => apply flushsync_noop_ok : prog.

  Lemma forall_ents_valid_length_eq : forall xp d d' ts,
    Forall (ents_valid xp d) ts ->
    length d' = length d ->
    Forall (ents_valid xp d') ts.

  Lemma vmap_match_notin : forall ts vm a,
    Map.find a vm = None ->
    vmap_match vm ts ->
    Forall (fun e => ~ In a (map fst e)) ts.

  Lemma dset_match_dsupd_notin : forall xp ds a v ts vm,
    Map.find a vm = None ->
    vmap_match vm ts ->
    dset_match xp ds ts ->
    dset_match xp (dsupd ds a v) ts.

  Lemma forall_ents_valid_ents_filter : forall ts xp d f,
    Forall (ents_valid xp d) ts ->
    Forall (ents_valid xp d) (map (fun x => filter f x) ts).

  Lemma forall_ents_valid_ents_remove : forall ts xp d a,
    Forall (ents_valid xp d) ts ->
    Forall (ents_valid xp d) (map (ents_remove a) ts).

  Lemma forall_ents_valid_ents_remove_list : forall ts xp d al,
    Forall (ents_valid xp d) ts ->
    Forall (ents_valid xp d) (map (ents_remove_list al) ts).

  Lemma dset_match_dsupd : forall xp ts ds a v,
    dset_match xp ds ts ->
    dset_match xp (dsupd ds a v) (map (ents_remove a) ts).

  Lemma dset_match_dssync_vecs : forall xp ts ds al,
    dset_match xp ds ts ->
    dset_match xp (dssync_vecs ds al) ts.

  Lemma dset_match_dssync : forall xp ds a ts,
    dset_match xp ds ts ->
    dset_match xp (dssync ds a) ts.

  Lemma effective_dsupd_comm : forall ds a v n,
    effective (dsupd ds a v) n = dsupd (effective ds n) a v.

  Lemma effective_dsupd_vecs_comm : forall ds avl n,
    effective (dsupd_vecs ds avl) n = dsupd_vecs (effective ds n) avl.

  Lemma effective_dssync_vecs_comm : forall ds al n,
    effective (dssync_vecs ds al) n = dssync_vecs (effective ds n) al.

  Lemma effective_dssync_comm : forall ds a n,
    effective (dssync ds a) n = dssync (effective ds n) a.

  Lemma cached_dsupd_latest_recover_any : forall xp ds a v ms hm ms0,
    dset_match xp (effective ds (length ms0)) ms0 ->
    rep xp (Cached ((dsupd ds a v) !!, nil)) ms hm =p=>
    would_recover_any xp (dsupd ds a v) hm.

  Lemma cached_dssync_vecs_latest_recover_any : forall xp ds al ms hm ms0,
    dset_match xp (effective ds (length ms0)) ms0 ->
    rep xp (Cached ((dssync_vecs ds al) !!, nil)) ms hm =p=>
    would_recover_any xp (dssync_vecs ds al) hm.

  Lemma cached_latest_recover_any : forall xp ds ms hm ms0,
    dset_match xp (effective ds (length ms0)) ms0 ->
    rep xp (Cached (ds !!, nil)) ms hm =p=>
    would_recover_any xp ds hm.


  Theorem dwrite'_ok: forall xp a v ms,
    {< F Fd ds vs,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ Map.find a (MSVMap (fst ms)) = None ]] *
      [[[ fst (effective ds (length (MSTxns (fst ms)))) ::: (Fd * a |-> vs) ]]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists ds',
      << F, rep: xp (Cached ds') ms' hm' >> *
      [[  ds' = dsupd ds a (v, vsmerge vs) ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
      \/ exists ms' d',
      << F, rep: xp (Cached (d', nil)) ms' hm' >> *
      [[  d' = updN (fst (effective ds (length (MSTxns (fst ms))))) a (v, vsmerge vs) ]] *
      [[[ d' ::: (Fd * a |-> (v, vsmerge vs)) ]]]
    >} dwrite' xp a v ms.


  Hint Extern 1 ({{_}} Bind (dwrite' _ _ _ _) _) => apply dwrite'_ok : prog.

  Lemma diskset_ptsto_bound_effective : forall F xp a vs ds ts,
    dset_match xp (effective ds (length ts)) ts ->
    (F * a |-> vs)%pred (list2nmem ds!!) ->
    a < length (nthd (length (snd ds) - length ts) ds).

  Theorem dwrite_ok: forall xp a v ms,
    {< F Fd ds vs,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[[ ds !! ::: (Fd * a |-> vs) ]]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached (dsupd ds a (v, vsmerge vs))) ms' hm' >>
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >> \/
      << F, would_recover_any: xp (dsupd ds a (v, vsmerge vs)) hm' -- >>
    >} dwrite xp a v ms.


  Theorem dsync_ok: forall xp a ms,
    {< F Fd ds vs,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[[ ds !! ::: (Fd * a |-> vs) ]]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached (dssync ds a)) ms' hm' >>
    CRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} dsync xp a ms.


  Lemma vmap_match_nonoverlap : forall ts vm al,
    overlap al vm = false ->
    vmap_match vm ts ->
    Forall (fun e => disjoint al (map fst e)) ts.

  Lemma dset_match_dsupd_vecs_nonoverlap : forall xp avl vm ds ts,
    overlap (map fst avl) vm = false ->
    vmap_match vm ts ->
    dset_match xp ds ts ->
    dset_match xp (dsupd_vecs ds avl) ts.

  Theorem dwrite_vecs'_ok: forall xp avl ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ overlap (map fst avl) (MSVMap (fst ms)) = false ]] *
      [[ Forall (fun e => fst e < length (fst (effective ds (length (MSTxns (fst ms)))))) avl 
         /\ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached (dsupd_vecs ds avl)) ms' hm' >>
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >> \/
      exists ms',
      << F, rep: xp (Cached (vsupd_vecs (fst (effective ds (length (MSTxns (fst ms))))) avl, nil)) ms' hm' >>
    >} dwrite_vecs' xp avl ms.

  Hint Extern 1 ({{_}} Bind (dwrite_vecs' _ _ _) _) => apply dwrite_vecs'_ok : prog.

  Lemma effective_avl_addrs_ok : forall (avl : list (addr * valu)) ds ts xp,
    Forall (fun e => fst e < length (ds !!)) avl ->
    dset_match xp (effective ds (length ts)) ts ->
    Forall (fun e => fst e < length (nthd (length (snd ds) - length ts) ds)) avl.

  Theorem dwrite_vecs_ok: forall xp avl ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ Forall (fun e => fst e < length (ds!!)) avl /\ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached (dsupd_vecs ds avl)) ms' hm' >>
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >> \/
      << F, would_recover_any: xp (dsupd_vecs ds avl) hm' -- >>
    >} dwrite_vecs xp avl ms.


  Theorem dsync_vecs_ok: forall xp al ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ Forall (fun e => e < length (ds!!)) al /\ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached (dssync_vecs ds al)) ms' hm' >>
    CRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} dsync_vecs xp al ms.

  Definition recover_any_pred xp ds hm :=
    ( exists d n ms, [[ n <= length (snd ds) ]] *
      (rep xp (Cached (d, nil)) ms hm \/
        rep xp (Rollback d) ms hm) *
      [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]])%pred.

  Theorem sync_invariant_recover_any_pred : forall xp ds hm,
    sync_invariant (recover_any_pred xp ds hm).
  Hint Resolve sync_invariant_recover_any_pred.

  Lemma NEListSubset_effective : forall ds ds' n,
    NEListSubset ds ds' ->
    NEListSubset ds (effective ds' n).

  Theorem crash_xform_any : forall xp ds hm,
    crash_xform (would_recover_any xp ds hm) =p=>
                 recover_any_pred  xp ds hm.

  Lemma crash_xform_recovering : forall xp d mm hm,
    crash_xform (rep xp (Recovering d) mm hm) =p=>
                 recover_any_pred xp (d, nil) hm.

  Lemma crash_xform_cached : forall xp ds ms hm,
    crash_xform (rep xp (Cached ds) ms hm) =p=>
      exists d n ms', rep xp (Cached (d, nil)) ms' hm *
        [[[ d ::: (crash_xform (diskIs (list2nmem (nthd n ds)))) ]]] *
        [[ n <= length (snd ds) ]].

  Lemma crash_xform_rollback : forall xp d ms hm,
    crash_xform (rep xp (Rollback d) ms hm) =p=>
      exists d' ms', rep xp (Rollback d') ms' hm *
        [[[ d' ::: (crash_xform (diskIs (list2nmem d))) ]]].

  Lemma any_pred_any : forall xp ds hm,
    recover_any_pred xp ds hm =p=>
    exists d, would_recover_any xp (d, nil) hm.


  Lemma recover_idem : forall xp ds hm,
    crash_xform (recover_any_pred xp ds hm) =p=>
                 recover_any_pred xp ds hm.


  Theorem recover_ok: forall xp cs,
    {< F raw ds,
    PRE:hm
      BUFCACHE.rep cs raw *
      [[ (F * recover_any_pred xp ds hm)%pred raw ]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists raw',
      BUFCACHE.rep (MSCache ms') raw' *
      [[ (exists d n, [[ n <= length (snd  ds) ]] *
          F * rep xp (Cached (d, nil)) (fst ms') hm' *
          [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
      )%pred raw' ]]
    XCRASH:hm'
      exists raw' cs' mm', BUFCACHE.rep cs' raw' *
      [[ (exists d n, [[ n <= length (snd  ds) ]] *
          F * rep xp (Recovering d) mm' hm' *
          [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
          )%pred raw' ]]
    >} recover xp cs.


  Hint Extern 1 ({{_}} Bind (recover _ _) _) => apply recover_ok : prog.
  Hint Extern 1 ({{_}} Bind (dwrite _ _ _ _) _) => apply dwrite_ok : prog.
  Hint Extern 1 ({{_}} Bind (dwrite_vecs _ _ _) _) => apply dwrite_vecs_ok : prog.
  Hint Extern 1 ({{_}} Bind (dsync _ _ _) _) => apply dsync_ok : prog.
  Hint Extern 1 ({{_}} Bind (dsync_vecs _ _ _) _) => apply dsync_vecs_ok : prog.


End GLog.
