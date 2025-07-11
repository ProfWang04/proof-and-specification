Require Import String.
Require Import Hashmap.
Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Classes.SetoidTactics.
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
Require Import DiskLogHash.
Require Import AsyncDisk.
Require Import SepAuto.
Require Import GenSepN.
Require Import MapUtils.
Require Import FMapFacts.
Require Import Lock.
Require Import LogReplay.

Import ListNotations.

Set Implicit Arguments.


Module LogNotations.

  Notation "'<<' F ',' func ':' a1 a2 ms hm '>>'" :=
    (exists raw, BUFCACHE.rep (snd ms%pred) raw *
     lift_empty ((F * (func a1 a2 (fst ms) hm))%pred raw))%pred
    (at level 100, func, F, a1, a2, ms, hm at level 0, only parsing) : pred_scope.

  Notation "'<<' F ',' func ':' a1 a2 a3 ms hm '>>'" :=
    (exists raw, BUFCACHE.rep (snd ms%pred) raw *
     lift_empty ((F * (func a1 a2 a3 (fst ms) hm))%pred raw))%pred
    (at level 100, func, F, a1, a2, a3, ms, hm at level 0, only parsing) : pred_scope.

  Notation "'<<' F ',' func ':' a1 a2 hm '--' '>>'" :=
    (exists raw cs, BUFCACHE.rep cs raw *
     lift_empty ((F * (func a1 a2 hm))%pred raw))%pred
    (at level 100, func, F, a1, a2, hm at level 0, only parsing) : pred_scope.

  Notation "'<<' F ',' func ':' a1 a2 a3 hm '--' '>>'" :=
    (exists raw cs, BUFCACHE.rep cs raw *
     lift_empty ((F * (func a1 a2 a3 hm))%pred raw))%pred
    (at level 100, func, F, a1, a2, a3, hm at level 0, only parsing) : pred_scope.

End LogNotations.


Module MLog.

  Import AddrMap LogReplay LogNotations.

  Definition mstate := valumap.
  Definition memstate := (mstate * cachestate)%type.
  Definition mk_memstate ms cs : memstate := (ms, cs).
  Definition MSCache (ms : memstate) := snd ms.
  Definition MSInLog (ms : memstate) := fst ms.

  Definition readOnly (ms ms' : memstate) := (fst ms = fst ms').

  Inductive logstate :=
  | Synced  (na : nat) (d : diskstate)
  (* Synced state: both log and disk content are synced *)

  | Flushing (d : diskstate) (ents : DLog.contents)
  (* A transaction is being flushed to the log, but not sync'ed yet
   * e.g. DiskLog.ExtendedUnsync or DiskLog.Extended *)

  | Applying (d : diskstate)
  (* In the process of applying the log to real disk locations.
     Block content might or might not be synced.
     Log might be truncated but not yet synced.
     e.g. DiskLog.Synced or DiskLog.Truncated
   *)

  | Rollback (d : diskstate)
  (* Crashed during a flush and the data no longer matches the header.
    Will eventually recover this diskstate. *)

  | Recovering (d : diskstate)
  (* In the process of recovering from a Crashed state. *)
  .

  Definition equal_unless_in (keys: list addr) (l1 l2: list valuset) :=
    length l1 = length l2 /\
    forall a,  ~ In a keys -> selN l1 a ($0, nil) = selN l2 a ($0, nil).

  Definition synced_rep xp (d : diskstate) : rawpred :=
    arrayS (DataStart xp) d.

  Definition unsync_rep xp (ms : valumap) (old : diskstate) : rawpred :=
    (exists vs, [[ equal_unless_in (map_keys ms) old vs ]] *
     arrayS (DataStart xp) vs
    )%pred.


  Definition rep xp st mm hm :=
    ( exists log d0,
      [[ Map.Equal mm (replay_mem log vmap0) ]] *
      [[ goodSize addrlen (length d0) /\ map_valid mm d0 ]] *
    match st with
    | Synced na d =>
        [[ map_replay mm d0 d ]] *
        synced_rep xp d0 *
        DLog.rep xp (DLog.Synced na log) hm
    | Flushing d ents => exists na,
        [[ log_valid ents d /\ map_replay mm d0 d ]] *
        synced_rep xp d0 *
        (DLog.rep xp (DLog.Synced na log) hm
      \/ DLog.rep xp (DLog.Extended log ents) hm)
    | Applying d => exists na,
        [[ map_replay mm d0 d ]] *
        (((DLog.rep xp (DLog.Synced na log) hm) *
          (unsync_rep xp mm d0))
      \/ ((DLog.rep xp (DLog.Truncated log) hm) *
          (synced_rep xp d)))
    | Rollback d =>
        [[ map_replay mm d0 d ]] *
        synced_rep xp d0 *
        DLog.rep xp (DLog.Rollback log) hm
    | Recovering d =>
        [[ map_replay mm d0 d ]] *
        synced_rep xp d0 *
        DLog.rep xp (DLog.Recovering log) hm
    end)%pred.


  (* some handy state wrappers used in crash conditons *)

  Definition would_recover_before xp d hm :=
    (exists mm, rep xp (Applying d) mm hm \/
     exists mm na', rep xp (Synced na' d) mm hm)%pred.

  Definition would_recover_either xp d ents hm :=
     (exists mm,
      (exists na', rep xp (Synced na' d) mm hm) \/
      (exists na', rep xp (Synced na' (replay_disk ents d)) mm hm) \/
      rep xp (Flushing d ents) mm hm \/
      rep xp (Applying d) mm hm \/
      rep xp (Recovering d) mm hm)%pred.

  Theorem sync_invariant_rep : forall xp st mm hm,
    sync_invariant (rep xp st mm hm).

  Hint Resolve sync_invariant_rep.

  Theorem sync_invariant_would_recover_before : forall xp d hm,
    sync_invariant (would_recover_before xp d hm).

  Theorem sync_invariant_would_recover_either : forall xp d ents hm,
    sync_invariant (would_recover_either xp d ents hm).

  Hint Resolve sync_invariant_would_recover_before sync_invariant_would_recover_either.


  (******************  Program *)

  Definition read xp a ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    match Map.find a oms with
    | Some v => Ret ^(ms, v)
    | None =>
        let^ (cs, v) <- BUFCACHE.read_array (DataStart xp) a cs;
        Ret ^(mk_memstate oms cs, v)
    end.

  Definition flush_noapply xp ents ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    let^ (cs, ok) <- DLog.extend xp ents cs;
    If (bool_dec ok true) {
      Ret ^(mk_memstate (replay_mem ents oms) cs, true)
    } else {
      Ret ^(mk_memstate oms cs, false)
    }.

  Definition apply xp ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    cs <- BUFCACHE.write_vecs (DataStart xp) (Map.elements oms) cs;
    cs <- BUFCACHE.sync_vecs_now (DataStart xp) (map_keys oms) cs;
    cs <- DLog.trunc xp cs;
    Ret (mk_memstate vmap0 cs).

  Definition flush xp ents ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    If (addr_eq_dec (length ents) 0) {
      Ret ^(ms, true)
    } else {
      let^ (cs, na) <- DLog.avail xp cs;
      let ms := (mk_memstate oms cs) in
      ms' <- If (lt_dec na (length ents)) {
        ms <- apply xp ms;
        Ret ms
      } else {
        Ret ms
      };
      r <- flush_noapply xp ents ms';
      Ret r
   }.

  Definition sync_cache (xp : log_xparams) ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    cs <- BUFCACHE.sync_all cs;
    Ret (mk_memstate oms cs).

  Definition dwrite xp a v ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    ms' <- If (MapFacts.In_dec oms a) {
      ms <- apply xp ms;
      Ret ms
    } else {
      Ret ms
    };
    cs' <- BUFCACHE.write_array (DataStart xp) a v (MSCache ms');
    Ret (mk_memstate (MSInLog ms') cs').


  Definition dsync xp a ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    cs' <- BUFCACHE.begin_sync cs;
    cs' <- BUFCACHE.sync_array (DataStart xp) a cs';
    cs' <- BUFCACHE.end_sync cs';
    Ret (mk_memstate oms cs').


  Definition recover xp cs :=
    cs <- DLog.recover xp cs;
    let^ (cs, log) <- DLog.read xp cs;
    Ret (mk_memstate (replay_mem log vmap0) cs).

  Definition init (xp : log_xparams) cs :=
    cs <- DLog.init xp cs;
    Ret (mk_memstate vmap0 cs).


  Arguments DLog.rep: simpl never.
  Hint Extern 0 (okToUnify (DLog.rep _ _ _) (DLog.rep _ _ _)) => constructor : okToUnify.



  (****** auxiliary lemmas *)



  Lemma rep_hashmap_subset : forall xp mm hm hm',
    (exists l, hashmap_subset l hm hm')
    -> forall st, rep xp st mm hm
        =p=> rep xp st mm hm'.

  Lemma would_recover_either_hashmap_subset : forall xp d ents hm hm',
    (exists l, hashmap_subset l hm hm')
    -> would_recover_either xp d ents hm
        =p=> would_recover_either xp d ents hm'.

  Lemma synced_applying : forall xp na d ms hm,
    rep xp (Synced na d) ms hm =p=>
    exists ms', rep xp (Applying d) ms' hm.

  Lemma synced_flushing : forall xp na d ms hm,
    rep xp (Synced na d) ms hm =p=>
    exists ms' ents, rep xp (Flushing d ents) ms' hm.


  Lemma equal_unless_in_length_eq : forall a b l,
    equal_unless_in l a b -> length b = length a.

  Lemma apply_synced_data_ok' : forall l d,
    NoDup (map fst l) ->
    vssync_vecs (vsupd_vecs d l) (map fst l) = replay_disk l d.

  Lemma apply_synced_data_ok : forall xp m d,
    arrayS (DataStart xp) (vssync_vecs (vsupd_vecs d (Map.elements m)) (map_keys m))
    =p=> synced_rep xp (replay_disk (Map.elements m) d).


  Lemma apply_unsync_applying_ok' : forall l d n,
    NoDup (map fst l) ->
    equal_unless_in (map fst l) d (vsupd_vecs d (firstn n l)).


  Lemma apply_unsync_applying_ok : forall xp m d n,
    arrayS (DataStart xp) (vsupd_vecs d (firstn n (Map.elements m)))
       =p=> unsync_rep xp m d.

  Lemma apply_unsync_syncing_ok' : forall l a d n,
    NoDup (map fst l) ->
    ~ In a (map fst l) ->
    selN d a ($0, nil) = selN (vssync_vecs (vsupd_vecs d l) (firstn n (map fst l))) a ($0, nil).

  Lemma apply_unsync_syncing_ok : forall xp m d n,
    arrayS (DataStart xp) (vssync_vecs (vsupd_vecs d (Map.elements m)) (firstn n (map_keys m)))
       =p=> unsync_rep xp m d.


  Lemma rep_rollback_pimpl : forall xp d ms hm,
    rep xp (Rollback d) ms hm =p=>
      rep xp (Recovering d) ms hm.

  Lemma rep_synced_pimpl : forall xp nr d ms hm,
    rep xp (Synced nr d) ms hm =p=>
      rep xp (Recovering d) ms hm.


  Theorem recover_before_either : forall xp d ents hm,
    would_recover_before xp d hm =p=>
    would_recover_either xp d ents hm.

  Theorem synced_recover_before : forall xp na d ms hm,
    rep xp (Synced na d) ms hm =p=>
    would_recover_before xp d hm.

  Theorem synced_recover_either : forall xp na d ms ents hm,
    rep xp (Synced na d) ms hm =p=>
    would_recover_either xp d ents hm.

  Theorem rollback_recover_either : forall xp d ms ents hm,
    rep xp (Rollback d) ms hm =p=>
    would_recover_either xp d ents hm.

  Theorem applying_recover_before : forall xp d ms hm,
    rep xp (Applying d) ms hm =p=>
    would_recover_before xp d hm.

  Theorem synced_recover_after : forall xp na d ms ents hm,
    rep xp (Synced na (replay_disk ents d)) ms hm =p=>
    would_recover_either xp d ents hm.

  Theorem applying_recover_after : forall xp d ms ents hm,
    rep xp (Applying d) ms hm =p=>
    would_recover_either xp d ents hm.

  Theorem flushing_recover_after : forall xp d ms ents hm,
    rep xp (Flushing d ents) ms hm =p=>
    would_recover_either xp d ents hm.



  (** specs *)


  Hint Extern 0 (okToUnify (synced_rep ?a _) (synced_rep ?a _)) => constructor : okToUnify.

  Section UnfoldProof1.
  Local Hint Unfold rep map_replay: hoare_unfold.

  Definition init_ok : forall xp cs,
    {< F l m d,
    PRE:hm   BUFCACHE.rep cs d *
          [[ (F * arrayS (DataStart xp) m * arrayS (LogHeader xp) l)%pred d ]] *
          [[ length l = (1 + LogDescLen xp + LogLen xp) /\
             length m = (LogHeader xp) - (DataStart xp) /\
             LogDescriptor xp = LogHeader xp + 1 /\
             LogData xp = LogDescriptor xp + LogDescLen xp /\
             LogLen xp = (LogDescLen xp * PaddedLog.DescSig.items_per_val)%nat /\
             goodSize addrlen ((LogHeader xp) + length l) ]] *
          [[ sync_invariant F ]]
    POST:hm' RET: ms  exists d' nr,
          BUFCACHE.rep (MSCache ms) d' *
          [[ (F * rep xp (Synced nr m) (MSInLog ms) hm')%pred d' ]]
    XCRASH:hm_crash any
    >} init xp cs.

  Theorem read_ok: forall xp ms a,
    {< F d na vs,
    PRE:hm
      << F, rep: xp (Synced na d) ms hm >> *
      [[[ d ::: exists F', (F' * a |-> vs) ]]]
    POST:hm' RET:^(ms', r)
      << F, rep: xp (Synced na d) ms' hm' >> * [[ r = fst vs ]] * [[ readOnly ms ms' ]]
    CRASH:hm'
      exists ms', << F, rep: xp (Synced na d) ms' hm' >>
    >} read xp a ms.

  End UnfoldProof1.



  Local Hint Resolve log_valid_nodup.


  Section UnfoldProof2.
  Local Hint Unfold rep map_replay synced_rep: hoare_unfold.

  Theorem flush_noapply_ok: forall xp ents ms,
    {< F d na,
     PRE:hm  << F, rep: xp (Synced na d) ms hm >> *
          [[ log_valid ents d /\ sync_invariant F ]]
     POST:hm' RET:^(ms',r)
          ([[ r = true ]]  * exists na',
            << F, rep: xp (Synced na' (replay_disk ents d)) ms' hm' >>) \/
          ([[ r = false /\ length ents > na ]] *
            << F, rep: xp (Synced na d) ms' hm' >>)
     XCRASH:hm'  exists ms',
            << F, rep: xp (Flushing d ents) ms' hm' >>
    >} flush_noapply xp ents ms.

  End UnfoldProof2.



  Section UnfoldProof3.
  Local Hint Unfold rep map_replay would_recover_before: hoare_unfold.
  Hint Extern 0 (okToUnify (synced_rep ?a _) (synced_rep ?a _)) => constructor : okToUnify.

  Lemma goodSize_vssync_vsupd_vecs : forall l ents ks,
    goodSize addrlen (length l) ->
    goodSize addrlen (length (vssync_vecs (vsupd_vecs l ents) ks)).

  Lemma map_valid_vssync_vsupd_vecs : forall l mm ents ks,
    map_valid mm l ->
    map_valid mm (vssync_vecs (vsupd_vecs l ents) ks).

  Lemma replay_disk_vssync_vsupd_vecs : forall d mm,
    replay_disk (Map.elements mm) d =
    vssync_vecs (vsupd_vecs d (Map.elements mm)) (map_keys mm).

  Lemma replay_disk_vssync_vsupd_vecs_twice : forall d mm,
    replay_disk (Map.elements mm) d =
    replay_disk (Map.elements mm) (vssync_vecs (vsupd_vecs d (Map.elements mm)) (map_keys mm)).

  Lemma replay_disk_vsupd_vecs' : forall l d,
    KNoDup l ->
    replay_disk l (vsupd_vecs d l) =
    replay_disk l d.

  Lemma replay_disk_vsupd_vecs : forall mm d,
    replay_disk (Map.elements mm) (vsupd_vecs d (Map.elements mm)) =
    replay_disk (Map.elements mm) d.


  Local Hint Resolve goodSize_vssync_vsupd_vecs map_valid_map0
                     map_valid_vssync_vsupd_vecs KNoDup_NoDup
                     replay_disk_vssync_vsupd_vecs replay_disk_vssync_vsupd_vecs_twice
                     replay_disk_vsupd_vecs.

  Theorem apply_ok: forall xp ms,
    {< F d na,
    PRE:hm
      << F, rep: xp (Synced na d) ms hm >> *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Synced (LogLen xp) d) ms' hm' >> *
      [[ Map.Empty (MSInLog ms') ]]
    XCRASH:hm'
      << F, would_recover_before: xp d hm' -- >>
    >} apply xp ms.

  End UnfoldProof3.


  Local Hint Unfold map_replay : hoare_unfold.
  Hint Extern 1 ({{_}} Bind (apply _ _) _) => apply apply_ok : prog.
  Hint Extern 1 ({{_}} Bind (flush_noapply _ _ _) _) => apply flush_noapply_ok : prog.
  Hint Extern 0 (okToUnify (synced_rep ?a _) (synced_rep ?a _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (rep _ _ _ _) (rep _ _ _ _)) => constructor : okToUnify.

  Theorem flush_ok: forall xp ents ms,
    {< F d na,
     PRE:hm  << F, rep: xp (Synced na d) ms hm >> *
          [[ log_valid ents d /\ sync_invariant F ]]
     POST:hm' RET:^(ms',r) exists na',
          ([[ r = true ]] *
           << F, rep: xp (Synced na' (replay_disk ents d)) ms' hm' >>)
      \/  ([[ r = false /\ length ents > (LogLen xp) ]] *
           << F, rep: xp (Synced na' d) ms' hm' >>)
     XCRASH:hm'
          << F, would_recover_either: xp d ents hm' -- >>
    >} flush xp ents ms.



  Theorem dwrite_ok: forall xp a v ms,
    {< F Fd d na vs,
    PRE:hm
      << F, rep: xp (Synced na d) ms hm >> *
      [[[ d ::: (Fd * a |-> vs) ]]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists d' na',
      << F, rep: xp (Synced na' d') ms' hm' >> *
      [[ d' = updN d a (v, vsmerge vs) ]] *
      [[[ d' ::: (Fd * a |-> (v, vsmerge(vs))) ]]]
    XCRASH:hm'
      << F, would_recover_before: xp d hm' -- >> \/
      exists ms' na' d',
      << F, rep: xp (Synced na' d') ms' hm' >> *
      [[[ d' ::: (Fd * a |-> (v, vsmerge(vs))) ]]] *
      [[ d' = updN d a (v, vsmerge vs) ]]
    >} dwrite xp a v ms.



  Section UnfoldProof4.
  Local Hint Unfold rep map_replay synced_rep: hoare_unfold.

  Theorem dsync_ok: forall xp a ms,
    {< F Fd d na vs,
    PRE:hm
      << F, rep: xp (Synced na d) ms hm >> *
      [[[ d ::: (Fd * a |-> vs) ]]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists d' na',
      << F, rep: xp (Synced na' d') ms' hm' >> *
      [[[ d' ::: (Fd * a |-> (fst vs, nil)) ]]] *
      [[  d' = vssync d a ]]
    CRASH:hm'
      exists ms' na',
      << F, rep: xp (Synced na' d) ms' hm' >>
    >} dsync xp a ms.

  End UnfoldProof4.




  (********* dwrite/dsync for a list of address/value pairs *)

  Definition dwrite_vecs xp avl ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    ms' <- If (bool_dec (overlap (map fst avl) oms) true) {
      ms <- apply xp ms;
      Ret ms
    } else {
      Ret ms
    };
    cs' <- BUFCACHE.write_vecs (DataStart xp) avl (MSCache ms');
    Ret (mk_memstate (MSInLog ms') cs').


  Definition dsync_vecs xp al ms :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    cs' <- BUFCACHE.sync_vecs_now (DataStart xp) al cs;
    Ret (mk_memstate oms cs').


  (****************** crash and recovery *)

  Lemma map_valid_replay_mem_synced_list : forall x0 x3 x4 l',
    map_valid x0 x4 ->
    possible_crash_list x4 l' ->
    Map.Equal x0 (replay_mem x3 vmap0) ->
    map_valid (replay_mem x3 vmap0) (synced_list l').

  Hint Rewrite selN_combine repeat_selN' Nat.min_id synced_list_length : lists.

  Ltac simplen_rewrite H := try progress (
    set_evars_in H; (rewrite_strat (topdown (hints lists)) in H); subst_evars;
      [ try simplen_rewrite H | try autorewrite with lists .. ]).

  Ltac simplen' := repeat match goal with
    | [H : context[length ?x] |- _] => progress ( first [ is_var x | simplen_rewrite H ] )
    | [H : length ?l = _  |- context [ length ?l ] ] => setoid_rewrite H
    | [H : context[Nat.min ?a ?a] |- _ ] => rewrite Nat.min_id in H
    | [H : ?l = _  |- context [ ?l ] ] => setoid_rewrite H
    | [H : ?l = _ , H2 : context [ ?l ] |- _ ] => rewrite H in H2
    | [H : @length ?T ?l = 0 |- context [?l] ] => replace l with (@nil T) by eauto
    | [H : equal_unless_in _ _ _ |- _ ] => apply equal_unless_in_length_eq in H
    | [H : possible_crash_list _ _ |- _ ] => apply possible_crash_list_length in H
    | [ |- _ < _ ] => try solve [eapply lt_le_trans; eauto; try omega ]
    end.

  Ltac simplen :=  auto; repeat (try subst; simpl;
    auto; simplen'; autorewrite with lists); simpl; eauto; try omega.

  Ltac map_rewrites :=
    match goal with
    | [ H : Map.Equal (replay_mem ?x ?y) _ |- map_valid (replay_mem ?x ?y) ?l ] =>
        eapply (map_valid_equal (MapFacts.Equal_sym H))
    | [ H : Map.Equal _ (replay_mem ?x ?y) |- map_valid (replay_mem ?x ?y) ?l ] =>
        eapply (map_valid_equal H)
    | [ H : Map.Equal _  (replay_mem ?x ?y)
        |-  context [ replay_disk (Map.elements (replay_mem ?x ?y)) _ ] ] =>
        rewrite (mapeq_elements (MapFacts.Equal_sym H))
    | [ H : Map.Equal (replay_mem ?x ?y) _
        |-  context [ replay_disk (Map.elements (replay_mem ?x ?y)) _ ] ] =>
        rewrite (mapeq_elements H)
    end.

  Ltac t :=
    repeat map_rewrites;
    try match goal with
      | [ H : goodSize _ ?a |- goodSize _ ?b ] => simplen
      | [ H : map_valid ?a _ |- map_valid ?a _ ] =>
          solve [ eapply (length_eq_map_valid _ H); simplen ]
      | [ |- map_valid (replay_mem _ _) (synced_list _) ] =>
          try solve [ eapply map_valid_replay_mem_synced_list; eauto ]
    end.

  Lemma equal_unless_in_possible_crash : forall l a b c,
    equal_unless_in l (synced_list a) b ->
    possible_crash_list b c ->
    forall i, ~ In i l -> selN a i $0 = selN c i $0.

  Lemma equal_unless_in_updN : forall B l a (b : B) v d d',
    ~ KIn (a, b) l ->
    equal_unless_in (a :: map fst l) d d' ->
    equal_unless_in (map fst l) (updN d a (v, nil)) (updN d' a (v, nil)).

  Lemma equal_unless_in_sym : forall l a b,
    equal_unless_in l a b <-> equal_unless_in l b a.

  Lemma equal_unless_in_refl : forall l a,
    equal_unless_in l a a.

  Lemma equal_unless_in_replay_disk' : forall l a b,
    KNoDup l ->
    equal_unless_in (map fst l) a b ->
    replay_disk l a = replay_disk l b.

  Lemma equal_unless_in_replay_disk : forall a b m,
    equal_unless_in (map_keys m) b a ->
    replay_disk (Map.elements m) a = replay_disk (Map.elements m) b.

  Lemma list2nmem_replay_disk_crash_xform : forall ents vsl vl (F : rawpred),
    KNoDup ents ->
    possible_crash_list vsl vl ->
    F (list2nmem (replay_disk ents vsl)) ->
    crash_xform F (list2nmem (replay_disk ents (synced_list vl))).


  Lemma crash_xform_list2nmem_replay_disk : forall F ents vsl vl,
    crash_xform F (list2nmem (replay_disk ents vsl)) ->
    possible_crash_list vsl vl ->
    crash_xform F (list2nmem (replay_disk ents (synced_list vl))).


  Lemma map_valid_replay_mem_app : forall a ents l' x0 x1,
     Map.Equal x0 (replay_mem a vmap0) ->
     map_valid x0 x1 ->
     possible_crash_list x1 l' ->
     log_valid ents (replay_disk (Map.elements (elt:=valu) x0) x1) ->
     map_valid (replay_mem (a ++ ents) vmap0) (synced_list l').

  Lemma in_vsmerge_incl_trans : forall v vs vs',
    In v (vsmerge vs) ->
    fst vs = fst vs' ->
    incl (snd vs) (snd vs') ->
    In v (vsmerge vs').

  Lemma possible_crash_vsupd_vecs_listupd : forall F m x st l avl,
    (F * arrayS st l)%pred m ->
    possible_crash m x ->
    possible_crash (listupd m st (vsupd_vecs l avl)) x.

  Lemma dwrite_vecs_xcrash_ok : forall cs d raw xp F avl m n n' log hm,
    overlap (map fst avl) m <> true ->
    map_valid m d ->
    Map.Equal m (replay_mem log vmap0) ->
    goodSize addrlen (length d) ->
    ((DLog.rep xp (DLog.Synced n' log) hm * F) * 
      arrayS (DataStart xp) (vsupd_vecs d (firstn n avl)))%pred raw ->
    crash_xform (BUFCACHE.rep cs raw) =p=> 
      crash_xform (exists ms na, 
      << F, rep: xp (Synced na (vsupd_vecs (replay_disk (Map.elements m) d) avl)) ms hm >>).


  Lemma dwrite_vecs_xcrash_ok_empty : forall cs d raw xp F avl m n n' log hm,
    Map.Empty m ->
    Map.Equal m (replay_mem log vmap0) ->
    goodSize addrlen (length d) ->
    ((DLog.rep xp (DLog.Synced n' log) hm * F) * 
      arrayS (DataStart xp) (vsupd_vecs d (firstn n avl)))%pred raw ->
    crash_xform (BUFCACHE.rep cs raw) =p=> 
        crash_xform (exists ms na, 
        << F, rep: xp (Synced na (vsupd_vecs (replay_disk (Map.elements m) d) avl)) ms hm >>).


  Lemma crash_xform_applying : forall xp d mm hm,
    crash_xform (rep xp (Applying d) mm hm) =p=>
      exists na d' mm', (rep xp (Synced na d') mm' hm) *
      [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].


  Lemma crash_xform_synced : forall xp nr d ms hm,
    crash_xform (rep xp (Synced nr d) ms hm) =p=>
      exists d' ms' nr', rep xp (Synced nr' d') ms' hm *
      [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].


  Lemma crash_xform_applying_applying : forall xp d ms hm,
    crash_xform (rep xp (Applying d) ms hm) =p=>
      exists d' ms', rep xp (Applying d') ms' hm *
      [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].

  Lemma crash_xform_flushing : forall xp d ents ms hm,
    crash_xform (rep xp (Flushing d ents) ms hm) =p=>
      exists d' ms',
        (exists nr, rep xp (Synced nr d') ms' hm *
          ([[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]] \/
           [[[ d' ::: crash_xform (diskIs (list2nmem (replay_disk ents d))) ]]])) \/
        (rep xp (Rollback d') ms' hm *
          [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]]).

  Lemma crash_xform_recovering' : forall xp d ms hm,
    crash_xform (rep xp (Recovering d) ms hm) =p=>
      exists d' ms',
        ((exists nr, rep xp (Synced nr d') ms' hm) \/
          rep xp (Rollback d') ms' hm) *
        [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].

  Lemma crash_xform_rollback : forall xp d ms hm,
    crash_xform (rep xp (Rollback d) ms hm) =p=>
      exists d' ms', rep xp (Rollback d') ms' hm *
      [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].

  Lemma crash_xform_before : forall xp d hm,
    crash_xform (would_recover_before xp d hm) =p=>
      exists d' ms' na, rep xp (Synced na d') ms' hm *
      [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].


  Definition recover_either_pred xp d ents hm :=
    (exists d' ms',
      (exists nr, rep xp (Synced nr d') ms' hm *
        ([[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]] \/
         [[[ d' ::: crash_xform (diskIs (list2nmem (replay_disk ents d))) ]]])) \/
      (rep xp (Rollback d') ms' hm *
        [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]]))%pred.

  Lemma crash_xform_either : forall xp d ents hm,
    crash_xform (would_recover_either xp d ents hm) =p=>
                  recover_either_pred xp d ents hm.

  Lemma crash_xform_recovering : forall xp d ms ents hm,
    crash_xform (rep xp (Recovering d) ms hm) =p=>
      recover_either_pred xp d ents hm.

  Lemma either_pred_either : forall xp d hm ents,
    recover_either_pred xp d ents hm =p=>
    exists d', would_recover_either xp d' ents hm.

  Lemma recover_idem : forall xp d ents hm,
    crash_xform (recover_either_pred xp d ents hm) =p=>
                 recover_either_pred xp d ents hm.


  Theorem recover_ok: forall xp cs,
    {< F raw d ents,
    PRE:hm
      BUFCACHE.rep cs raw *
      [[ (F * recover_either_pred xp d ents hm)%pred raw ]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists raw',
      BUFCACHE.rep (MSCache ms') raw' *
      [[(exists d' na, F * rep xp (Synced na d') (MSInLog ms') hm' *
        ([[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]] \/
         [[[ d' ::: crash_xform (diskIs (list2nmem (replay_disk ents d))) ]]]
      ))%pred raw' ]]
    XCRASH:hm'
      exists cs' raw' ms', BUFCACHE.rep cs' raw' *
      [[ (exists d', F * rep xp (Recovering d') ms' hm' *
         ([[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]] \/
         [[[ d' ::: crash_xform (diskIs (list2nmem (replay_disk ents d))) ]]]
        ))%pred raw' ]]
    >} recover xp cs.


  Theorem dwrite_vecs_ok : forall xp avl ms,
    {< F d na,
    PRE:hm
      << F, rep: xp (Synced na d) ms hm >> *
      [[ Forall (fun e => fst e < length d) avl /\ sync_invariant F ]]
    POST:hm' RET:ms' exists na',
      << F, rep: xp (Synced na' (vsupd_vecs d avl)) ms' hm' >>
    XCRASH:hm'
      << F, would_recover_before: xp d hm' -- >> \/
      exists na' ms',
      << F, rep: xp (Synced na' (vsupd_vecs d avl)) ms' hm' >>
    >} dwrite_vecs xp avl ms.



  Theorem dsync_vecs_ok: forall xp al ms,
    {< F d na,
    PRE:hm
      << F, rep: xp (Synced na d) ms hm >> *
      [[ Forall (fun e => e < length d) al /\ sync_invariant F ]]
    POST:hm' RET:ms' exists na',
      << F, rep: xp (Synced na' (vssync_vecs d al)) ms' hm' >>
    CRASH:hm' exists na' ms',
      << F, rep: xp (Synced na' d) ms' hm' >>
    >} dsync_vecs xp al ms.

  Hint Extern 1 ({{_}} Bind (init _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_}} Bind (read _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} Bind (flush _ _ _) _) => apply flush_ok : prog.
  Hint Extern 1 ({{_}} Bind (dwrite _ _ _ _) _) => apply dwrite_ok : prog.
  Hint Extern 1 ({{_}} Bind (dsync _ _ _) _) => apply dsync_ok : prog.
  Hint Extern 1 ({{_}} Bind (dwrite_vecs _ _ _) _) => apply dwrite_vecs_ok : prog.
  Hint Extern 1 ({{_}} Bind (dsync_vecs _ _ _) _) => apply dsync_vecs_ok : prog.
  Hint Extern 1 ({{_}} Bind (recover _ _) _) => apply recover_ok : prog.

End MLog.