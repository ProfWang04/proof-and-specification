Require Import Mem.
Require Import Pred.
Require Import Prog.
Require Import ListPred.
Require Import List.
Require Import SepAuto.
Require Import Array.
Require Import Omega.
Require Import AsyncDisk PredCrash.
Require Import FunctionalExtensionality.


Set Implicit Arguments.
Set Default Proof Using "Type".

Section MemPred.

  Variable LowAT : Type.
  Variable LowAEQ : EqDec LowAT.
  Variable LowV : Type.

  Variable HighAT : Type.
  Variable HighAEQ : EqDec HighAT.
  Variable HighV : Type.

  Definition low_mem := @mem LowAT LowAEQ LowV.
  Definition high_mem := @mem HighAT HighAEQ HighV.

  Definition low_pred := @pred LowAT LowAEQ LowV.
  Definition high_pred := @pred HighAT HighAEQ HighV.


  Fixpoint avs2mem_iter (avs : list (HighAT * HighV)) (m : @mem HighAT HighAEQ HighV) :=
    match avs with
    | nil => m
    | (a, v) :: rest =>
      upd (avs2mem_iter rest m) a v
    end.

  Definition avs2mem avs :=
    avs2mem_iter avs empty_mem.

  Fixpoint avs_except avs victim : @list (HighAT * HighV) :=
    match avs with
    | nil => nil
    | (a, v) :: rest =>
      if HighAEQ a victim then avs_except rest victim else (a, v) :: avs_except rest victim
    end.

  Theorem avs_except_notin_eq : forall avs a,
    ~ In a (map fst avs) -> avs_except avs a = avs.

  Theorem avs_except_cons : forall avs a v,
    NoDup (map fst ((a, v) :: avs)) ->
    avs_except ((a, v) :: avs) a = avs.

  Theorem avs2mem_ne : forall avs a v a',
    a <> a' ->
    avs2mem ((a, v) :: avs) a' = avs2mem avs a'.

  Theorem listpred_avs_except : forall avs (lp : _ -> low_pred) a v,
    NoDup (map fst avs) ->
    avs2mem avs a = Some v ->
    listpred lp avs =p=> listpred lp (avs_except avs a) * lp (a, v).

  Theorem avs_except_notin : forall avs a a',
    ~ In a' (map fst avs) -> ~ In a' (map fst (avs_except avs a)).

  Hint Resolve avs_except_notin.

  Lemma avs2mem_notindomain : forall l a,
    ~ In a (map fst l) ->
    notindomain a (avs2mem l).

  Theorem avs_except_nodup : forall avs a,
    NoDup (map fst avs) -> NoDup (map fst (avs_except avs a)).

  Hint Resolve avs_except_nodup.

  Lemma avs2mem_except_eq : forall avs a,
    avs2mem (avs_except avs a) a = None.

  Lemma avs2mem_except_ne : forall avs a a',
    a <> a' ->
    avs2mem (avs_except avs a) a' = avs2mem avs a'.

  Theorem mem_except_avs_except : forall avs a,
    mem_except (avs2mem avs) a = avs2mem (avs_except avs a).

  Hint Resolve mem_except_avs_except.

  Lemma avs2mem_none_notin : forall avs a,
    avs2mem avs a = None -> ~ In a (map fst avs).

  Variable Pred : HighAT -> HighV -> low_pred.

  Definition mem_pred_one (av : HighAT * HighV) : low_pred :=
    Pred (fst av) (snd av).

  Definition mem_pred (hm : high_mem) : low_pred :=
    (exists hm_avs,
     [[ NoDup (map fst hm_avs) ]] *
     [[ hm = avs2mem hm_avs ]] *
     listpred mem_pred_one hm_avs)%pred.

  Theorem mem_pred_extract' : forall hm a v,
    hm a = Some v ->
    mem_pred hm =p=> mem_pred (mem_except hm a) * mem_pred_one (a, v).

  Theorem mem_pred_extract : forall hm a v,
    hm a = Some v ->
    mem_pred hm =p=> mem_pred (mem_except hm a) * Pred a v.

  Theorem mem_pred_absorb' : forall hm a v,
    mem_pred (mem_except hm a) * mem_pred_one (a, v) =p=> mem_pred (upd hm a v).

  Theorem mem_pred_absorb : forall hm a v,
    mem_pred (mem_except hm a) * Pred a v =p=> mem_pred (upd hm a v).

  Theorem mem_pred_absorb_nop' : forall hm a v,
    hm a = Some v ->
    mem_pred (mem_except hm a) * mem_pred_one (a, v) =p=> mem_pred hm.

  Theorem mem_pred_absorb_nop : forall hm a v,
    hm a = Some v ->
    mem_pred (mem_except hm a) * Pred a v =p=> mem_pred hm.

  Theorem mem_pred_empty_mem :
    mem_pred empty_mem <=p=> emp.

End MemPred.

Theorem mem_pred_pimpl : forall LA LEQ LV HA HEQ HV hm p1 p2,
  (forall a v, p1 a v =p=> p2 a v) ->
  @mem_pred LA LEQ LV HA HEQ HV p1 hm =p=> mem_pred p2 hm.

Theorem mem_pred_pimpl_except : forall LA LEQ LV HA HEQ HV hm p1 p2 a',
  (forall a v, a <> a' -> p1 a v =p=> p2 a v) ->
  @mem_pred LA LEQ LV HA HEQ HV p1 (mem_except hm a') =p=> mem_pred p2 (mem_except hm a').


Theorem mem_pred_absent_hm :
  forall A AEQ LV HV p hm m a,
  m a = None ->
  (forall a v, p a v =p=> exists v', a |-> v') ->
  @mem_pred A AEQ LV A AEQ HV p hm m ->
  hm a = None.

Theorem mem_pred_absent_lm :
  forall A AEQ LV HV p hm m a,
  hm a = None ->
  (forall a v, p a v =p=> exists v', a |-> v') ->
  @mem_pred A AEQ LV A AEQ HV p hm m ->
  m a = None.


Theorem xform_mem_pred : forall prd (hm : rawdisk),
  crash_xform (@mem_pred _ addr_eq_dec _ _ addr_eq_dec _ prd hm) <=p=>
  @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (fun a v => crash_xform (prd a v)) hm.


Theorem sync_xform_mem_pred : forall prd (hm : rawdisk),
  sync_xform (@mem_pred _ addr_eq_dec _ _ addr_eq_dec _ prd hm) <=p=>
  @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (fun a v => sync_xform (prd a v)) hm.


Theorem sync_invariant_mem_pred : forall HighAT HighAEQ HighV (prd : HighAT -> HighV -> _) hm,
  (forall a v, sync_invariant (prd a v)) ->
  sync_invariant (@mem_pred _ _ _ _ HighAEQ _ prd hm).

Hint Resolve sync_invariant_mem_pred.


Section MEM_MATCH.

  Variable AT V : Type.
  Variable AEQ : EqDec AT.

  Implicit Types m ma mb : @Mem.mem AT AEQ V.

  Definition mem_match ma mb :=
    forall a, ma a = None <-> mb a = None.

  Lemma mem_match_refl : forall m,
    mem_match m m.

  Lemma mem_match_trans : forall m ma mb,
    mem_match m ma ->
    mem_match ma mb ->
    mem_match m mb.

  Lemma mem_match_sym : forall ma mb,
    mem_match ma mb ->
    mem_match mb ma.

  Lemma mem_match_except : forall ma mb a,
    mem_match ma mb ->
    mem_match (mem_except ma a) (mem_except mb a).

  Lemma mem_match_upd : forall ma mb a va vb,
    mem_match ma mb ->
    mem_match (upd ma a va) (upd mb a vb).

  Lemma mem_match_upd_l : forall ma mb a va vb,
    mem_match ma mb ->
    mb a = Some vb ->
    mem_match (upd ma a va) mb.

  Lemma mem_match_upd_r : forall ma mb a va vb,
    mem_match ma mb ->
    ma a = Some va ->
    mem_match ma (upd mb a vb).

  Lemma mem_match_cases : forall ma mb a,
    mem_match ma mb ->
    (ma a = None /\ mb a = None) \/
    exists va vb, (ma a = Some va /\ mb a = Some vb).

End MEM_MATCH.


Section MEM_REGION.

  Variable V : Type.
  Implicit Types m ma mb : @Mem.mem _ addr_eq_dec V.

  Definition region_filled m st n :=
    forall a, a >= st -> a < st + n -> m a <> None.

  Lemma region_filled_sel : forall m st n a,
    region_filled m st n ->
    a >= st -> a < st + n ->
    exists v, m a = Some v.

  Lemma listupd_region_filled : forall l m a,
    region_filled (listupd m a l) a (length l).

(*
  Lemma arrayN_region_filled : forall l m a F,
    (F * arrayN a l)%pred m ->
    region_filled m a (length l).
*)

  Lemma mem_match_listupd_l : forall l ma mb a,
    mem_match ma mb ->
    region_filled mb a (length l) ->
    mem_match (listupd ma a l) mb.

End MEM_REGION.


Section MEM_INCL.

  Implicit Types m ma mb : rawdisk.

  Definition mem_incl ma mb := forall a,
    (ma a = None /\ mb a = None) \/
    exists va vb, ma a = Some va /\ mb a = Some vb /\
    incl (vsmerge va) (vsmerge vb).

  Lemma mem_incl_refl : forall m,
    mem_incl m m.

  Lemma mem_incl_trans : forall m ma mb,
    mem_incl ma m ->
    mem_incl m mb ->
    mem_incl ma mb.

  Lemma possible_crash_incl_trans : forall m ma mb,
    possible_crash ma m ->
    mem_incl ma mb ->
    possible_crash mb m.

  Lemma mem_incl_upd : forall a va vb ma mb,
    mem_incl ma mb ->
    incl (vsmerge va) (vsmerge vb) ->
    mem_incl (upd ma a va) (upd mb a vb).

  Lemma mem_incl_listupd : forall la lb,
    Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) la lb ->
    forall ma mb st,
    mem_incl ma mb ->
    mem_incl (listupd ma st la) (listupd mb st lb).

  Lemma mem_incl_listupd_same : forall la lb,
    Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) la lb ->
    forall m st,
    mem_incl (listupd m st la) (listupd m st lb).

End MEM_INCL.