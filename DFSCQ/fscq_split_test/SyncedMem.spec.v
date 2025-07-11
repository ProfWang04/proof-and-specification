Require Import FunctionalExtensionality.
Require Import Arith.
Require Import Omega.
Require Import List.
Require Import Pred.
Require Import Mem.
Require Import AsyncDisk.
Require Import DiskSet.
Require Import Array.
Require Import ListUtils.
Require Import LogReplay.
Require Import GenSepN.
Require Import ListPred.

Import ListNotations.

Definition syncedmem := @Mem.mem _ addr_eq_dec bool.

Definition sm_vs_valid (sm : @Mem.mem _ addr_eq_dec _) vs :=
  forall a, a < length vs -> sm a <> None /\ (sm a = Some true -> vs_synced a vs).

Definition sm_ds_valid (sm : @Mem.mem _ addr_eq_dec _) ds :=
  Forall (sm_vs_valid sm) (fst ds :: snd ds).

Lemma sm_ds_valid_pushd_iff: forall sm ds d,
  sm_ds_valid sm ds /\ sm_vs_valid sm d <-> sm_ds_valid sm (pushd d ds).

Lemma sm_ds_valid_pushd: forall sm ds d,
  sm_vs_valid sm d ->
  sm_ds_valid sm ds -> sm_ds_valid sm (pushd d ds).

Lemma sm_ds_valid_pushd_r: forall sm ds d,
  sm_ds_valid sm (pushd d ds) ->
  sm_ds_valid sm ds.

Lemma sm_ds_valid_pushd_l: forall sm ds d,
  sm_ds_valid sm (pushd d ds) ->
  sm_vs_valid sm d.

Lemma vs_synced_updN_synced: forall a d i v,
  vs_synced a d ->
  vs_synced a (updN d i (v, nil)).

Lemma sm_vs_valid_upd_unsynced: forall sm d a v,
  sm_vs_valid sm d ->
  sm_vs_valid (Mem.upd sm a false) (updN d a v).

Lemma sm_vs_valid_upd_synced: forall sm i d v,
  sm_vs_valid sm d ->
  sm_vs_valid (Mem.upd sm i true) (updN d i (v, nil)).

Lemma sm_vs_valid_same_upd_synced: forall sm i d v,
  sm_vs_valid sm d ->
  sm_vs_valid sm (updN d i (v, nil)).

Lemma sm_vs_valid_vssync': forall sm vs a,
  sm_vs_valid sm vs -> sm_vs_valid sm (vssync vs a).

Lemma sm_vs_valid_vs_synced: forall sm vs a,
  sm_vs_valid sm vs -> sm a = Some true ->
  vs_synced a vs.


Lemma sm_ds_valid_dsupd: forall sm ds a v,
  a < length (ds!!) ->
  sm_ds_valid sm ds ->
  sm_ds_valid (Mem.upd sm a false) (dsupd ds a v).

Lemma sm_ds_valid_latest: forall sm ds,
  sm_ds_valid sm ds ->
  sm_vs_valid sm ds!!.

Lemma sm_ds_valid_synced: forall sm d,
  sm_vs_valid sm d ->
  sm_ds_valid sm (d, nil).

Lemma sm_ds_valid_dssync: forall sm ds a,
  sm_ds_valid sm ds ->
  sm_ds_valid (Mem.upd sm a true) (dssync ds a).

Lemma sm_ds_valid_dssync': forall sm ds a,
  sm_ds_valid sm ds -> sm_ds_valid sm (dssync ds a).

Lemma sm_ds_valid_dssync_vecs': forall sm ds al,
  sm_ds_valid sm ds -> sm_ds_valid sm (dssync_vecs ds al).

Lemma sm_ds_valid_ds_synced: forall sm ds a,
  sm_ds_valid sm ds -> sm a = Some true ->
  ds_synced a ds.


Lemma sm_ds_valid_pushd_latest: forall sm ds,
  sm_ds_valid sm ds ->
  sm_ds_valid sm (pushd ds!! ds).

Lemma sm_ds_valid_d_in: forall sm ds d,
  sm_ds_valid sm ds ->
  d_in d ds ->
  sm_vs_valid sm d.

Lemma sm_ds_valid_nthd: forall n sm ds,
  sm_ds_valid sm ds ->
  sm_vs_valid sm (nthd n ds).

Lemma sm_vs_valid_all_synced: forall sm d d',
  sm_vs_valid sm d ->
  length d = length d' ->
  Forall (fun v => snd v = []) d' ->
  sm_vs_valid sm d'.

Definition sm_disk_exact (d : diskstate) :=
  list2nmem (map (fun v => match (snd v) with [] => true | _ => false end) d).

Lemma sm_vs_valid_disk_exact: forall d,
  sm_vs_valid (sm_disk_exact d) d.

Definition sm_unsynced : syncedmem := fun _ => Some false.
Definition sm_synced : syncedmem := fun _ => Some true.
Definition sm_sync_all (sm : syncedmem) : syncedmem := fun a =>
  match sm a with
  | None => None
  | Some _ => Some true
  end.

Definition sm_sync_invariant (p : pred) : Prop := forall sm, p sm -> p (sm_sync_all sm).

Lemma sm_vs_valid_sm_unsynced: forall d,
  sm_vs_valid sm_unsynced d.
Local Hint Resolve sm_vs_valid_sm_unsynced.

Lemma sm_ds_valid_sm_unsynced: forall ds,
  sm_ds_valid sm_unsynced ds.

Definition sm_set_vecs (b : bool) (sm : syncedmem) (a : list addr) :=
  fold_left (fun sm a => @Mem.upd _ _ addr_eq_dec sm a b) a sm.

Definition sm_upd_vecs sm (a : list (_ * valu)) := sm_set_vecs false sm (map fst a).
Definition sm_sync_vecs := sm_set_vecs true.

Lemma sm_set_vecs_cons: forall a sm x b,
  sm_set_vecs b sm (x :: a) = Mem.upd (sm_set_vecs b sm a) x b.

Lemma sm_set_vecs_cons_inside: forall a sm x b,
  sm_set_vecs b sm (x :: a) = sm_set_vecs b (Mem.upd sm x b) a.

Lemma sm_upd_vecs_cons: forall a sm x,
  sm_upd_vecs sm (x :: a) = Mem.upd (sm_upd_vecs sm a) (fst x) false.

Lemma sm_sync_vecs_cons: forall a sm x,
  sm_sync_vecs sm (x :: a) = Mem.upd (sm_sync_vecs sm a) x true.

Lemma sm_upd_vecs_cons_inside: forall a sm x,
  sm_upd_vecs sm (x :: a) = sm_upd_vecs (Mem.upd sm (fst x) false) a.

Lemma sm_sync_vecs_cons_inside: forall a sm x,
  sm_sync_vecs sm (x :: a) = sm_sync_vecs (Mem.upd sm x true) a.

Lemma sm_vs_valid_vsupd_vecs: forall a sm v,
  sm_vs_valid sm v ->
  sm_vs_valid (sm_upd_vecs sm a) (vsupd_vecs v a).

Lemma sm_vs_valid_vssync_vecs: forall a sm v,
  sm_vs_valid sm v ->
  sm_vs_valid (sm_sync_vecs sm a) (vssync_vecs v a).

Lemma sm_vs_valid_ds_valid: forall sm ds,
  Forall (sm_vs_valid sm) (fst ds :: snd ds) ->
  sm_ds_valid sm ds.

Lemma sm_ds_valid_dsupd_vecs: forall a sm ds,
  sm_ds_valid sm ds ->
  sm_ds_valid (sm_upd_vecs sm a) (dsupd_vecs ds a).

Lemma sm_ds_valid_dssync_vecs: forall a sm ds,
  sm_ds_valid sm ds ->
  sm_ds_valid (sm_sync_vecs sm a) (dssync_vecs ds a).

Lemma sm_sync_all_mem_union: forall AEQ m1 m2,
  @mem_union _ AEQ _ (sm_sync_all m1) (sm_sync_all m2) = sm_sync_all (mem_union m1 m2).

Lemma sm_sync_all_mem_disjoint: forall m1 m2 AEQ,
  mem_disjoint m1 m2 -> @mem_disjoint _ AEQ _ (sm_sync_all m1) (sm_sync_all m2).

Lemma sm_sync_invariant_sep_star: forall (p q : pred),
  sm_sync_invariant p -> sm_sync_invariant q ->
  sm_sync_invariant (p * q).

Lemma sm_sync_all_sep_star_swap: forall AEQ (p p' q q' : @pred _ AEQ _) sm,
  (p * q)%pred sm ->
  (forall m, p m -> p' (sm_sync_all m)) ->
  (forall m, q m -> q' (sm_sync_all m)) ->
  (p' * q')%pred (sm_sync_all sm).

Lemma sm_sync_all_sep_star_swap_l: forall (p p' q : pred) sm,
  (p * q)%pred sm ->
  (forall m, p m -> p' (sm_sync_all m)) ->
  sm_sync_invariant q ->
  (p' * q)%pred (sm_sync_all sm).

Lemma sm_sync_all_sep_star_swap_r: forall (p q q' : pred) sm,
  (p * q)%pred sm ->
  (forall m, q m -> q' (sm_sync_all m)) ->
  sm_sync_invariant p ->
  (p * q')%pred (sm_sync_all sm).

Lemma sm_sync_invariant_lift_empty: forall P,
  sm_sync_invariant (lift_empty P).

Lemma sm_sync_all_ptsto: forall AEQ a b (m : syncedmem),
  (@ptsto _ AEQ _ a b)%pred m ->
  (@ptsto _ AEQ _ a true)%pred (sm_sync_all m).

Lemma sm_sync_invariant_exis_ptsto: forall a,
  sm_sync_invariant (a |->?)%pred.

Lemma sm_sync_invariant_emp:
  sm_sync_invariant emp.

Lemma sm_sync_invariant_listpred: forall T prd (l : list T),
  (forall x, In x l -> sm_sync_invariant (prd x)) ->
  sm_sync_invariant (listpred prd l).

Lemma sm_sync_all_listpred_swap: forall T AEQ (prd prd' : T -> @pred _ AEQ _) (l : list T) sm,
  (forall sm x, In x l -> prd x sm -> prd' x (sm_sync_all sm)) ->
  listpred prd l sm ->
  listpred prd' l (sm_sync_all sm).

Lemma sm_sync_all_arrayN_swap: forall T AEQ (prd prd' : nat -> T -> @pred _ AEQ _) d (l : list T) i sm,
  (forall sm  i' x, i' < length l -> selN l i' d = x -> prd (i + i') x sm -> prd' (i + i') x (sm_sync_all sm)) ->
  arrayN prd i l sm ->
  arrayN prd' i l (sm_sync_all sm).

Lemma sm_sync_invariant_piff: forall (p q : pred),
  piff p q -> sm_sync_invariant p <-> sm_sync_invariant q.

Hint Resolve sm_sync_invariant_sep_star.
Hint Resolve sm_sync_invariant_exis_ptsto.
Hint Resolve sm_sync_invariant_emp.
Hint Resolve sm_sync_invariant_lift_empty.
Hint Resolve sm_sync_invariant_listpred.

Hint Resolve sm_sync_all_ptsto.

Definition mem_except_mem {AT AEQ V} (m ex : @Mem.mem AT AEQ V) : @Mem.mem AT AEQ V := fun a =>
  match ex a with
  | Some _ => None
  | None => m a
  end.

Lemma mem_except_mem_disjoint: forall AT AEQ V (m ex : @Mem.mem AT AEQ V),
  mem_disjoint (mem_except_mem m ex) ex.

Lemma mem_except_mem_union: forall AT AEQ V (m ex : @Mem.mem AT AEQ V),
  mem_union (mem_except_mem m ex) ex = (mem_union ex m).

Lemma sm_sync_all_mem_union_sm_synced: forall m m1 m2,
  sm_sync_all m = mem_union m1 m2 ->
  mem_disjoint m1 m2 ->
  sm_synced = mem_union m2 sm_synced.

Lemma sm_synced_sep_star_l: forall AEQ (p q : @pred _ AEQ _) m,
  (p * q)%pred (sm_sync_all m) ->
  (any * q)%pred sm_synced.

Lemma sm_synced_sep_star_r: forall AEQ (p q : @pred _ AEQ _) m,
  (p * q)%pred (sm_sync_all m) ->
  (p * any)%pred sm_synced.