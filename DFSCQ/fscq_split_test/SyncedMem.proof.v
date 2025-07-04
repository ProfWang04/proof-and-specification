Proof.
  unfold pushd, sm_ds_valid, ds_synced.
  split; intuition; cbn in *.
  all: repeat apply Forall_cons.
  all: try solve [eapply Forall_inv; eauto | eapply Forall_cons2; eauto].
  repeat (eapply Forall_cons2; eauto).
  eapply Forall_inv.
  eapply Forall_cons2; eauto.
Qed.
Proof.
  intros.
  apply sm_ds_valid_pushd_iff.
  auto.
Qed.
Proof.
  intros.
  rewrite <- sm_ds_valid_pushd_iff in H.
  intuition.
Qed.
Proof.
  intros.
  rewrite <- sm_ds_valid_pushd_iff in H.
  intuition.
Qed.
Proof.
  unfold vs_synced, vssync.
  intros.
  destruct (lt_dec i (length d)).
  destruct (addr_eq_dec i a); subst.
  rewrite selN_updN_eq; auto.
  rewrite selN_updN_ne; auto.
  rewrite updN_oob by omega; auto.
Qed.
Proof.
  unfold sm_vs_valid, Mem.upd, vsupd.
  intros.
  rewrite length_updN in *.
  intuition.
  destruct addr_eq_dec; subst.
  congruence.
  eapply H; eauto.
  destruct addr_eq_dec.
  congruence.
  unfold vs_synced.
  rewrite selN_updN_ne; auto.
  eapply H; eauto.
Qed.
Proof.
  unfold sm_vs_valid, Mem.upd; cbn.
  intros.
  rewrite length_updN in *.
  intuition.
  destruct addr_eq_dec; subst.
  congruence.
  eapply H; eauto.
  destruct addr_eq_dec; subst.
  unfold vs_synced.
  rewrite selN_updN_eq; auto.
  apply vs_synced_updN_synced.
  eapply H; eauto.
Qed.
Proof.
  unfold sm_vs_valid, Mem.upd; cbn.
  intros.
  rewrite length_updN in *.
  intuition.
  - eapply H; eauto.
  - destruct (addr_eq_dec a i); subst.
    + unfold vs_synced.
      rewrite selN_updN_eq; auto.
    + apply vs_synced_updN_synced.
      eapply H; eauto.
Qed.
Proof.
  unfold sm_vs_valid, vssync; intros.
  rewrite length_updN in *.
  intuition.
  eapply H; eauto.
  eapply H in H1; auto.
  eapply vs_synced_updN_synced.
  auto.
Qed.
Proof.
  unfold vs_synced, sm_vs_valid.
  intros.
  destruct (lt_dec a (length vs)) as [Hl|Hl].
  apply H in Hl; intuition.
  rewrite selN_oob by omega.
  auto.
Qed.
Proof.
  unfold sm_ds_valid.
  intros.
  constructor.
  rewrite dsupd_fst.
  eapply sm_vs_valid_upd_unsynced.
  eapply Forall_inv; eauto.
  unfold dsupd; cbn.
  rewrite <- Forall_map.
  rewrite Forall_forall in *.
  intros.
  cbn in *.
  eapply sm_vs_valid_upd_unsynced; auto.
Qed.
Proof.
  unfold latest, sm_ds_valid; cbn.
  intros.
  inversion H; subst.
  destruct (snd ds) eqn:?; cbn; eauto.
  eapply Forall_inv; eauto.
Qed.
Proof.
  unfold sm_ds_valid.
  cbn; intros.
  repeat (constructor; auto).
Qed.
Proof.
  unfold sm_ds_valid.
  intros.
  constructor.
  setoid_rewrite d_map_fst.
  unfold vssync.
  destruct (selN) eqn:?; cbn.
  apply sm_vs_valid_upd_synced.
  eapply Forall_inv; eauto.
  unfold dssync; cbn.
  rewrite <- Forall_map.
  inversion H; subst.
  rewrite Forall_forall in *.
  intros.
  eapply sm_vs_valid_upd_synced; auto.
Qed.
Proof.
  unfold sm_ds_valid; cbn; intros.
  inversion H; subst; constructor.
  eapply sm_vs_valid_vssync'; auto.
  rewrite <- Forall_map.
  rewrite Forall_forall in *.
  intros x; specialize (H x); intuition.
  eapply sm_vs_valid_vssync'; auto.
Qed.
Proof.
  induction al; cbn; intros.
  rewrite dssync_vecs_nop by constructor.
  auto.
  rewrite dssync_vecs_cons.
  rewrite dssync_vecs_dssync_comm.
  eapply sm_ds_valid_dssync'; auto.
Qed.
Proof.
  unfold ds_synced, sm_ds_valid.
  intros.
  rewrite Forall_forall in *.
  intros x; specialize (H x); intuition.
  eapply sm_vs_valid_vs_synced; eauto.
Qed.
Proof.
  intros.
  auto using sm_ds_valid_pushd, sm_ds_valid_latest.
Qed.
Proof.
  unfold d_in, sm_ds_valid.
  intros.
  inversion H; clear H; rewrite Forall_forall in *; subst.
  intuition; subst.
  auto.
Qed.
Proof.
  intros.
  eapply sm_ds_valid_d_in; eauto.
  eapply nthd_in_ds.
Qed.
Proof.
  unfold sm_vs_valid.
  intros.
  rewrite Forall_forall in *.
  rewrite H0 in *.
  intuition.
  eapply H; eauto.
  unfold vs_synced.
  eauto using in_selN.
Qed.
Proof.
  unfold sm_vs_valid, sm_disk_exact, list2nmem.
  intros.
  rewrite map_map.
  erewrite selN_map by auto.
  intuition.
  congruence.
  unfold vs_synced.
  inversion H0.
  destruct selN as [? l] eqn:H'.
  rewrite H' in *.
  destruct l; cbn in *; congruence.
Qed.
Proof.
  unfold sm_vs_valid; firstorder. discriminate.
  unfold sm_unsynced in *. congruence.
Qed.
Proof.
  unfold sm_ds_valid; intros.
  induction (fst ds :: snd ds); constructor; auto.
Qed.
Proof.
  unfold sm_set_vecs.
  induction a; cbn; intros.
  auto.
  rewrite <- IHa.
  cbn.
  destruct (Nat.eq_dec a x).
  congruence.
  rewrite Mem.upd_comm; auto.
Qed.
Proof.
  unfold sm_set_vecs.
  induction a; cbn; intros.
  auto.
  rewrite <- IHa.
  cbn.
  destruct (Nat.eq_dec a x).
  congruence.
  rewrite Mem.upd_comm; auto.
Qed.
Proof.
  eauto using sm_set_vecs_cons.
Qed.
Proof.
  eauto using sm_set_vecs_cons.
Qed.
Proof.
  eauto using sm_set_vecs_cons_inside.
Qed.
Proof.
  eauto using sm_set_vecs_cons_inside.
Qed.
Proof.
  induction a; intros.
  auto.
  destruct a.
  rewrite vsupd_vecs_cons, sm_upd_vecs_cons_inside.
  cbn.
  eapply IHa.
  eapply sm_vs_valid_upd_unsynced.
  auto.
Qed.
Proof.
  induction a; intros.
  auto.
  rewrite vssync_vecs_cons, sm_sync_vecs_cons_inside.
  eapply IHa.
  eapply sm_vs_valid_upd_synced.
  auto.
Qed.
Proof.
  intros.
  unfold sm_ds_valid; auto.
Qed.
Proof.
  intros.
  apply sm_vs_valid_ds_valid.
  rewrite Forall_forall; intros.
  unfold dsupd_vecs, d_map in *.
  cbn in *.
  intuition subst.
  eapply sm_vs_valid_vsupd_vecs.
  inversion H; auto.
  rewrite in_map_iff in *.
  deex.
  eapply sm_vs_valid_vsupd_vecs.
  inversion H; subst.
  rewrite Forall_forall in *.
  auto.
Qed.
Proof.
  intros.
  apply sm_vs_valid_ds_valid.
  rewrite Forall_forall; intros.
  unfold dssync_vecs, d_map in *.
  cbn in *.
  intuition subst.
  eapply sm_vs_valid_vssync_vecs.
  inversion H; auto.
  rewrite in_map_iff in *.
  deex.
  eapply sm_vs_valid_vssync_vecs.
  inversion H; subst.
  rewrite Forall_forall in *.
  auto.
Qed.
Proof.
  unfold mem_union, sm_sync_all.
  intros.
  apply functional_extensionality.
  intros.
  destruct m1, m2; auto.
Qed.
Proof.
  unfold mem_disjoint, sm_sync_all.
  intuition repeat deex.
  destruct m1 eqn:?, m2 eqn:?; try congruence.
  apply H; eauto.
Qed.
Proof.
  unfold_sep_star.
  unfold sm_sync_invariant.
  intuition repeat deex.
  repeat eexists.
  rewrite sm_sync_all_mem_union; eauto.
  eauto using sm_sync_all_mem_disjoint.
  all: auto.
Qed.
Proof.
  unfold_sep_star.
  intuition repeat deex.
  repeat eexists.
  rewrite sm_sync_all_mem_union.
  reflexivity.
  apply sm_sync_all_mem_disjoint; auto.
  all: auto.
Qed.
Proof.
  eauto using sm_sync_all_sep_star_swap.
Qed.
Proof.
  eauto using sm_sync_all_sep_star_swap.
Qed.
Proof.
  unfold sm_sync_invariant, sm_sync_all, lift_empty.
  intuition.
  rewrite H1; auto.
Qed.
Proof.
  unfold ptsto, sm_sync_all.
  intuition.
  rewrite H0; auto.
  rewrite H1; auto.
Qed.
Proof.
  unfold sm_sync_invariant, sm_sync_all, ptsto.
  intros.
  destruct H as [x ?].
  intuition.
  exists true.
  destruct sm; try congruence.
  intuition.
  rewrite H1; auto.
Qed.
Proof.
  unfold sm_sync_invariant, sm_sync_all, emp.
  intuition.
  rewrite H.
  auto.
Qed.
Proof.
  induction l; cbn; intros.
  apply sm_sync_invariant_emp.
  apply sm_sync_invariant_sep_star; auto.
Qed.
Proof.
  induction l; cbn; intros.
  apply sm_sync_invariant_emp; auto.
  eapply sm_sync_all_sep_star_swap; eauto.
Qed.
Proof.
  induction l; cbn; intros.
  apply sm_sync_invariant_emp; auto.
  eapply sm_sync_all_sep_star_swap; eauto.
  intros.
  specialize (H m 0).
  rewrite Nat.add_0_r in *.
  apply H; auto.
  omega.
  intros.
  eapply IHl; auto.
  intros.
  rewrite plus_Snm_nSm in *.
  apply H; auto.
  omega.
Qed.
Proof.
  unfold sm_sync_invariant.
  intros.
  intuition.
  all : do 3 match goal with H: _ |- _ => apply H end; auto.
Qed.
Proof.
  unfold mem_disjoint, mem_except_mem.
  intuition repeat deex.
  destruct ex; congruence.
Qed.
Proof.
  intros.
  unfold mem_union, mem_except_mem.
  eapply functional_extensionality.
  intros.
  destruct ex; auto.
  destruct m; auto.
Qed.
Proof.
  unfold sm_sync_all, mem_union, sm_synced.
  intros.
  eapply functional_extensionality.
  intros a.
  eapply equal_f in H.
  instantiate (1 := a) in H.
  destruct m eqn:?, m1 eqn:?; inversion H; subst.
  destruct m2 eqn:?; auto.
  match goal with Hm: mem_disjoint _ _ |- _ =>
    exfalso; apply Hm end.
  all: eauto.
Qed.
Proof.
  unfold_sep_star.
  intuition repeat deex.
  repeat eexists.
  3: eassumption.
  2: apply mem_except_mem_disjoint.
  rewrite mem_except_mem_union.
  eapply sm_sync_all_mem_union_sm_synced; eauto.
Qed.
Proof.
  intros.
  apply sep_star_comm.
  apply sep_star_comm in H.
  eauto using sm_synced_sep_star_l.
Qed.