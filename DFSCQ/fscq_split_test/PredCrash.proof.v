Proof.
  unfold crash_xform; eauto.
Qed.
Proof.
  intros.
  exists (fun a => match ma a with | None => None | Some v => m' a end).
  exists (fun a => match mb a with | None => None | Some v => m' a end).
  repeat split.

  - unfold mem_union; apply functional_extensionality; intros.
    case_eq (ma x); case_eq (mb x); case_eq (m' x); auto.
    intros; unfold possible_crash in *.
    destruct (H x).
    destruct H4; congruence.
    repeat deex. unfold mem_union in H5.
    rewrite H2 in H5. rewrite H3 in H5. congruence.
  - unfold mem_disjoint; intro; repeat deex.
    case_eq (ma a); case_eq (mb a); intros.
    firstorder.
    rewrite H1 in H3; congruence.
    rewrite H4 in H2; congruence.
    rewrite H4 in H2; congruence.
  - unfold possible_crash in *; intro a.
    case_eq (ma a); intros; [right|left]; auto.
    pose proof (mem_union_addr a H0 H1).
    destruct (H a); destruct H3; try congruence.
    repeat deex; repeat eexists; eauto.
    congruence.
  - unfold possible_crash in *; intro a.
    case_eq (mb a); intros; [right|left]; auto.
    rewrite mem_disjoint_comm in H0.
    pose proof (mem_union_addr a H0 H1); rewrite mem_union_comm in H2 by auto.
    destruct (H a); destruct H3; try congruence.
    repeat deex; repeat eexists; eauto.
    congruence.
Qed.
Proof.
  unfold mem_disjoint, possible_crash; intros.
  intro Hnot.
  repeat deex.
  destruct (H0 a); destruct (H1 a); try intuition congruence.
  repeat deex.
  apply H.
  do 3 eexists; eauto.
Qed.
Proof.
  unfold possible_crash, mem_union; intros.
  destruct (H a); destruct (H0 a).
  - destruct H1. destruct H2.
    rewrite H1 in *; rewrite H2 in *; rewrite H3 in *; rewrite H4 in *.
    intuition.
  - destruct H1. repeat deex.
    rewrite H1 in *; rewrite H2 in *; rewrite H3 in *; rewrite H4 in *.
    right. do 2 eexists. intuition.
  - repeat deex.
    rewrite H1 in *; rewrite H2 in *.
    right. do 2 eexists. intuition.
  - repeat deex.
    rewrite H1 in *; rewrite H3 in *; rewrite H4 in *.
    right. do 2 eexists. intuition.
Qed.
Proof.
  unfold possible_crash; intros.
  specialize (H a).
  specialize (H0 a).
  intuition; repeat deex; try congruence.
  right; repeat eexists; intuition eauto.
  rewrite H0 in H1.
  inversion H1; subst; clear H1.
  inversion H3.
  simpl in H1; subst; auto.
  inversion H1.
Qed.
Proof.
  unfold possible_crash; intuition.
  specialize (H a); intuition; repeat deex; congruence.
Qed.
Proof.
  unfold possible_crash; intuition.
  destruct (addr_eq_dec a a0); subst.
  repeat rewrite upd_eq; auto.
  specialize (H a0); intuition; right; eexists; eauto.
  repeat rewrite upd_ne; auto.
Qed.
Proof.
  unfold possible_crash; intuition.
  pose proof (H a) as H'; intuition; repeat deex.

  - repeat rewrite updSome_none by eauto.
    intuition.

  - destruct (addr_eq_dec a a0); subst.
    + repeat erewrite updSome_eq by eauto. right. eauto.
    + repeat rewrite updSome_ne by eauto. eauto.
Qed.
Proof.
  unfold synced_mem; intuition.
  specialize (H a); intuition; try congruence.
  destruct H1.
  rewrite H in H0; inversion H0; auto.
Qed.
Proof.
  unfold possible_crash, synced_mem; intuition.
  specialize (H a); intuition.
  right; repeat deex.
  eexists; eauto.
Qed.
Proof.
  unfold synced_mem, possible_crash; intuition.
  specialize (H a); intuition.
  destruct H0; right.
  do 2 eexists; simpl; intuition eauto.
Qed.
Proof.
  unfold possible_crash, emp; intros.
  specialize (H a); intuition; repeat deex.
  congruence.
Qed.
Proof.
  unfold possible_crash, emp; intros.
  specialize (H a); intuition; repeat deex.
  congruence.
Qed.
Proof.
  unfold possible_crash, vsmerge; simpl; intros.
  destruct vs, vs'; simpl in *.
  destruct (addr_eq_dec a0 a); subst.

  - specialize (H0 a); intuition.
    left; congruence.
    right; erewrite upd_eq by eauto; repeat deex; destruct vs; simpl in *.
    rewrite H in H2; inversion H2; subst.
    exists (w0, l0); exists w1; intuition.
    rewrite H in H2; inversion H2; subst.
    exists (w0, l0); exists v'; intuition.

  - rewrite upd_ne by auto.
    specialize (H0 a0); intuition.
Qed.
Proof.
  intros.
  eapply possible_crash_ptsto_upd_incl'; eauto.
  eapply ptsto_valid'; eauto.
Qed.
Proof.
  unfold possible_crash, vsmerge; intuition.
  destruct (addr_eq_dec a a1); subst; simpl in *.
  - specialize (H a1); intuition; right;
    erewrite upd_eq in * by eauto; try congruence.
    repeat deex.
    destruct vs, v0; inversion H2; subst; simpl in *.
    exists (w0, l0), w; intuition.
    destruct vs, v0; inversion H2; subst; simpl in *.
    exists (w0, l0), v'; intuition.
  - specialize (H a1); intuition; rewrite upd_ne in *; auto.
Qed.
Proof.
  intros.
  eapply possible_crash_upd_incl; eauto.
  unfold vsmerge; simpl.
  apply incl_cons2, incl_nil.
Qed.
Proof.
  intros.
  eapply possible_crash_ptsto_upd_incl; eauto.
  apply incl_cons2; simpl.
  unfold incl, postfix in *; destruct H1; subst; intuition.
  eapply in_skipn_in; eauto.
Qed.
Proof.
  unfold possible_crash; intuition.
  specialize (H a); intuition; try congruence.
  repeat deex; eexists; split; eauto.
  rewrite H0 in H1; inversion H1; subst; auto.
Qed.
Proof.
  unfold_sep_star; unfold crash_xform, piff, pimpl; split; intros; repeat deex.
  - edestruct possible_crash_mem_union; try eassumption; repeat deex.
    do 2 eexists; intuition; eexists; eauto.
  - eexists; split.
    do 2 eexists; intuition; [| eassumption | eassumption].
    eapply possible_crash_disjoint; eauto.
    apply possible_crash_union; eauto.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  unfold crash_xform, lift_empty, possible_crash; intros; split;
    intros m H; repeat deex.
  specialize (H1 a); destruct H1; intuition.
  repeat deex; congruence.
  eexists; intuition.
Qed.
Proof.
  unfold_sep_star; intros; repeat deex.
  edestruct possible_crash_mem_union; try eassumption; repeat deex.
  do 2 eexists; repeat split; auto; unfold crash_xform; eexists; split; eauto.
Qed.
Proof.
  split; unfold crash_xform, exis, pimpl; intros;
  repeat deex; repeat eexists; intuition eauto.
Qed.
Proof.
  unfold crash_xform, foral_, pimpl; intros.
  repeat deex; repeat eexists; intuition eauto.
Qed.
Proof.
  unfold crash_xform, possible_crash, ptsto, pimpl; intros.
  repeat deex; destruct (H1 a).
  intuition; congruence.
  repeat deex; rewrite H in H3; inversion H3; subst.
  repeat eexists.
  apply lift_impl.
  intros; eauto.
  split; auto.
  intros.
  destruct (H1 a').
  intuition.
  repeat deex.
  specialize (H2 a' H4).
  congruence.
Qed.
Proof.
  unfold crash_xform, possible_crash, ptsto, pimpl; intros.
  exists (insert empty_mem a vs).
  intuition.
  rewrite insert_eq; eauto.
  rewrite insert_ne; eauto.
  destruct (eq_nat_dec a a0); subst.
  - right. rewrite insert_eq; auto. exists vs. exists v. intuition.
  - left. rewrite insert_ne; auto.
Qed.
Proof.
  intros.
  rewrite crash_xform_exists_comm.
  apply pimpl_exists_l; intro.
  rewrite crash_xform_ptsto.
  apply pimpl_exists_l; intro.
  apply pimpl_exists_r.
  exists (x0, nil).
  rewrite sep_star_comm.
  apply sep_star_lift_l; intros; auto.
Qed.
Proof.
  unfold ptsto_subset; intros.
  rewrite crash_xform_exists_comm.
  apply pimpl_exists_l; intros.
  rewrite crash_xform_sep_star_dist, crash_xform_lift_empty.
  rewrite crash_xform_ptsto.
  apply sep_star_lift_l; intro.
  apply pimpl_exists_l; intros.
  rewrite sep_star_comm.
  apply sep_star_lift_l; intro.
  apply pimpl_exists_r; exists x0.
  apply sep_star_lift_r'.
  apply pimpl_and_split; auto.
  unfold lift, pimpl; intros.
  cbn in *; intuition.
Qed.
Proof.
  unfold ptsto_subset; intros.
  rewrite crash_xform_exists_comm.
  apply pimpl_exists_r; eexists.
  rewrite crash_xform_sep_star_dist, crash_xform_lift_empty.
  rewrite <- crash_xform_ptsto_r.
  apply sep_star_lift_r.
  apply pimpl_and_split; eauto.
  unfold lift, pimpl; intros.
  cbn in *; intuition.
  eauto.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  unfold crash_xform, possible_crash, emp, pimpl; repeat deex; intuition; repeat deex.
  destruct (H1 a); [ intuition | repeat deex; congruence ].
Qed.
Proof.
  unfold crash_xform, possible_crash, emp, pimpl. intros.
  exists empty_mem. intuition.
Qed.
Proof.
  unfold crash_xform, pimpl, possible_crash, ptsto; intros.
  deex; intuition eauto.
  { destruct (H1 a).
    + intuition; congruence.
    + repeat deex.
      inversion H5; subst; rewrite H in H3; inversion H3; subst; [ auto | inversion H4 ]. }
  { destruct (H1 a').
    + intuition.
    + repeat deex.
      assert (m' a' = None) by eauto; congruence.
  }
Qed.
Proof.
  intros.
  eapply ptsto_valid; eauto.
Qed.
Proof.
  unfold ptsto; unfold_sep_star; intros.
  repeat deex.
  destruct H1.
  destruct H0.
  eexists.
  apply mem_union_addr; eauto.
Qed.
Proof.
  unfold crash_xform, pimpl, diskIs.
  intros.
  destruct H; intuition; subst.
  exists m0.
  unfold_sep_star.
  exists (fun a => None).
  exists m0.
  intuition.
  unfold mem_disjoint; intuition.
  repeat deex; discriminate.
  unfold lift_empty; intuition.
Qed.
Proof.
  unfold crash_xform, pimpl, diskIs.
  intros; subst; firstorder.
Qed.
Proof.
  split.
  apply crash_xform_diskIs.
  apply pimpl_exists_l; intro.
  rewrite sep_star_comm.
  apply sep_star_lift_l; intro.
  apply crash_xform_diskIs_r; auto.
Qed.
Proof.
  unfold possible_crash, mem_except; intuition.
  specialize (H a0).
  destruct (addr_eq_dec a0 a); intuition.
Qed.
Proof.
  unfold mem_except, upd; intuition.
  apply functional_extensionality; intros.
  destruct (AEQ x a); intuition.
Qed.
Proof.
  intros.
  eapply possible_crash_mem_except in H.
  rewrite <- mem_except_upd in H.
  auto.
Qed.
Proof.
  unfold possible_crash; intuition.
  apply functional_extensionality; intros.
  specialize (H x); specialize (H0 x).
  intuition; repeat deex; try congruence.

  destruct vs, vs0; subst.
  rewrite H1 in H0; inversion H0; subst.
  unfold vsmerge in *; simpl in *.
  intuition; subst; congruence.
Qed.
Proof.
  intros.
  apply crash_xform_diskIs in H.
  apply crash_xform_diskIs in H0.
  destruct H; destruct H0.
  apply sep_star_comm in H; apply sep_star_lift_apply in H.
  apply sep_star_comm in H0; apply sep_star_lift_apply in H0.
  destruct H; destruct H0.
  rewrite crash_xform_diskIs, <- crash_xform_diskIs_r by eauto.
  unfold diskIs in *; subst.
  unfold pimpl; intros; subst.
  eapply possible_crash_eq; eauto.
  destruct H.
  apply sep_star_comm in H; apply sep_star_lift_apply in H; destruct H.
  subst; auto.
Qed.
Proof.
  unfold crash_xform, possible_crash; intuition.
  apply functional_extensionality; intros.
  repeat deex.
  specialize (H2 x); specialize (H3 x).
  intuition; repeat deex; try congruence.

  rewrite H, H2.
  unfold vsmerge, diskIs in *; destruct vs, vs0.
  simpl in *; intuition; subst; try congruence.
  rewrite H2 in H4; inversion H4; subst.
  inversion H5.
  rewrite H2 in H4; inversion H4; subst.
  inversion H5.
Qed.
Proof.
  unfold crash_xform, diskIs.
  unfold pimpl; intros.
  destruct H0; intuition subst.
  eexists; eauto.
Qed.
Proof.
  split.
  rewrite crash_xform_or_dist.
  apply pimpl_or_r; left; auto.
  rewrite crash_xform_or_dist.
  apply pimpl_or_l; auto.
  rewrite crash_xform_ptsto.
  apply pimpl_exists_l; intro.
  rewrite sep_star_comm.
  apply sep_star_lift_l; intro.
  rewrite crash_xform_ptsto_r; eauto.
  unfold vsmerge in *; simpl in *; intuition.
Qed.
Proof.
  split; rewrite crash_xform_or_dist.
  apply pimpl_or_r; right; auto.
  apply pimpl_or_l; auto.
  rewrite crash_xform_ptsto.
  apply pimpl_exists_l; intro.
  rewrite sep_star_comm.
  apply sep_star_lift_l; intro.
  rewrite <- crash_xform_ptsto_r; eauto.
  unfold vsmerge; simpl; intuition.
Qed.
Proof.
  unfold crash_xform, pimpl; intros.
  repeat deex; eexists; intuition eauto.
  eapply possible_crash_trans; eauto.
Qed.
Proof.
  unfold crash_xform, pimpl, possible_crash; intros.
  repeat deex; eexists; intuition eauto.
  specialize (H1 a); intuition.
  repeat destruct H; destruct H1.
  right.
  do 2 eexists; intuition eauto.
  cbn; left; auto.
Qed.
Proof.
  split.
  apply crash_xform_idem_l.
  apply crash_xform_idem_r.
Qed.
Proof.
  unfold crash_xform; intros.
  repeat deex.
  eapply possible_crash_synced; eauto.
Qed.
Proof.
  intros.
  apply possible_crash_refl.
  eapply crash_xform_synced; eauto.
Qed.
Proof.
  unfold pimpl, crash_xform; eauto.
Qed.
Proof.
  intros.
  apply H1.
  eapply pred_apply_crash_xform; eauto.
Qed.
Proof.
  unfold possible_sync; intros.
  destruct (m a); intuition eauto 10 using incl_refl.
Qed.
Proof.
  unfold possible_sync; intros.
  specialize (H a).
  specialize (H0 a).
  destruct (m1 a); intuition try congruence; repeat deex; try congruence.
  right.
  rewrite H0 in H1; inversion H1; subst.
  do 3 eexists; intuition eauto.
  eapply incl_tran; eauto.
Qed.
Proof.
  unfold possible_sync, sync_mem; intros.
  destruct (m a); intuition.
  right.
  repeat eexists.
  apply incl_nil.
Qed.
Proof.
  unfold possible_sync, sync_mem; intros.
  extensionality a.
  specialize (H a).
  destruct (m a) as [ [] | ];
    intuition eauto;
    repeat deex;
    try congruence.
  inversion H0; subst.
  apply ListUtils.incl_in_nil in H2; subst; eauto.
Qed.
Proof.
  unfold possible_sync; intros.
  destruct (AEQ a a0); subst.
  - right. exists v. exists l. exists l'. intuition.
    erewrite upd_eq; eauto.
  - erewrite upd_ne; eauto.
    destruct (m a0); intuition.
    right. do 3 eexists. intuition eauto. apply incl_refl.
Qed.
Proof.
  unfold sync_invariant, sync_xform, pimpl; intros.
  deex.
  eapply H; eauto.
  apply possible_sync_sync_mem.
Qed.
Proof.
  unfold pimpl, ptsto_subset; intros.
  exists (snd vs).
  apply sep_star_lift_apply'.
  destruct vs; exact H.
  firstorder.
Qed.
Proof.
  unfold pimpl, ptsto_subset; intros.
  destruct H.
  apply sep_star_lift_apply in H; intuition.
  eexists; eauto.
Qed.
Proof.
  unfold ptsto_subset; intros; split.
  apply pimpl_exists_l; intros; simpl.
  apply sep_star_lift_l; intros.
  erewrite incl_in_nil with (l := x); auto.
  apply pimpl_exists_r; intros; simpl.
  exists nil.
  apply sep_star_lift_r.
  apply pimpl_and_lift; auto.
  apply incl_nil.
Qed.
Proof.
  unfold pimpl, ptsto_subset; intros.
  destruct H0.
  apply sep_star_lift_apply in H0; intuition.
  eexists. apply sep_star_lift_apply'; eauto.
  eapply incl_tran; eauto.
Qed.
Proof.
  intros; rewrite crash_xform_ptsto_subset.
  apply pimpl_exists_l; intros.
  rewrite ptsto_pimpl_ptsto_subset.
  apply pimpl_exists_r; exists x; auto.
Qed.
Proof.
  unfold sync_mem, ptsto; destruct vs; intuition; subst.
  rewrite H1; simpl; auto.
  rewrite H2 by eauto; auto.
Qed.
Proof.
  unfold possible_sync, ptsto; intuition;
    remember H as H'; clear HeqH'; specialize (H' a); intuition; try congruence.
  repeat deex. rewrite H1 in H3. inversion H3; subst.
  eexists.
  apply sep_star_lift_apply'; eauto.
  intuition.
  specialize (H a'); intuition.
  repeat deex. rewrite H2 in H6; congruence.
Qed.
Proof.
  unfold sync_invariant, pimpl, ptsto_subset, lift; intuition.
  destruct H0.
  apply sep_star_lift_apply in H0; intuition.
  eapply possible_sync_ptsto in H; [ | eauto ].
  destruct H.
  apply sep_star_lift_apply in H; intuition.
  eexists.
  apply sep_star_lift_apply'. eauto.
  eapply incl_tran; eauto.
Qed.
Proof.
  unfold sync_invariant, pimpl; intros.
  destruct H0; destruct x.
  eapply possible_sync_ptsto in H; [ | eauto ].
  destruct H.
  apply sep_star_lift_apply in H; intuition.
  eexists; eauto.
Qed.
Proof.
  unfold sync_xform, ptsto_subset, pimpl; intros.
  deex. destruct H0. apply sep_star_lift_apply in H; intuition.
  eapply ptsto_sync_mem; eauto.
Qed.
Proof.
  intros.
  rewrite sync_xform_ptsto_subset_precise.
  unfold ptsto_subset, pimpl; intros.
  exists nil.
  apply sep_star_lift_apply'; eauto.
  apply incl_nil.
Qed.
Proof.
  unfold sync_invariant, pimpl; intros.
  eapply possible_sync_ptsto in H; [ | eauto ].
  destruct H. apply sep_star_lift_apply in H; intuition.
  apply incl_in_nil in H2; subst; eauto.
Qed.
Proof.
  unfold sync_invariant, possible_sync, emp, pimpl; intros.
  specialize (H0 a).
  specialize (H a).
  intuition.
  repeat deex. congruence.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  unfold sync_xform, sync_mem, lift_empty, possible_crash; intros; split;
    intros m H; repeat deex.
  rewrite H2; eauto.
  exists m; intuition.
  apply functional_extensionality; intros.
  rewrite H1; auto.
Qed.
Proof.
  unfold sync_xform, sync_mem, emp; split; intro; intros; repeat deex.
  destruct (m' a) eqn:?; congruence.
  eexists; split; eauto.
  apply functional_extensionality; intros.
  destruct (m x) eqn:?; congruence.
Qed.
Proof.
  unfold mem_union, sync_mem; intros.
  apply functional_extensionality; intros.
  destruct (m1 x); auto.
  destruct p; auto.
Qed.
Proof.
  unfold mem_disjoint, sync_mem; intuition.
  apply H.
  repeat deex.
  exists a.
  destruct (m1 a); try congruence.
  destruct (m2 a); try congruence.
  eauto.
Qed.
Proof.
  unfold mem_disjoint, sync_mem; intuition.
  apply H.
  repeat deex.
  exists a. destruct v1. destruct v2.
  rewrite H1. rewrite H2. eauto.
Qed.
Proof.
  unfold_sep_star; unfold sync_xform, piff, pimpl; split; intros; repeat deex.
  - exists (sync_mem m1). exists (sync_mem m2). intuition eauto.
  - exists (mem_union m'0 m'); intuition.
    do 2 eexists; intuition.
Qed.
Proof.
  split; unfold sync_xform, exis, pimpl; intros;
  repeat deex; repeat eexists; intuition eauto.
Qed.
Proof.
  unfold sync_xform, foral_, pimpl; intros.
  repeat deex; repeat eexists; intuition eauto.
Qed.
Proof.
  unfold sync_xform, pimpl; intros.
  deex; eauto.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  unfold sync_xform, diskIs, pimpl; intros.
  deex; auto.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  unfold sync_mem; intros.
  apply functional_extensionality; intros.
  destruct (m x); auto.
  destruct p; auto.
Qed.
Proof.
  unfold sync_xform, piff, pimpl; split; intros; repeat deex.
  - exists m'0; intuition. apply sync_mem_idem.
  - eexists; split.
    exists m'; intuition.
    rewrite sync_mem_idem; auto.
Qed.
Proof.
  unfold sync_invariant; intros.
  destruct H1. eexists. eauto.
Qed.
Proof.
  intros.
  exists (fun a => match ma a with | None => None | Some v => m' a end).
  exists (fun a => match mb a with | None => None | Some v => m' a end).
  repeat split.

  - unfold mem_union; apply functional_extensionality; intros.
    case_eq (ma x); case_eq (mb x); case_eq (m' x); auto.
    intros; unfold possible_sync in *.
    destruct (H x).
    destruct H4; congruence.
    repeat deex. unfold mem_union in H5.
    rewrite H2 in H5. rewrite H3 in H5. congruence.
  - unfold mem_disjoint; intro; repeat deex.
    case_eq (ma a); case_eq (mb a); intros.
    firstorder.
    rewrite H1 in H3; congruence.
    rewrite H4 in H2; congruence.
    rewrite H4 in H2; congruence.
  - intro a.
    case_eq (ma a); intros; [right|left]; auto.
    pose proof (mem_union_addr a H0 H1).
    destruct (H a); destruct H3; try congruence.
    repeat deex; repeat eexists; eauto.
    congruence.
  - intro a.
    case_eq (mb a); intros; [right|left]; auto.
    rewrite mem_disjoint_comm in H0.
    pose proof (mem_union_addr a H0 H1); rewrite mem_union_comm in H2 by auto.
    destruct (H a); destruct H3; try congruence.
    repeat deex; repeat eexists; eauto.
    congruence.
Qed.
Proof.
  unfold mem_disjoint; intros.
  intro Hnot.
  repeat deex.
  destruct (H0 a); destruct (H1 a); try intuition congruence.
  repeat deex.
  apply H.
  do 3 eexists; eauto.
Qed.
Proof.
  unfold possible_sync, mem_union; intros.
  destruct (H a); destruct (H0 a).
  - destruct H1. destruct H2.
    rewrite H1 in *; rewrite H2 in *; rewrite H3 in *; rewrite H4 in *.
    intuition.
  - destruct H1. repeat deex.
    rewrite H1 in *; rewrite H2 in *; rewrite H3 in *; rewrite H4 in *.
    right. do 3 eexists. intuition.
  - repeat deex.
    rewrite H1 in *; rewrite H2 in *.
    right. do 3 eexists. intuition.
  - repeat deex.
    rewrite H1 in *; rewrite H3 in *; rewrite H4 in *.
    right. do 3 eexists. intuition.
Qed.
Proof.
  unfold_sep_star; unfold sync_invariant; intros; repeat deex.
  apply possible_sync_mem_union in H1; eauto; repeat deex.
  do 2 eexists. intuition eauto.
Qed.
Proof.
  unfold sync_invariant; intros.
  apply star_emp_pimpl; apply pimpl_star_emp in H0.
  apply sep_star_lift_apply in H0. apply sep_star_lift_apply'; intuition.
  eapply sync_invariant_emp; eauto.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  unfold possible_sync, possible_crash; intros.
  specialize (H a); specialize (H0 a); intuition; repeat deex; try congruence.
  right.
  do 2 eexists; intuition eauto.
  rewrite H0 in H1; inversion H1; subst.
  rewrite H.
  rewrite incl_in_nil with (l := l'); eauto.
Qed.
Proof.
  induction l'; simpl; intros.
  - destruct l.
    apply incl_refl.
    specialize (H w); simpl in *; intuition.
  - unfold vsmerge; simpl.
    unfold incl; simpl in *; intros; intuition eauto.
    specialize (H a0); simpl in *; intuition eauto.
Qed.
Proof.
  unfold possible_sync, possible_crash; intros.
  specialize (H a); specialize (H0 a); intuition; repeat deex; try congruence.
  right.
  do 2 eexists; intuition eauto.
  rewrite H0 in H1; inversion H1; subst.
  eapply incl_vsmerge; eauto.
Qed.
Proof.
  unfold sync_invariant, crash_xform; intros; deex.
  eexists; split; eauto.
  eapply possible_sync_possible_crash_trans; eauto.
Qed.
Proof.
  intros.
  eapply H; eauto.
  eapply possible_sync_upd; eauto.
Qed.
Proof.
  unfold ptsto_subset, ptsto; unfold_sep_star.
  intros; repeat deex.
  destruct H1. repeat deex.
  eexists; split.
  apply mem_union_addr; eauto.
  apply mem_union_addr; eauto.
  apply H5.
Qed.
Proof.
  intros.
  apply sep_star_comm in H.
  eapply ptsto_subset_valid; eauto.
Qed.
Proof.
  unfold ptsto_subset; simpl in *; intros.
  apply sep_star_comm in H.
  apply pimpl_exists_r_star_r in H.
  destruct H.
  apply sep_star_assoc in H.
  eapply ptsto_upd with (v := (v, vs')) in H.
  setoid_rewrite sep_star_comm in H.
  apply sep_star_assoc in H.
  apply sep_star_lift_apply in H; destruct H.

  apply sep_star_comm.
  apply pimpl_exists_r_star.
  eapply pimpl_exists_r; eauto.
  setoid_rewrite sep_star_comm.
  apply sep_star_assoc; apply sep_star_comm.
  apply sep_star_lift_apply'; eauto.
Qed.