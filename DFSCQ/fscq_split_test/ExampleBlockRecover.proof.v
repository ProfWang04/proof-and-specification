Proof.
  unfold recover, LOG.after_crash; intros.
  prestep. norm. cancel. intuition; eauto.
  prestep. norm. cancel. intuition; eauto.
  pred_apply; cancel.

  prestep.
  unfold LOG.after_crash; norm. cancel.
  intuition simpl.
  pred_apply; norm. cancel.
  intuition simpl; eauto.

  safestep; eauto.
  subst; pimpl_crash; eauto.

  subst; pimpl_crash. norm; try tauto. cancel.
  intuition; pred_apply. norm. cancel.
  intuition eauto.

  subst; pimpl_crash. norm; try tauto. cancel.
  intuition; pred_apply. norm. cancel.
  intuition eauto.
Qed.
Proof.
  unfold update_block_d; intros.
  step.
  step.

  (* XXX: why eauto with prog pick the wrong spec? *)
  eapply pimpl_ok2.
  apply LOG.commit_ro_ok.
  cancel.
  instantiate (1 := (m1, nil)); simpl.
  rewrite singular_latest by auto; simpl; cancel.

  step.
  subst; pimpl_crash.
  cancel. or_r; cancel; eauto.
  rewrite LOG.notxn_idempred; auto.

  or_l; rewrite LOG.recover_any_idempred; cancel.
  or_r; rewrite LOG.active_idempred; cancel.
  or_l; rewrite LOG.notxn_idempred; cancel.
Qed.
Proof.
  unfold forall_helper.
  intros; eexists; intros.
  eapply pimpl_ok3.
  eapply corr3_from_corr2_rx.
  eapply update_block_d_ok.
  eapply recover_ok.
  cancel.
  eapply pimpl_ok2.
  eapply H2.
  cancel.
  subst.
  apply pimpl_refl.
  cancel_exact.
  apply pimpl_refl.
  xform_norm.

  - rewrite LOG.idempred_idem.
    xform_norml.
    rewrite SB.crash_xform_rep.
    recover_ro_ok.
    cancel.

    step.
    pred_apply.
    replace n with 0 by omega; rewrite nthd_0; simpl.
    rewrite crash_xform_diskIs_pred by eauto.
    xform_dist; rewrite crash_xform_ptsto; cancel.

    cancel.
    rewrite LOG.after_crash_idempred; cancel.

  - rewrite LOG.idempred_idem.
    xform_norml.
    rewrite SB.crash_xform_rep.
    recover_ro_ok.
    cancel.

    step.
    pred_apply.
    replace n with 0 by omega; rewrite nthd_0; simpl.
    rewrite crash_xform_diskIs_pred by eauto.
    xform_dist; rewrite crash_xform_ptsto; cancel.

    cancel.
    rewrite LOG.after_crash_idempred; cancel.
Qed.
Proof.
  unfold update_block_d2; intros.
  step.
  step.

  (* XXX: why eauto with prog pick the wrong spec? *)
  eapply pimpl_ok2.
  apply LOG.commit_ok.
  cancel.
  step.

  subst; pimpl_crash; cancel.
  or_r; rewrite LOG.notxn_idempred; cancel.
  or_l; rewrite LOG.recover_any_idempred; cancel.
  or_r; rewrite LOG.active_idempred; cancel.
  or_l; rewrite LOG.notxn_idempred; cancel.
Qed.
Proof.
  unfold forall_helper.
  intros; eexists; intros.
  eapply pimpl_ok3.
  eapply corr3_from_corr2_rx.
  eapply update_block_d2_ok.
  eapply recover_ok.
  cancel.
  eapply pimpl_ok2.
  eapply H2.
  cancel.
  subst.
  or_l. cancel. subst.
  apply pimpl_refl.
  or_r. cancel. subst.
  apply pimpl_refl.
  apply pimpl_refl.

  xform_norm.

  - rewrite LOG.idempred_idem.
    xform_norml.
    rewrite SB.crash_xform_rep.
    recover_ro_ok.
    cancel.

    step.
    destruct v0; simpl in *.
    or_l; norm. cancel.
    eassign n; intuition.

    cancel.
    or_l; destruct v0.
    rewrite LOG.after_crash_idempred; cancel.

  - rewrite LOG.idempred_idem.
    xform_norml.
    rewrite SB.crash_xform_rep.
    recover_ro_ok.
    cancel.

    step.
    destruct v0; simpl in *.
    or_r; norm. cancel.
    pred_apply.
    replace n with 0 by omega; rewrite nthd_0; simpl.
    rewrite crash_xform_diskIs_pred by eauto.
    xform_dist; rewrite crash_xform_ptsto; cancel.

    cancel.
    rewrite LOG.after_crash_idempred; cancel.
Qed.