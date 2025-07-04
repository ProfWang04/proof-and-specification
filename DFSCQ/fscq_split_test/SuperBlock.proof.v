  Proof.
    simpl. rewrite valulen_is. apply Nat.eqb_eq.
    compute. reflexivity.
  Qed.
  Proof.
    unfold pickle_superblock, unpickle_superblock.
    destruct fsxp.
    repeat rewrite Rec.of_to_id.
    destruct FSXPLog.
    destruct FSXPInode.
    destruct FSXPInodeAlloc.
    destruct FSXPBlockAlloc1.
    destruct FSXPBlockAlloc2.
    unfold Rec.recget', Rec.recset'.
    unfold addr2w; simpl; intros.
    repeat rewrite wordToNat_natToWord_idempotent' by xparams_ok.
    auto.
    unfold Rec.well_formed.
    simpl.
    intuition.
  Qed.
  Proof.
    intros.
    unfold v_pickle_superblock, v_unpickle_superblock.
    unfold eq_rec_r, eq_rec.
    rewrite eq_rect_nat_double.
    rewrite <- (eq_rect_eq_dec eq_nat_dec).
    apply pickle_unpickle_superblock; auto.
  Qed.
  Proof.
    unfold magic_number.
    eapply wordToNat_natToWord_idempotent'_iff; eauto.
  Qed.
  Proof.
    unfold load, rep.
    hoare.
    apply v_pickle_unpickle_superblock; auto.
  Qed.
  Proof.
    unfold rep, init.
    step.
    rewrite ptsto_pimpl_ptsto_subset; cancel.
    hoare.
    xcrash.
    xcrash.
    xcrash.
    xcrash.
  Qed.
  Proof.
    unfold rep; intros; split;
    rewrite crash_xform_sep_star_dist;
    rewrite crash_xform_sep_star_dist;
    repeat rewrite crash_xform_lift_empty.

    rewrite crash_xform_ptsto_subset; cancel.
    rewrite ptsto_pimpl_ptsto_subset.
    subst; auto.

    rewrite <- crash_xform_ptsto_subset_r.
    cancel.
    rewrite ptsto_subset_pimpl_ptsto; eauto.
    unfold vsmerge; simpl; auto.
  Qed.
  Proof.
    unfold rep; eauto.
  Qed.
  Proof.
    unfold rep; intros; cancel.
  Qed.