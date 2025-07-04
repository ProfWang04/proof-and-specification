  Proof.
    unfold fs_xparams_ok.
    unfold log_xparams_ok, inode_xparams_ok, balloc_xparams_ok.
    unfold compute_xparams; simpl.
    intuition.
    all: eapply goodSize_trans; try eassumption.
    all: lia.
  Qed.
  Proof.
    intros; omega.
  Qed.
  Proof.
    intros; omega.
  Qed.
  Proof.
    unfold mkfs.
    safestep.

    prestep.
    norml; unfold stars; simpl.
    denote! (arrayS _ _ _) as Hx.
    eapply arrayN_isolate_hd in Hx.
    unfold ptsto_subset in Hx at 1.
    safecancel.
    apply compute_xparams_ok.
    apply SB.goodSize_magic_number.
    denote (length disk = _) as Heq; rewrite Heq in *; auto.
    auto.

    (* LOG.init *)
    prestep. norm. cancel.
    intuition simpl. pred_apply.
    (* split LHS into log region and data region *)
    erewrite arrayN_split at 1.
    simpl.
    rewrite sep_star_comm.
    apply sep_star_assoc.

    rewrite skipn_length.
    setoid_rewrite skipn_length with (n := 1).
    substl (length disk).
    apply S_minus_1_helper.

    rewrite firstn_length.
    setoid_rewrite skipn_length with (n := 1).
    substl (length disk).
    rewrite Nat.min_l.
    rewrite Nat.sub_0_r; auto.
    rewrite S_minus_1_helper2.
    generalize (data_bitmaps * valulen + inode_bitmaps * valulen / INODE.IRecSig.items_per_val); intros.
    generalize (log_descr_blocks * PaddedLog.DescSig.items_per_val); intros.
    omega.

    eapply goodSize_trans; [ | eauto ].
    rewrite skipn_length.
    setoid_rewrite skipn_length with (n := 1).
    substl (length disk).
    generalize (data_bitmaps * valulen + inode_bitmaps * valulen / INODE.IRecSig.items_per_val); intros.
    generalize (log_descr_blocks * PaddedLog.DescSig.items_per_val); intros.
    omega.
    auto.
    auto.
    step.
    rewrite Nat.sub_0_r in *.

    (* BFILE.init *)
    step.

    (* IAlloc.alloc *)
    step.
    step.
    step.
    step.

    (* LOG.flushsync *)
    step.
    step.

    rewrite latest_pushd.
    equate_log_rep.
    cancel. or_r.
    unfold rep. cancel.

    denote (_ =p=> freeinode_pred) as Hy.
    denote (freeinode_pred =p=> _) as Hz.

    rewrite <- Hy in Hz.
    2: apply repeat_length with (x := BFILE.bfile0).


    assert (1 < length (repeat BFILE.bfile0 (inode_bitmaps * valulen
       / INODE.IRecSig.items_per_val * INODE.IRecSig.items_per_val))) as Hlen.
    rewrite repeat_length; omega.

    specialize (Hz _ (list2nmem_array _)).
    pred_apply; cancel.
    pose proof (list2nmem_ptsto_cancel BFILE.bfile0 _ Hlen).
    unfold tree_dir_names_pred.
    cancel.
    unfold BFILE.freepred in *. subst.
    apply DirTreePred.SDIR.bfile0_empty.
    apply emp_empty_mem.
    eapply Forall_repeat.
    eauto.

    (* failure cases *)
    apply pimpl_any.
    step.
    step.
    step.
    equate_log_rep.
    cancel.
    or_l; cancel.

    apply pimpl_any.
    step.
    step.
    equate_log_rep.
    cancel.
    or_l; cancel.

    apply pimpl_any.
    step.
    equate_log_rep.
    cancel.
    or_l; cancel.

    all: try solve [ try xcrash; apply pimpl_any ].
    substl (length disk).
    apply gt_Sn_O.

  Unshelve.
    all: try easy.
    try exact ($0, nil).
  Qed.
  Proof.
    unfold recover, LOG.after_crash; intros.
    eapply pimpl_ok2; monad_simpl.
    eapply BUFCACHE.init_recover_ok.
    intros; norm. cancel.
    intuition simpl. eauto.

    prestep. norml.
    denote ((crash_xform _) d') as Hx.
    apply crash_xform_sep_star_dist in Hx.
    rewrite SB.crash_xform_rep in Hx.
    rewrite LOG.after_crash_idem' in Hx; eauto.
    destruct_lift Hx; denote (crash_xform (crash_xform _)) as Hx.
    apply crash_xform_idem_l in Hx.

    norm. cancel.
    intuition.
    pred_apply.
    apply sep_star_comm; eauto.

    step.
    prestep. norm. cancel.
    unfold LOG.after_crash; norm. cancel.
    intuition simpl.
    pred_apply; norml.
    unfold stars; simpl.

    norm. cancel.
    rewrite LOG.rep_inner_hashmap_subset.
    eassign (SB.rep fsxp).
    cancel.
    or_l; cancel.
    auto.
    intuition simpl; eauto.
    safecancel.
    rewrite LOG.rep_inner_hashmap_subset.
    or_r; cancel.
    auto.
    eauto.
    auto.
    intuition.

    step.
 
    prestep. norm.
    2: intuition idtac.
    cancel.
    intuition simpl; eauto.
    intuition simpl; eauto.
    intuition simpl; eauto.

    xcrash.

    eapply LOG.crash_xform_cached_before; eauto.

    xcrash.

    denote (SB.rep) as Hsb. rewrite SB.rep_magic_number in Hsb. destruct_lift Hsb.

    step.

    xcrash.
    unfold LOG.before_crash.
    denote or as Hor; apply sep_star_or_distr in Hor.
    destruct Hor as [ Hor | Hor ];
    rewrite LOG.rep_inner_hashmap_subset in Hor; eauto.

    rewrite LOG.rep_inner_notxn_pimpl in Hor.
    destruct_lift Hor.
    norm. cancel.
    intuition.
    pred_apply.
    safecancel.

    rewrite LOG.rep_inner_rollbacktxn_pimpl in Hor.
    norm. cancel.
    intuition.
    pred_apply.
    safecancel.

    xcrash.
    unfold LOG.before_crash.
    denote or as Hor; apply sep_star_or_distr in Hor.
    destruct Hor as [ Hor | Hor ];
    rewrite LOG.rep_inner_hashmap_subset in Hor; eauto.

    rewrite LOG.rep_inner_notxn_pimpl in Hor.
    destruct_lift Hor.
    norm. cancel.
    intuition.
    pred_apply.
    safecancel.

    rewrite LOG.rep_inner_rollbacktxn_pimpl in Hor.
    norm. cancel.
    intuition.
    pred_apply.
    safecancel.
    Unshelve. all: eauto.
  Qed.
  Proof.
    unfold file_get_attr; intros.
    step.
    safestep.
    safestep.
    eassumption.
    eapply pimpl_ok2; monad_simpl.
    apply LOG.commit_ro_ok.
    cancel.
    step.
    step.
    cancel.
    subst; pimpl_crash; cancel.
    rewrite LOG.notxn_intact. rewrite LOG.intact_idempred. reflexivity.
    rewrite LOG.intact_idempred.
    pimpl_crash; cancel.
    pimpl_crash. norml. clear H. safecancel.
    rewrite LOG.notxn_intact. rewrite LOG.intact_idempred. reflexivity.
    Unshelve. all: exact tt.
  Qed.
  Proof.
    unfold file_get_sz; intros.
    step.
    step.
    step.
    step.
    Unshelve. all: exact tt.
  Qed.
  Proof.
    unfold read_fblock; intros.
    step.
    safestep.
    safestep.
    all: try eassumption.
    eapply pimpl_ok2; monad_simpl.
    apply LOG.commit_ro_ok.
    cancel.
    step.
    step.
    pimpl_crash; cancel.
    rewrite LOG.notxn_intact.
    apply LOG.intact_idempred.
    pimpl_crash; cancel.
    apply LOG.intact_idempred.
    pimpl_crash. norml. clear H. cancel.
    apply LOG.notxn_idempred.
    Unshelve. all: exact tt.
  Qed.
  Proof.
    unfold file_set_attr; intros.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    or_l; cancel.
    unfold BFILE.mscs_same_except_log; intuition.
    xcrash_solve.
    xcrash_solve.
    {
      rewrite LOG.recover_any_idempred; cancel.
      or_r; cancel.
      xform_norm; cancel.
      xform_norm; cancel.
      xform_norm; cancel.
      xform_norm; cancel.
      xform_norm; safecancel.
      2: reflexivity.
      eauto.
    }
    xcrash_solve.
    rewrite LOG.intact_idempred. xform_norm. cancel.
    xcrash_solve.
    rewrite LOG.intact_idempred. xform_norm. cancel.
  Qed.
  Proof.
    unfold file_truncate; intros.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    xcrash_solve.
    {
      or_r; cancel.
      rewrite LOG.recover_any_idempred.
      xform_normr.
      safecancel.
      eauto.
    }
    step.
    step.
    xcrash_solve.
    rewrite LOG.intact_idempred. xform_norm. cancel.
    xcrash_solve.
    rewrite LOG.intact_idempred. xform_norm. cancel.
    xcrash_solve.
    rewrite LOG.intact_idempred. xform_norm. cancel.
  Unshelve.
    all: easy.
  Qed.
  Proof.
    unfold update_fblock_d; intros.
    step.
    step.
    prestep.
    (* extract dset_match from (rep ds), this is useful for proving crash condition *)
    rewrite LOG.active_dset_match_pimpl at 1.
    norm. cancel.
    xcrash_solve.
    intuition.
    latest_rewrite.
    pred_apply; cancel.
    eauto.
    eauto.
    safestep.
    step.
    step.
    xcrash_solve.

    - xform_normr; cancel.
      or_r; xform_normr; cancel.
      apply LOG.notxn_idempred.
      eauto.

    - cancel.
      repeat xcrash_rewrite.
      xform_norm.
      rewrite LOG.recover_any_idempred.
      or_l; cancel.
      rewrite LOG.recover_any_idempred.
      or_r; cancel; xform_normr; cancel.

    - cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel.
      rewrite LOG.notxn_intact, LOG.intact_idempred.
      xform_normr; cancel.
    Unshelve.
      all: easy.
  Qed.
  Proof.
    unfold file_sync; intros.
    step.
    step.
    prestep; norm. cancel. intuition.
    latest_rewrite.
    pred_apply; cancel.
    eauto.
    step.
    step.
    step.
    - xcrash_solve.
      rewrite <- crash_xform_idem.
      rewrite LOG.crash_xform_intact_dssync_vecs_idempred.
      rewrite SB.crash_xform_rep.
      xcrash.
    - xcrash_solve.
      rewrite LOG.recover_any_idempred.
      xcrash.
    - xcrash_solve.
      rewrite LOG.intact_idempred.
      xcrash.
    Unshelve.
      all: constructor.
  Qed.
  Proof.
    unfold tree_sync; intros.
    step.
    step using auto.
    step.
    step.
    xcrash_solve.
    rewrite LOG.recover_any_idempred.
    cancel.
  Unshelve.
    all: constructor.
  Qed.
  Proof.
    unfold tree_sync_noop; intros.
    step.
    step.
    xcrash_solve.
    rewrite LOG.recover_any_idempred.
    cancel.
  Qed.
  Proof.
    unfold lookup; intros.
    step.
    step.
    (* `step` here is really slow *)
    prestep. cancel.
    eapply pimpl_ok2; monad_simpl.
    apply LOG.commit_ro_ok.
    cancel.
    step.
    step.
    subst; pimpl_crash; cancel.
    apply LOG.notxn_idempred.
    step.
    step.
    cancel. apply LOG.notxn_idempred.
    cancel. apply LOG.intact_idempred.
    cancel. apply LOG.notxn_idempred.
  Unshelve.
    all: constructor.
  Qed.
  Proof.
    unfold create; intros.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    xcrash_solve.
    or_r; cancel.
    repeat (cancel; progress xform_norm).
    safecancel.
    2: reflexivity. cancel.
    rewrite LOG.recover_any_idempred; cancel.
    pred_apply; cancel.
    auto.
    auto.
    step.
    step.
    xcrash_solve. xform_norm. or_l. rewrite LOG.intact_idempred. cancel.
    xcrash_solve. xform_norm. or_l. rewrite LOG.intact_idempred. cancel.
    xcrash_solve. xform_norm. or_l. rewrite LOG.intact_idempred. cancel.
  Unshelve.
    all: constructor.
  Qed.
  Proof.
    unfold rename, rename_rep, rename_rep_inner; intros.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    xcrash. or_r. cancel.
    repeat (cancel; progress xform_norm).
    safecancel.
    rewrite LOG.recover_any_idempred. cancel.
    2: pred_apply; cancel.
    all: eauto.
    step.
    step.
    xcrash. or_l. rewrite LOG.notxn_idempred. cancel.
    xcrash. or_l. rewrite LOG.intact_idempred. cancel.
    xcrash. or_l. rewrite LOG.notxn_idempred. cancel.
  Unshelve.
    all: constructor.
  Qed.
  Proof.
    unfold delete; intros.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    xcrash. or_r.
    repeat (cancel; progress xform_norm).
    safecancel. rewrite LOG.recover_any_idempred. cancel.
    3: pred_apply; cancel.
    all: eauto.
    step.
    step.
    xcrash. or_l. rewrite LOG.notxn_idempred. cancel.
    xcrash. or_l. rewrite LOG.intact_idempred. cancel.
    xcrash. or_l. rewrite LOG.notxn_idempred. cancel.
  Unshelve.
    all: constructor.
  Qed.