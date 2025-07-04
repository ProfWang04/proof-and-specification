Proof.
  unfold file_crash; intros.
  repeat deex.
  do 2 eexists.
  eapply file_crash_trans; eauto.
Qed.
Proof.
  unfold possible_fmem_crash; intros.
  specialize (H a).
  specialize (H0 a).
  intuition;
  try solve [repeat deex; congruence].
  repeat deex.
  rewrite H0 in H1; inversion H1; subst; clear H1.
  right; do 2 eexists; repeat split; eauto.
  eapply BFileCrash.file_crash_trans; eauto.
Qed.
Proof.
  unfold flist_crash_xform; unfold pimpl; simpl; intros.
  repeat deex; intuition.
  exists mf'0; split; auto.
  eapply possible_fmem_crash_trans; eauto.
Qed.
Proof.  
  intros ds ts.
  destruct ds, ts.
  generalize dependent l0.
  induction l; simpl.
  intro l1; destruct l1.
  
  {
    unfold treeseq_in_ds, latest, NEforall2, TREESEQ.tree_rep, tree_rep_latest, rep; simpl; intros.
    intuition.
    destruct_lift H0.
    rewrite crash_xform_idem in H.
    destruct_lift H.
    rewrite flist_crash_xform_idem in H4.
    do 2 eexists; eauto.
    pred_apply; cancel.

    rewrite crash_xform_idem in H1.
    destruct_lift H1.
    rewrite flist_crash_xform_idem in H4.
    pred_apply; cancel.
  }
  
  {
    unfold treeseq_in_ds, latest, NEforall2; simpl; intros; intuition; inversion H2.
  }
  
  {
    intro l0; destruct l0.
    {
       unfold treeseq_in_ds, latest, NEforall2; simpl; intros; intuition; inversion H2.
    }
    
    unfold treeseq_in_ds, latest; simpl; intros.
    split.
    split; simpl.
    - destruct H.
      destruct H; simpl in *.
      intuition.
      
      unfold TREESEQ.tree_rep, tree_rep_latest, rep in *; simpl in *.
      destruct_lift H2.
      rewrite crash_xform_idem in H.
      rewrite flist_crash_xform_idem in H4.
      pred_apply; cancel.
    - destruct H.
      destruct H; simpl in *.
      induction H1.
      auto.
      apply Forall2_cons; auto.
      intuition.
      unfold TREESEQ.tree_rep, tree_rep_latest, rep in *; simpl in *.
      destruct_lift H.
      rewrite crash_xform_idem in H.
      rewrite flist_crash_xform_idem in H6.
      pred_apply; cancel.
    
    - destruct H.
      unfold tree_rep_latest, rep in *; simpl in *.
      rewrite crash_xform_idem in H0.
      destruct_lift H0.
      rewrite flist_crash_xform_idem in H2.
      pred_apply; cancel.
  }
Qed.
Proof.
  induction 1; auto; intros.
  destruct f3; try constructor; try solve [
  inversion H0; subst;
  inversion H].
  inversion H0; subst.
  constructor.
  eapply file_crash_trans; eauto.
Qed.
Proof.
  unfold possible_flatmem_crash; intros.
  specialize (H a).
  specialize (H0 a).
  intuition;
  try solve [repeat deex; congruence].
  repeat deex.
  rewrite H0 in H1; inversion H1; subst; clear H1.
  right; do 2 eexists; repeat split; eauto.
  eapply flatmem_entry_crash_trans; eauto.
Qed.
Proof.
  unfold flatmem_crash_xform; unfold pimpl; intuition.
  repeat deex.
  eexists; split; eauto.
  eapply possible_flatmem_crash_trans; eauto.
Qed.
Proof.
  intros; destruct ts, l; simpl in *.
  
  -
  unfold treeseq_pred, NEforall, tree_rep_recover in *; simpl in *.
  intuition.
  unfold tree_with_src in *.
  destruct_lift H2.
  rewrite flatmem_crash_xform_idem in H2.
  left; pred_apply; cancel.
  apply Forall_nil.
  unfold tree_with_dst in *.
  destruct_lift H2.
  rewrite flatmem_crash_xform_idem in H2.
  right; pred_apply; cancel.
  apply Forall_nil.
  
  -
   unfold treeseq_pred, tree_rep_recover in *; simpl in *.
   inversion H; subst; simpl in *; clear H.
   intuition.
   split; simpl.
   repeat (split; auto).
   unfold tree_with_src in *.
   destruct_lift H2.
   rewrite flatmem_crash_xform_idem in H2.
   left; pred_apply; cancel.
   induction H1.
   apply Forall_nil.
   apply Forall_cons; auto.
   intuition.
   unfold tree_with_src in *.
   destruct_lift H5.
   rewrite flatmem_crash_xform_idem in H5.
   left; pred_apply; cancel.
   unfold tree_with_dst in *.
   destruct_lift H5.
   rewrite flatmem_crash_xform_idem in H5.
   right; pred_apply; cancel.
   
   split; simpl.
   repeat (split; auto).
   unfold tree_with_dst in *.
   destruct_lift H2.
   rewrite flatmem_crash_xform_idem in H2.
   right; pred_apply; cancel.
   induction H1.
   apply Forall_nil.
   apply Forall_cons; auto.
   intuition.
   unfold tree_with_src in *.
   destruct_lift H5.
   rewrite flatmem_crash_xform_idem in H5.
   left; pred_apply; cancel.
   unfold tree_with_dst in *.
   destruct_lift H5.
   rewrite flatmem_crash_xform_idem in H5.
   right; pred_apply; cancel.
Qed.
Proof.
  intros; destruct ts, l; simpl in *.
  
  -
  unfold treeseq_pred, NEforall, tree_rep in *; simpl in *.
  intuition.
  unfold tree_with_tmp in *.
  deex.
  destruct_lift H2.
  rewrite flatmem_crash_xform_idem in H2.
  left; pred_apply; cancel.
  apply Forall_nil.
  unfold tree_with_src in *.
  destruct_lift H3.
  rewrite flatmem_crash_xform_idem in H2.
  right; left; pred_apply; cancel.
  apply Forall_nil.
  unfold tree_with_dst in *.
  destruct_lift H3.
  rewrite flatmem_crash_xform_idem in H2.
  right; right; pred_apply; cancel.
  apply Forall_nil.
  
  -
   unfold treeseq_pred, tree_rep in *; simpl in *.
   inversion H; subst; simpl in *; clear H.
   intuition.
   split; simpl.
   repeat (split; auto).
   unfold tree_with_tmp in *.
   deex; destruct_lift H2.
   rewrite flatmem_crash_xform_idem in H2.
   left; pred_apply; cancel.
   induction H1.
   apply Forall_nil.
   apply Forall_cons; auto.
   intuition.
   unfold tree_with_tmp in *.
  deex.
  destruct_lift H5.
  rewrite flatmem_crash_xform_idem in H5.
  left; pred_apply; cancel.
  unfold tree_with_src in *.
  destruct_lift H6.
  rewrite flatmem_crash_xform_idem in H5.
  right; left; pred_apply; cancel.
  unfold tree_with_dst in *.
  destruct_lift H6.
  rewrite flatmem_crash_xform_idem in H5.
  right; right; pred_apply; cancel.
   
   split; simpl.
   repeat (split; auto).
   unfold tree_with_src in *.
   destruct_lift H3.
   rewrite flatmem_crash_xform_idem in H2.
   right; left; pred_apply; cancel.
   induction H1.
   apply Forall_nil.
   apply Forall_cons; auto.
   intuition.
   unfold tree_with_tmp in *.
  deex.
  destruct_lift H5.
  rewrite flatmem_crash_xform_idem in H5.
  left; pred_apply; cancel.
  unfold tree_with_src in *.
  destruct_lift H6.
  rewrite flatmem_crash_xform_idem in H5.
  right; left; pred_apply; cancel.
  unfold tree_with_dst in *.
  destruct_lift H6.
  rewrite flatmem_crash_xform_idem in H5.
  right; right; pred_apply; cancel.
   
   split; simpl.
   repeat (split; auto).
   unfold tree_with_dst in *.
   destruct_lift H3.
   rewrite flatmem_crash_xform_idem in H2.
   right; right; pred_apply; cancel.
   induction H1.
   apply Forall_nil.
   apply Forall_cons; auto.
   intuition.
   unfold tree_with_tmp in *.
  deex.
  destruct_lift H5.
  rewrite flatmem_crash_xform_idem in H5.
  left; pred_apply; cancel.
  unfold tree_with_src in *.
  destruct_lift H6.
  rewrite flatmem_crash_xform_idem in H5.
  right; left; pred_apply; cancel.
  unfold tree_with_dst in *.
  destruct_lift H6.
  rewrite flatmem_crash_xform_idem in H5.
  right; right; pred_apply; cancel.
Qed.
Proof.
  unfold corr2; intros.
  specialize (H1 vm hm done crash).
  apply H1 in H2.
  apply pimpl_or_apply in H2.
  intuition.
  eapply H; eauto.
  eapply H0; eauto.
Qed.
Proof.
  intros.
  eapply pimpl_or2.
  apply atomic_cp_recover_ok_1.
  apply atomic_cp_recover_ok_2.
  unfold pimpl; intros.
  destruct_lift H.
  apply sep_star_or_distr in H.
  apply pimpl_or_apply in H.
  destruct H.
  pred_apply; or_l; cancel.
  all: eauto.
  eapply pimpl_ok2.
  apply H3.
  intros; cancel.
  or_l; cancel.
  or_r; cancel.
  rewrite sep_star_or_distr; or_l; cancel; eauto.
  all: eauto.
  
  unfold pimpl; intros.
  eapply H2.
  intros m2 Hp; apply H0 in Hp.
  pred_apply; xcrash.
  or_r. or_r. xcrash.
  or_l; cancel; eauto.
  all: eauto.
  destruct_lift H5; pred_apply; cancel.
  
  pred_apply; or_r; cancel.
  all: eauto.
  unfold pimpl; intros.
  eapply H2.
  intros m2 Hp; apply H0 in Hp.
  pred_apply; xcrash.
  or_r. or_r. xcrash.
  or_l; cancel; eauto.
  all: eauto.
  or_r. or_r. xcrash.
  or_r; cancel; eauto.
  all: eauto.
  destruct_lift H1; pred_apply; cancel.
Qed.
  Proof.
    unfold forall_helper; intros.
    eapply pimpl_ok3; intros.
    eapply corr3_from_corr2_rx.
    apply atomic_cp_ok.
    apply atomic_cp_recover_ok.
    
    cancel; eauto.
    specialize (H2 (a, (a0, b0))); simpl in H2; auto.
    eapply pimpl_ok2; eauto.
    simpl; cancel; eauto.
    or_l; cancel; eauto.
    or_l; cancel; eauto.
    or_l; cancel; eauto.
    or_r; cancel; eauto.
    or_r; cancel; eauto.
    
    instantiate
    (1:= fun hm' => (exists c, F_ * c * 
      [[ crash_xform (F_ * c) =p=> 
        F_ * crash_xform (
        exists mscs ds sm t ts dfile tinum'' tinum',
          (LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' *
          [[ treeseq_in_ds v v0 fsxp sm mscs ts ds ]] *
          [[ treeseq_pred (tree_rep v1 v5 [temp_fn] srcinum v6
             tinum'' dstbase dstname v8) ts ]])
           \/
          (LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' *
          [[ treeseq_in_ds v v0 fsxp sm mscs (pushd t ts) ds ]] *
          [[ tree_rep v1 v5 [temp_fn] srcinum v6 tinum' dstbase dstname dfile t ]] *
          [[ treeseq_pred (tree_rep v1 v5 [temp_fn] srcinum v6
             tinum'' dstbase dstname v8) ts ]])
          \/
          (exists dstfile',
          LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' *
          [[ treeseq_in_ds (crash_xform v) (BFileCrash.flist_crash_xform v0)
              fsxp sm mscs ts ds ]] *
          [[ treeseq_pred (tree_rep (flatmem_crash_xform v1) v5 
              [temp_fn] srcinum v6 tinum'' dstbase dstname dstfile') ts ]] *
          ([[ file_crash dfile dstfile' ]] \/ [[ file_crash v8 dstfile' ]])))]])%pred); simpl.

    cancel; eauto.
    rewrite crash_xform_sep_star_dist; rewrite H3.
    cancel; eauto.
    xcrash.
    or_l; cancel; eauto.
    or_r; or_l; cancel; eauto.

    unfold pimpl; intros.
    apply crash_xform_sep_star_dist in H. 
    rewrite crash_xform_lift_empty in H.
    rewrite crash_xform_exists_comm in H; destruct_lift H.
    apply crash_xform_sep_star_dist in H.
    rewrite crash_xform_lift_empty in H.
    destruct_lift H.
    specialize (H13 _ H) as Hx.
    repeat (rewrite crash_xform_exists_comm in Hx; destruct_lift Hx).
    repeat (rewrite crash_xform_exists_comm in H0; destruct_lift H0).
    rewrite crash_xform_or_dist in H0.
    apply sep_star_or_distr in H0; apply pimpl_or_apply in H0; destruct H0.
    
    -
    repeat (rewrite crash_xform_sep_star_dist in H0;
        rewrite crash_xform_lift_empty in H0;
        destruct_lift H0).
    rewrite LOG.idempred_idem in H0.
    destruct_lift H0.
    rewrite SB.crash_xform_rep in H0.
    
    repeat eexists.
    repeat rewrite <- sep_star_assoc.
    repeat apply sep_star_lift_apply'; intros; eauto.
    pred_apply; cancel.
    or_l; cancel; eauto.

    specialize (H1 r_).
    eapply pimpl_ok2; eauto.
    simpl; cancel; eauto.
    or_l; cancel; eauto.
    or_r; cancel; eauto.
    or_r; cancel; eauto.
    
    eexists.
    apply sep_star_lift_apply'.
    destruct_lift H14; eauto.
    intros.
    apply crash_xform_sep_star_dist in H15.
    rewrite H3 in H15.
    pred_apply; cancel.
    unfold pimpl; intros m2 Hp; apply H5 in Hp; pred_apply; cancel.
    rewrite crash_xform_or_dist; cancel.
    xcrash.
    or_l; cancel; eauto.
    xcrash.
    or_r; or_l; cancel; eauto.
    or_r; or_r; xcrash; eauto.
    or_l; cancel; eauto.
    or_r; or_r; xcrash; eauto.
    or_r; cancel; eauto.
    
    -
    rewrite crash_xform_or_dist in H0.
    apply sep_star_or_distr in H0; apply pimpl_or_apply in H0; destruct H0.
    
    +
    repeat (rewrite crash_xform_sep_star_dist in H0;
        rewrite crash_xform_lift_empty in H0;
        destruct_lift H0).
    rewrite LOG.idempred_idem in H0.
    destruct_lift H0.
    rewrite SB.crash_xform_rep in H0.

    repeat eexists.
    repeat rewrite <- sep_star_assoc.
    repeat apply sep_star_lift_apply'; intros; eauto.
    pred_apply; cancel.
    or_r; cancel; eauto.
    
    specialize (H1 r_).
    eapply pimpl_ok2; eauto.
    simpl; cancel; eauto.
    or_l; cancel; eauto.
    or_r; cancel; eauto.
    or_r; cancel; eauto.
    
    eexists.
    apply sep_star_lift_apply'.
    destruct_lift H14; eauto.
    intros.
    apply crash_xform_sep_star_dist in H15.
    rewrite H3 in H15.
    pred_apply; cancel.
    unfold pimpl; intros m2 Hp; apply H5 in Hp; pred_apply; cancel.
    rewrite crash_xform_or_dist; cancel.
    xcrash.
    or_l; cancel; eauto.
    xcrash.
    or_r; or_l; cancel; eauto.
    or_r; or_r; xcrash; eauto.
    or_l; cancel; eauto.

    instantiate (1:= dummy5).
    or_r; or_r; xcrash; eauto.
    or_l; cancel; eauto.


    +
    repeat (rewrite crash_xform_exists_comm in H0; destruct_lift H0).
    rewrite crash_xform_sep_star_dist in H0.
    rewrite crash_xform_or_dist in H0;
    repeat rewrite crash_xform_lift_empty in H0;
    destruct_lift H0.
    repeat (rewrite crash_xform_sep_star_dist in H0;
        rewrite crash_xform_lift_empty in H0;
        destruct_lift H0).
    apply sep_star_or_distr in H0; apply pimpl_or_apply in H0; destruct H0; destruct_lift H0.
    
    *
    rewrite LOG.idempred_idem in H0.
    destruct_lift H0.
    rewrite SB.crash_xform_rep in H0.
    
    repeat eexists.
    repeat rewrite <- sep_star_assoc.
    repeat apply sep_star_lift_apply'; intros; eauto.
    pred_apply; cancel.
    or_l; cancel; eauto.

    specialize (H1 r_).
    eapply pimpl_ok2; eauto.
    simpl; cancel; eauto.
    or_l; cancel; eauto.
    or_r; cancel; eauto.
    apply treeseq_in_ds_crash_idem; eauto.
    apply treeseq_pred_tree_rep_recover_idem; eauto.
    or_r; cancel; eauto.
    apply treeseq_in_ds_crash_idem; eauto.
    apply treeseq_pred_tree_rep_recover_idem; eauto.
    
    eexists.
    apply sep_star_lift_apply'.
    destruct_lift H14; eauto.
    intros.
    apply crash_xform_sep_star_dist in H16.
    rewrite H3 in H16.
    pred_apply; cancel.
    unfold pimpl; intros m2 Hp; apply H5 in Hp; pred_apply; cancel.
    rewrite crash_xform_or_dist; cancel.
    xcrash.
    instantiate (1:= dummy5).
    or_r; or_r; xcrash; eauto.
    or_l; cancel; eauto.
    
    xcrash.
    instantiate (1:= dummy5).
    or_r; or_r; xcrash; eauto.
    or_l; cancel; eauto.
    eapply treeseq_pred_pushd; eauto.
    
    instantiate (1:= dummy8).
    apply treeseq_in_ds_crash_idem in H22; eauto.
    apply treeseq_pred_tree_rep_idem in H21; eauto.
    or_r; or_r; xcrash; eauto.
    or_l; xcrash.
    
    instantiate (1:= dummy8).
    apply treeseq_in_ds_crash_idem in H22; eauto.
    apply treeseq_pred_tree_rep_idem in H21; eauto.
    or_r; or_r; xcrash; eauto.
    or_l; xcrash.
    
    *
    rewrite LOG.idempred_idem in H0.
    destruct_lift H0.
    rewrite SB.crash_xform_rep in H0.
    
    repeat eexists.
    repeat rewrite <- sep_star_assoc.
    repeat apply sep_star_lift_apply'; intros; eauto.
    pred_apply; cancel.
    or_l; cancel; eauto.

    specialize (H1 r_).
    eapply pimpl_ok2; eauto.
    simpl; cancel; eauto.
    or_l; cancel; eauto.
    or_r; cancel; eauto.
    apply treeseq_in_ds_crash_idem; eauto.
    apply treeseq_pred_tree_rep_recover_idem; eauto.
    or_r; cancel; eauto.
    apply treeseq_in_ds_crash_idem; eauto.
    apply treeseq_pred_tree_rep_recover_idem; eauto.
    
    eexists.
    apply sep_star_lift_apply'.
    destruct_lift H14; eauto.
    intros.
    apply crash_xform_sep_star_dist in H16.
    rewrite H3 in H16.
    pred_apply; cancel.
    unfold pimpl; intros m2 Hp; apply H5 in Hp; pred_apply; cancel.
    rewrite crash_xform_or_dist; cancel.
    xcrash.
    instantiate (1:= dummy5).
    or_r; or_r; xcrash; eauto.
    or_r; cancel; eauto.
    
    xcrash.
    instantiate (1:= dummy5).
    or_r; or_r; xcrash; eauto.
    or_r; cancel; eauto.
    eapply treeseq_pred_pushd; eauto.
    
    instantiate (1:= dummy8).
    apply treeseq_in_ds_crash_idem in H22; eauto.
    apply treeseq_pred_tree_rep_idem in H21; eauto.
    or_r; or_r; xcrash; eauto.
    or_l; xcrash.
    
    instantiate (1:= dummy8).
    apply treeseq_in_ds_crash_idem in H22; eauto.
    apply treeseq_pred_tree_rep_idem in H21; eauto.
    or_r; or_r; xcrash; eauto.
    or_l; xcrash.
    
    Unshelve.
    all: eauto.
    repeat econstructor; eauto.
Qed.