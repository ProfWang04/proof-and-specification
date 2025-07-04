   Proof.
    intros.
  split; eauto.
  split; simpl.
  unfold tree_graft.
  apply tree_names_distinct_update_subtree.
  eapply tree_names_distinct_d_in; eauto; apply latest_in_ds.
  simpl.
  apply TND_dir.
  rewrite Forall_forall; intros dt Hx.
  apply in_map_iff in Hx.
  split_hypothesis.
  apply in_add_to_list_tree_or in H4.
  destruct H4.
  rewrite H4 in H3; rewrite <- H3; simpl; apply TND_file.
  
  eapply treeseq_pred_tree_rep_latest in H as Hz; destruct Hz.
  rewrite H0 in H5.
  inversion H5.
  rewrite <- H3.
  rewrite Forall_forall in H9.
  apply H9.
  apply in_map; auto.
  
  apply NoDup_add_to_list.
   eapply treeseq_pred_tree_rep_latest in H as Hz; destruct Hz.
  rewrite H0 in H3.
  inversion H3.
  auto.

  eapply find_subtree_none_In.
  rewrite <- H0.
  eapply dir2flatmem2_find_subtree_ptsto_none.
  eapply tree_names_distinct_d_in; eauto; apply latest_in_ds.
  pred_apply; cancel.

  split.
  eapply treerep_synced_dirfile; eauto.
  left; eexists; unfold tree_with_tmp; pred_apply; cancel.
  simpl; apply Forall_nil.
  Qed.
Proof.
  unfold atomic_cp; prestep.
  unfold pimpl; intros m' Hx; destruct_lift Hx.
  eapply tree_with_src_the_dnum in H9 as Hy; eauto.
  destruct Hy.
  unfold tree_with_src in H9; destruct H9.
  pred_apply; norm.
  unfold stars; cancel.
  intuition; eauto.
  eapply treeseq_in_ds_tree_pred_latest; eauto.
  instantiate (2:= []); simpl; eauto.
  
  prestep.
  norm.
  inversion H16.
  inversion H16.
  
  unfold stars.
  simpl.
  cancel.
  eexists; eauto.
  intuition; eauto.
  eapply treeseq_in_ds_pushd.
  eauto.
  unfold tree_rep_latest.
  instantiate (1:= {| TStree:= (tree_graft the_dnum x [] temp_fn 
                                (TreeFile a0 dirfile0) (TStree dummy3 !!));
                      TSilist:= ilist';
                      TSfree:= (frees'_1, frees'_2) |}).
  simpl; auto.
  eauto.
  unfold treeseq_one_safe; simpl.
  rewrite <- H5; eauto.
  eauto.

  prestep.
  norm.
  unfold stars; cancel.
  split.
  split.
  split; auto.
  split; auto.
  split; eauto.
  split.
  2: instantiate (2:= dirfile0).
  split.
  split; eauto.
  intuition; eauto.
  
  unfold latest; simpl.
  split; eauto.
  apply treeseq_safe_refl.
  simpl; apply Forall_nil.
  
  inversion H14; inversion H0. 
  eapply treeseq_tree_rep_sync_after_create; eauto.
  pred_apply; cancel.

  inversion H16.
  replace ([temp_fn]) with (([]: list string)++[temp_fn])%list by auto.
  eapply dirents2mem2_graft_file_none; simpl; eauto.
  eapply tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  pred_apply; cancel.
  
  inversion H14.
  unfold tree_with_tmp; simpl.
  replace ([temp_fn]) with (([]: list string)++[temp_fn])%list by auto.
  eexists.
  apply sep_star_assoc.
  apply sep_star_comm.
  apply sep_star_assoc.
  apply sep_star_comm.
  eapply dirents2mem2_graft_file_none; simpl; eauto.
  eapply tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  pred_apply; cancel.
  simpl; auto.
  unfold dirfile0; simpl; length_rewrite_l.
  
  step.
  unfold pimpl; intros.
  eapply H2.
  instantiate (1:= realcrash).
  intros m0 Hx; apply H15 in Hx; pred_apply; xcrash.
  or_l; xcrash; eauto.
  eauto.
  or_r; xcrash; eauto.
  rewrite H25 in H24; eauto.
  pred_apply; cancel; eauto.
  
  unfold pimpl; intros.
  eapply H2.
  instantiate (1:= realcrash).
  intros m0 Hx; apply H13 in Hx; pred_apply; xcrash.
  or_r; xcrash.
  eapply treeseq_in_ds_pushd.
  eauto.
  unfold tree_rep_latest.
  instantiate (2:= {| TStree:= (tree_graft the_dnum x [] temp_fn 
                                (TreeFile a0 dirfile0) (TStree dummy3 !!));
                      TSilist:= ilist';
                      TSfree:= (frees'_1, frees'_2) |}).
  simpl; eauto.
  unfold treeseq_one_safe; simpl.
  rewrite <- H5; eauto.
  eauto.
  eapply treeseq_tree_rep_sync_after_create; eauto.
  pred_apply; cancel.
  eauto.
  replace ([temp_fn]) with (([]: list string)++[temp_fn])%list by auto.
  eapply dirents2mem2_graft_file_none; simpl; eauto.
  eapply tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  rewrite H19; auto.
  pred_apply; cancel.
  eauto.
  pred_apply; cancel.

  norm.
  unfold stars; cancel.
  or_l; cancel.
  or_l; cancel; eauto.
  unfold tree_with_src; pred_apply; cancel.
  intuition.
  
  unfold stars.
  simpl.
  cancel.
  eexists; eauto.
  intuition.
  
  eapply H2.
  instantiate (1:= realcrash).
  intros m0 Hx; apply H5 in Hx; pred_apply; xcrash.
  eapply crash_ts_split'; eauto.
  or_r; xcrash; eauto.
  
  eapply treeseq_in_ds_pushd.
  eauto.
  unfold tree_rep_latest; simpl.
  instantiate (2:= {| TStree:= (tree_graft the_dnum x [] temp_fn 
                                (TreeFile x2 dirfile0) (TStree dummy3 !!));
                    TSilist:= x4;
                    TSfree:= (x5_1, x5_2) |}).
  simpl; eauto.
  unfold treeseq_one_safe; simpl; eauto.
  rewrite <- H16; auto.
  auto.
  eapply treeseq_tree_rep_sync_after_create; eauto.
  pred_apply; cancel.
  eauto.
  replace ([temp_fn]) with (([]: list string)++[temp_fn])%list by auto.
  eapply dirents2mem2_graft_file_none; simpl; eauto.
  eapply tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  rewrite H15; auto.
  pred_apply; cancel.
  eauto.
  Unshelve.
  all: repeat constructor.
  all: apply any.
Qed.