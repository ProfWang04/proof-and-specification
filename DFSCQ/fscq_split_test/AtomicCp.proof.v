  Proof.
    intros.
    eapply dir2flatmem2_find_subtree_ptsto in H0 as Hfind; eauto.
    unfold treeseq_one_upd.
    destruct (find_subtree tmppath (TStree tree)).
    destruct d.
    inversion Hfind; subst; simpl.
    eapply dir2flatmem2_update_subtree; eauto.
    inversion Hfind.
    inversion Hfind.
  Qed.
  Proof.
    intros.
    unfold tree_with_tmp in *.
    destruct_lift H0. eexists.
    eapply pimpl_apply.
    2: eapply dirents2mem2_treeseq_one_upd_tmp; eauto.
    cancel.
    pred_apply; cancel.
  Qed.
  Proof.
    intros.
    eapply dir2flatmem2_find_subtree_ptsto in H1 as Hfind; eauto.
    eapply dir2flatmem2_find_subtree_ptsto_none in H0 as Hfindtmp; eauto.
    unfold treeseq_one_upd.
    intuition.
    destruct (find_subtree tmppath (TStree tree)).
    congruence.
    eassumption.
  Qed.
  Proof.
    intros.
    unfold tree_with_src in *.
    destruct_lift H0. eexists.
    eapply sep_star_assoc.
    eapply sep_star_comm.
    eapply sep_star_assoc_1.
    eapply dirents2mem2_treeseq_one_upd_src; eauto.
    pred_apply.
    cancel.
    pred_apply.
    cancel.
  Qed.
  Proof.
    intros.
    eapply d_in_nthd in H as Hin.
    destruct Hin.
    unfold tsupd in H0.
    rewrite d_map_nthd in H0.
    eexists (nthd x ts).
    split; eauto.
    eapply nthd_in_ds.
  Qed.
  Proof.
    intros.
    eapply NEforall_d_in in H as Hx.
    destruct Hx.
    apply H1.
    auto.
  Qed.
  Proof.
    intros.
    unfold treeseq_one_upd in H1.
    + destruct (find_subtree tmppath (TStree t)) eqn:D1.
      * destruct d eqn:D2.
        rewrite H1; simpl.
        eapply tree_names_distinct_update_subtree.
        eapply tree_names_distinct_d_in; eauto.
        apply TND_file.
        rewrite H1; eapply tree_names_distinct_d_in; eauto.
      * rewrite H1; eapply tree_names_distinct_d_in; eauto.
  Qed.
  Proof.
    intros.
    unfold treeseq_pred, tree_rep in *.
    intros.
    eapply NEforall_d_in'.
    intros.

    eapply tsupd_d_in_exists in H0.
    destruct H0.
    intuition.

    eapply tree_names_distinct_treeseq_one_upd; eauto.

    eapply NEforall_d_in in H as Hx.
    2: instantiate (1 := x0); eauto.
    intuition.
    eapply NEforall_d_in in H as Hx.
    2: instantiate (1 := x0); eauto.
    intuition.
    destruct H3.
    unfold tree_with_tmp in H3.
    rewrite H2.
    left.

    eexists {|
             DFData := (DFData x1) ⟦ Off0 := (fst v0, vsmerge t0) ⟧;
             DFAttr := DFAttr x1|}.
    eapply treeseq_one_upd_tree_rep_tmp; eauto.
    eauto.

    right. left.
    rewrite H2.
    eapply treeseq_one_upd_tree_rep_src; eauto.

    right. right.
    rewrite H2.
    eapply treeseq_one_upd_tree_rep_src; eauto.
  Qed.
  Proof.
    intros.
    eapply dir2flatmem2_find_subtree_ptsto in H0 as Hfind; eauto.
    unfold treeseq_one_file_sync.
    destruct (find_subtree tmppath (TStree tree)).
    destruct d.
    inversion Hfind; subst; simpl.
    eapply dir2flatmem2_update_subtree; eauto.
    inversion Hfind.
    inversion Hfind.
  Qed.
  Proof.
    intros.
    unfold tree_with_tmp in *.
    destruct_lift H0. eexists.
    eapply pimpl_apply.
    2: eapply dirents2mem2_treeseq_one_file_sync_tmp; eauto.
    cancel.
    pred_apply; cancel.
  Qed.
  Proof.
    intros.
    eapply d_in_nthd in H as Hin.
    destruct Hin.
    unfold ts_file_sync in H0.
    rewrite d_map_nthd in H0.
    eexists (nthd x ts).
    split; eauto.
    eapply nthd_in_ds.
  Qed.
  Proof.
    intros.
    eapply dir2flatmem2_find_subtree_ptsto in H1 as Hfind; eauto.
    eapply dir2flatmem2_find_subtree_ptsto_none in H0 as Hfindtmp; eauto.
    unfold treeseq_one_file_sync.
    intuition.
    destruct (find_subtree tmppath (TStree tree)).
    congruence.
    eassumption.
   Qed.
  Proof.
    intros.
    unfold tree_with_src in *.
    destruct_lift H0. eexists.
    eapply sep_star_assoc.
    eapply sep_star_comm.
    eapply sep_star_assoc_1.
    eapply dirents2mem2_treeseq_one_file_sync_src; eauto.
    pred_apply.
    cancel.
    pred_apply.
    cancel.
  Qed.
  Proof.
    intros.
    unfold treeseq_one_file_sync in H1.
    + destruct (find_subtree tmppath (TStree t)) eqn:D1.
      * destruct d eqn:D2.
        rewrite H1; simpl.
        eapply tree_names_distinct_update_subtree.
        eapply tree_names_distinct_d_in; eauto.
        apply TND_file.
        rewrite H1; eapply tree_names_distinct_d_in; eauto.
      * rewrite H1; eapply tree_names_distinct_d_in; eauto.
  Qed.
  Proof.
    intros.
    unfold treeseq_pred, tree_rep in *.
    intros.
    eapply NEforall_d_in'.
    intros.
    eapply tssync_d_in_exists in H0; eauto.
    destruct H0.
    intuition.
    eapply tree_names_distinct_treeseq_one_file_sync; eauto.
    eapply NEforall_d_in in H as Hx.
    2: instantiate (1 := x0); eauto.
    intuition.
    eapply NEforall_d_in in H as Hx.
    2: instantiate (1 := x0); eauto.
    intuition.
    destruct H3.
    unfold tree_with_tmp in H3.
    rewrite H2.
    left.
    eexists (synced_dirfile x1).
    eapply treeseq_one_file_sync_tree_rep_tmp; eauto.
    right. left.
    rewrite H2.
    eapply treeseq_one_file_sync_tree_rep_src; eauto.
    exact BFILE.bfile0.
    right. right.
    rewrite H2.
    eapply treeseq_one_file_sync_tree_rep_src; eauto.
    exact BFILE.bfile0.
  Qed.
  Proof.
    intros.
    rewrite synced_list_length. rewrite map_length.
    eapply ptsto_a_list2nmem_mem_eq in H. rewrite H.
    simpl; omega.
  Qed.
  Proof.
    intros.
    unfold treeseq_pred, NEforall in H.
    intuition.
    unfold tree_rep in H0.
    intuition.
  Qed.
   Proof.
    unfold copydata, tree_with_tmp; intros.
    step.
    eassign srcpath. cancel.
    prestep. norm. cancel.
    eassign srcpath. intuition eauto.
    pred_apply. cancel.
    pred_apply. cancel.
    step.
    2: eassign tmppath; cancel.
    msalloc_eq; eauto.
    pred_apply; cancel.
    step.
    denote! (forall _, treeseq_pred _ _ -> treeseq_pred _ _) as Ht.
    specialize (Ht tmppath).
    destruct Ht.
    msalloc_eq.
    eassumption.
    unfold treeseq_pred.
    unfold NEforall.
    split.
    msalloc_eq; eauto.
    msalloc_eq; eauto.
    step.

    safestep.
    2: eauto.
    or_l.
    cancel.
    eauto.

    eapply treeseq_tssync_tree_rep.
    eapply treeseq_upd_tree_rep.
    eauto.
    2: eauto.

    or_r.
    cancel.
    2: eauto.
    unfold synced_dirfile.
    erewrite ptsto_0_list2nmem_mem_eq with (d := (DFData file)) by eauto.
    erewrite ptsto_0_list2nmem_mem_eq with (d := (DFData f')) by eauto.
    cancel.

    eapply treeseq_pred_pushd.
    2: eapply treeseq_tssync_tree_rep.
    2: eapply treeseq_upd_tree_rep.
    2: eauto.

    unfold tree_rep; simpl; intuition; eauto.
    distinct_names.

    left.
    unfold tree_with_tmp.
    pred_apply.
    cancel.
    eauto.

    (* crashed during setattr  *)
    xcrash; eauto.
    eapply treeseq_tssync_tree_rep; eauto.
    eapply treeseq_upd_tree_rep; eauto.

    eapply treeseq_pred_pushd.
    2: eapply treeseq_tssync_tree_rep; eauto.
    2: eapply treeseq_upd_tree_rep; eauto.
    unfold tree_rep; intuition; eauto.
    distinct_names.

    left; unfold tree_with_tmp; simpl.
    pred_apply. cancel.
    eauto.

    (* crash during sync *)
    xcrash; eauto.
    eapply treeseq_upd_tree_rep; eauto.

    (* crash during upd *)
    xcrash; eauto.
    match goal with H: (_, _) = _ |- _ => rewrite H end.
    eapply treeseq_upd_tree_rep.
    eassumption.

    xcrash; eauto.

    xcrash; eauto.

  Grab Existential Variables.
    all: eauto.
    all: intros; exact True.
  Qed.
  Proof.
    unfold copy2temp, tree_with_tmp; intros.
    step.

    destruct a0.
    prestep. norm.
    inv_option_eq.
    inv_option_eq.

    cancel.
    intuition.
    eassumption.
    msalloc_eq. eauto.

    eapply treeseq_pred_pushd; eauto.
    unfold tree_rep; intuition; eauto.
    distinct_names.

    left; unfold tree_with_tmp; simpl.
    pred_apply. cancel.

    rewrite latest_pushd; simpl.
    unfold tree_with_tmp; pred_apply; cancel.

    eassumption.

    simpl.
    eapply pimpl_apply.
    2: apply list2nmem_array.
    rewrite arrayN_ptsto_selN_0.
    unfold Off0; cancel.
    rewrite setlen_length; omega.

    step.
    or_l. unfold tree_with_tmp in *; cancel.

    xcrash.

    step.

    xcrash.
    eassumption.
    eauto.
    eassumption.
    eapply treeseq_pred_pushd; eauto.
    unfold tree_rep; intuition; eauto.
    distinct_names.
    left; unfold tree_with_tmp; simpl.
    pred_apply. cancel.

  Grab Existential Variables.
    all: eauto.
  Qed.
  Proof.
    intros.
    unfold tree_with_tmp in H0.
    edestruct dir2flatmem2_find_subtree_ptsto_dir with 
      (tree := TStree ts !!) (fnlist := @nil string)
      (F := (exists dstinum : addr,
          (Ftree ✶ (srcpath |-> File srcinum file)
           ✶ tmppath |-> File tinum tfile)
          ✶ (dstbase ++ [dstname])%list |-> File dstinum dstfile)%pred).
    distinct_names'.
    pred_apply; cancel.
    eexists x; auto.
  Qed.
  Proof.
    intros.
    unfold tree_with_tmp in H0. 
    destruct H0.
    eexists (((Ftree ✶ [] |-> Dir the_dnum) ✶ srcpath |-> File srcinum file)%pred).
    eexists x.
    split.
    pred_apply. cancel.
    reflexivity.
  Qed.
  Proof.
    unfold copy_and_rename; intros.
    step.

    prestep. norml. 
    eapply tree_with_tmp_the_dnum in H15 as Hdnum; eauto. deex.
    cancel.

    eapply tree_with_tmp_the_dnum in H15 as Hdnum; eauto. deex.
    eapply tree_with_tmp_tmp_dst in H15 as Hdst; eauto. repeat deex.
    safecancel.
    eassign (@nil string). simpl. rewrite H14; eauto.
    pred_apply; cancel.

    step.
    step.

    or_r. unfold tree_with_dst.
    safecancel.
    erewrite <- treerep_synced_dirfile; eauto.

    unfold treeseq_pred, NEforall; simpl.
    intuition; eauto.
    2: apply Forall_nil.
    unfold tree_rep.
    intuition; eauto.
    distinct_names.
    right. right.
    pred_apply. unfold tree_with_dst.
    cancel.
    erewrite <- treerep_synced_dirfile; eauto.

    xcrash; eauto.
    eapply treeseq_pred_pushd; eauto.
    unfold tree_rep; intuition; simpl; eauto.
    distinct_names.
    right. right. 
    unfold tree_with_dst. pred_apply. cancel.
    erewrite <- treerep_synced_dirfile; eauto.

    step.
    or_l. cancel.
    unfold tree_with_tmp; cancel.
    eauto.

    unfold treeseq_pred, NEforall; simpl.
    intuition; eauto.
    2: apply Forall_nil.
    unfold tree_rep.
    intuition; eauto.
    distinct_names'.

    xcrash.
    eassumption. eauto.

    xcrash.
    eassumption. eauto.

    eassumption.
    eapply treeseq_pred_pushd; eauto.
    unfold tree_rep; intuition; simpl; eauto.
    distinct_names.
    right. right.
    unfold tree_with_dst. pred_apply; cancel.

    cancel.
    erewrite <- treerep_synced_dirfile; eauto.
    cancel.

    eassumption.
    step.
    unfold treeseq_pred, NEforall; simpl.
    intuition; eauto.
    2: apply Forall_nil.
    unfold tree_rep.
    intuition; eauto.
    distinct_names'.

    xcrash.
    eassumption. eauto.

    xcrash.
    eassumption. eauto.

  Grab Existential Variables.
    all: eauto.
  Qed.
  Proof.
    intros.
    eapply crash_xform_pimpl_proper in H0; [ | apply diskIs_pred; eassumption ].
    apply crash_xform_sep_star_dist in H0.
    rewrite xform_tree_rep in H0.
    destruct_lift H0.
    exists dummy.
    pred_apply.
    cancel.
  Qed.
  Proof.
    intros.
    unfold treeseq_in_ds in H.
    destruct H.
    eapply NEforall2_d_in in H.
    2: instantiate (1 := n).
    2: instantiate (1 := (nthd n ts)); eauto.
    2: instantiate (1 := (nthd n ds)); eauto.
    intuition.
    unfold TREESEQ.tree_rep in H2.
    repeat (denote exis as He; destruct He).
    eapply rep_tree_crash.
    instantiate (1 := (nthd n ds)).
    pred_apply.
    subst t.
    cancel.
    eassumption.
  Qed.
  Proof.
    intros.
    unfold treeseq_in_ds.
    constructor; simpl.
    split.
    unfold TREESEQ.tree_rep.
    intuition; simpl.
    pred_apply; safecancel.
    unfold treeseq_one_safe; simpl.
    eapply dirtree_safe_refl.
    constructor.
    unfold tree_rep_latest; simpl.
    pred_apply; cancel.

    replace ms with (BFILE.ms_empty (MSLL ms)).
    cancel.
    destruct ms.
    unfold ATOMICCP.MSLL.
    unfold BFILE.MSinitial in *.
    intuition. simpl in *. subst.
    unfold BFILE.ms_empty; simpl.
    reflexivity.
  Qed.
  Proof.
    intros.
    eapply find_name_exists in H.
    destruct H.
    intuition.
    unfold find_subtree in H0.
    inversion H0; eauto.
  Qed.
  Proof.
    intros.
    eapply find_name_exists in H.
    destruct H.
    intuition.
    unfold find_subtree in H0.
    inversion H0; eauto.
  Qed.
  Proof.
    intros.
    assert (exists d, find_subtree [] t = Some (TreeDir the_dnum d)).
    eapply dir2flatmem2_find_subtree_ptsto_dir; eauto.
    pred_apply; cancel.
    eauto.
  Qed.
  Proof.
    intros.
    eapply tree_rep_find_subtree_root in H0.
    destruct H0.
    unfold find_name.
    destruct (find_subtree [] t).
    destruct d; congruence.
    congruence.
    eauto.
  Qed.
  Proof.
    intros; subst t.
    unfold treeseq_in_ds in H; intuition.
    unfold treeseq_pred in H.
    eapply NEforall_d_in with (x := nthd n ts) in H.
    2: eapply nthd_in_ds.
    unfold tree_rep in H.
    intuition; eauto.

    destruct H2.
    unfold tree_with_tmp in *. 
    destruct H2.
    eapply tree_crash_find_subtree_root with (t := TStree (nthd n ts)); eauto.
    eapply tree_rep_find_subtree_root with (Ftree := Ftree); eauto.
    pred_apply; cancel.

    unfold tree_with_src in *. 
    destruct H3.
    eapply tree_crash_find_subtree_root with (t := TStree (nthd n ts)); eauto.
    eapply tree_rep_find_subtree_root with (Ftree := Ftree); eauto.
    pred_apply; cancel.

    unfold tree_with_dst in *. 
    destruct H3.
    eapply tree_crash_find_subtree_root with (t := TStree (nthd n ts)); eauto.
    eapply tree_rep_find_subtree_root with (Ftree := Ftree); eauto.
    pred_apply; cancel.
  Qed.
  Proof.
    intros; subst t.
    eapply tree_pred_crash_find_subtree_root in H; eauto.
    destruct H.
    unfold find_name.
    destruct (find_subtree [] t').
    destruct d.
    inversion H.
    inversion H; subst; eauto.
    inversion H.
  Qed.
  Proof.
    unfold treeseq_pred; intros.
    eapply NEforall_d_in in H; eauto.
  Qed.
  Proof.
    intros.
    eapply treeseq_pred_d_in; eauto.
    apply nthd_in_ds.
  Qed.
  Proof.
    unfold treeseq_pred, tree_rep; intros.
    eapply NEforall_impl; eauto; intros; simpl in *.
    intuition.
    - deex.
      pred_apply. cancel.
    - pred_apply; cancel.
    - pred_apply; cancel.
  Qed.
  Proof.
    intros.
    apply flatmem_crash_xform_or_dist in H.
    destruct H.
    pred_apply; cancel.
    exfalso.
    apply flatmem_crash_xform_or_dist in H.
    destruct H.
    - unfold tree_with_src in H.
      apply flatmem_crash_xform_exists in H; destruct_lift H.
      apply flatmem_crash_xform_sep_star in H.
      rewrite flatmem_crash_xform_sep_star in H.
      rewrite flatmem_crash_xform_nothing in H.
      unfold find_name in H0.
      erewrite dir2flatmem2_find_subtree_ptsto_none in H0; eauto.
      congruence.
      pred_apply; cancel.
    - unfold tree_with_dst in H.
      apply flatmem_crash_xform_exists in H; destruct_lift H.
      apply flatmem_crash_xform_sep_star in H.
      rewrite flatmem_crash_xform_sep_star in H.
      rewrite flatmem_crash_xform_nothing in H.
      unfold find_name in H0.
      erewrite dir2flatmem2_find_subtree_ptsto_none in H0; eauto.
      congruence.
      pred_apply; cancel.
  Qed.
  Proof.
    intros.
    apply flatmem_crash_xform_or_dist in H.
    destruct H.
    {
      exfalso.
      apply flatmem_crash_xform_exists in H. destruct_lift H.
      unfold tree_with_tmp in H.
      apply flatmem_crash_xform_exists in H. destruct_lift H.
      eapply pimpl_apply in H.
      2: repeat rewrite flatmem_crash_xform_sep_star.
      2: repeat rewrite flatmem_crash_xform_file.
      2: reflexivity.
      destruct_lift H.
      destruct_lift H.
      unfold find_name in H0.
      erewrite dir2flatmem2_find_subtree_ptsto in H0; eauto.
      congruence.
      pred_apply.
      cancel.
    }

    eauto.
  Qed.
Proof.
  induction tree; simpl in *; intros; auto.
  destruct a; simpl in *.
  destruct (string_dec s name); simpl in *.
  destruct H.
  left; auto.
  right; right; auto.
  destruct H.
  right; left; auto.
  apply IHtree in H.
  destruct H.
  left; auto.
  right; right; auto.
Qed.
Proof.
  induction tree; simpl in *; intros; auto.
  destruct H.
  left; auto.
  right; auto.
  destruct a; simpl in *.
  destruct (string_dec s name); simpl in *.
  destruct H.
  left; auto.
  right; right; auto.
  destruct H.
  right; left; auto.
  apply IHtree in H.
  destruct H.
  left; auto.
  right; right; auto.
Qed.
  Proof.
    intros.
    destruct ts; destruct l; unfold latest; simpl in *.
    destruct H; simpl in *.
    auto.
    destruct H; simpl in *.
    inversion H0; simpl in *; auto.
  Qed.
Proof.
  induction tree; intros.
  unfold add_to_list.
  apply NoDup_cons.
  apply in_nil.
  apply NoDup_nil.
  destruct a; simpl in *.
  destruct (string_dec s fname); simpl in *.
  destruct H0; left; auto.
  apply NoDup_cons.
  unfold not; intros.
  apply in_add_to_list_or in H1; auto.
  destruct H1.
  apply H0; left; auto.
  apply NoDup_cons_iff in H.
  apply H; auto.
  apply IHtree.
  apply NoDup_cons_iff in H.
  apply H; auto.
  unfold not; intros; apply H0.
  right; auto.
Qed.
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
  deex.
  apply in_add_to_list_tree_or in H5.
  destruct H5.
  rewrite H3; simpl; apply TND_file.
  
  eapply treeseq_pred_tree_rep_latest in H as Hz. destruct Hz.
  rewrite H0 in H4.
  inversion H4.
  rewrite Forall_forall in H8.
  apply H8.
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
  unfold atomic_cp.
  prestep.
  unfold pimpl; intros.
  destruct_lift H.
  unfold tree_with_src in *.
  destruct_lift H8.
  apply sep_star_assoc in H0.
  apply sep_star_comm in H0.
  apply sep_star_assoc in H0.
  apply sep_star_comm in H0.
  apply sep_star_assoc in H0.
  apply sep_star_assoc in H0.
  eapply dir2flatmem2_find_subtree_ptsto_dir in H0 as Hx.
  deex.
  pred_apply; norm.
  unfold stars; cancel.
  intuition; eauto.
  eapply treeseq_in_ds_tree_pred_latest; eauto.
  instantiate (2:= []); eauto.
  
  simpl; step.
  eapply treeseq_in_ds_pushd.
  eauto.
  unfold tree_rep_latest.
  instantiate (1:= {| TStree:= (tree_graft the_dnum d [] temp_fn 
                            (TreeFile a0 dirfile0) (TStree dummy4 !!));
                  TSilist:= ilist';
                  TSfree:= (frees'_1, frees'_2) |}).
  simpl; eauto.
  unfold treeseq_one_safe; simpl; rewrite <- H5; eauto.
  eauto.
  
  safestep.
  eauto.
  simpl; eauto.
  rewrite pushd_latest.
  unfold latest; simpl.
  split; eauto.
  apply treeseq_safe_refl.
  simpl; apply Forall_nil.
  
  eapply treeseq_tree_rep_sync_after_create; eauto.
  pred_apply; cancel.

  replace ([temp_fn]) with (([]: list string)++[temp_fn])%list by auto.
  eapply dirents2mem2_graft_file_none; simpl; eauto.
  eapply tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  rewrite H14; auto.
  pred_apply; cancel.
  
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
  rewrite H14; auto.
  pred_apply; cancel.
  simpl; auto.
  pred_apply; cancel.
  rewrite pushd_latest; simpl; auto.
  unfold dirfile0; simpl; omega.
  
  safestep.
  or_l; cancel.
  eauto.
  
  or_r; cancel.
  eauto.
  eauto.
  eauto.

  or_r; cancel; eauto.
  
  xcrash.
  unfold pimpl; intros.
  eapply H2.
  instantiate (1:= realcrash).
  intros m1 Hx; apply H25 in Hx; pred_apply; xcrash; eauto.
  or_l; cancel; eauto.
  xcrash; eauto.
  pred_apply; cancel.
  
  unfold pimpl; intros.
  eapply H2.
  instantiate (1:= realcrash).
  intros m1 Hx; apply H12 in Hx; pred_apply; xcrash; eauto.
  or_r; xcrash.
  eapply treeseq_in_ds_pushd.
  eauto.
  unfold tree_rep_latest.
  instantiate (2:= {| TStree:= (tree_graft the_dnum d [] temp_fn 
                            (TreeFile a0 dirfile0) (TStree dummy4 !!));
                  TSilist:= ilist';
                  TSfree:= (frees'_1, frees'_2) |}).
  simpl; eauto.
  unfold treeseq_one_safe; simpl; rewrite <- H5; eauto.
  eauto.
  
  assert (A: forall x dummy9, treeseq_pred (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy9 dstbase dstname 
  x)
  ({|
  TStree := tree_graft the_dnum d [] temp_fn (TreeFile a0 dirfile0) (TStree dummy4 !!);
  TSilist := ilist';
  TSfree := (frees'_1, frees'_2) |}, []) ->
  tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy9 dstbase dstname 
  x
  {|
  TStree := tree_graft the_dnum d [] temp_fn (TreeFile a0 dirfile0) (TStree dummy4 !!);
  TSilist := ilist';
  TSfree := (frees'_1, frees'_2) |}).
  unfold treeseq_pred; simpl; intros; auto.
  inversion H14; simpl in *; auto.
  
  apply A.
  eapply treeseq_tree_rep_sync_after_create; eauto.
  pred_apply; cancel.
  replace ([temp_fn]) with (([]: list string)++[temp_fn])%list by auto.
  eapply dirents2mem2_graft_file_none; simpl; eauto.
  eapply tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  rewrite H15; auto.
  pred_apply; cancel.
  eauto.
  pred_apply; cancel.
  
  eapply H2.
  instantiate (1:= realcrash).
  intros m1 Hx; apply H5 in Hx; pred_apply; xcrash; eauto.
  or_l; cancel; eauto.
  xcrash; eauto.
  or_r; xcrash.
  eapply treeseq_in_ds_pushd.
  eauto.
  unfold tree_rep_latest.
  instantiate (2:= {| TStree:= (tree_graft the_dnum d [] temp_fn 
                            (TreeFile x0 dirfile0) (TStree dummy4 !!));
                  TSilist:= x2;
                  TSfree:= (x3_1, x3_2) |}).
  simpl; eauto.
  unfold treeseq_one_safe; simpl; rewrite <- H15; eauto.
  eauto.
  eapply treeseq_tree_rep_sync_after_create; eauto.
  pred_apply; cancel.
  replace ([temp_fn]) with (([]: list string)++[temp_fn])%list by auto.
  eapply dirents2mem2_graft_file_none; simpl; eauto.
  eapply tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  rewrite H14; auto.
  pred_apply; cancel.
  eauto.
  
  eapply tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  Unshelve.
  all: repeat constructor.
  all: apply any.
Qed.
  Proof.
    unfold atomic_cp_recover; intros.
    prestep. norml.
    safecancel.

    (* need to apply treeseq_tree_crash_exists before
     * creating evars in postcondition to create a
     * treeseq_in_ds on crashed disk. *)
    prestep. norm'l.

    denote! (crash_xform _ _) as Hcrash.
    eapply treeseq_tree_crash_exists with (msll' := (MSLL ms)) in Hcrash; eauto.
    destruct Hcrash.
    match goal with H: context [lift_empty] |- _ => destruct_lift H end.
    safecancel.
    eassign ((d, @nil (list valuset))).
    cancel.
    eassign ((mk_tree x (TSilist (nthd n ts)) (TSfree (nthd n ts)), @nil treeseq_one)); simpl in *.
    eapply treeseq_in_ds_crash; eauto.

    (* other preconditions of lookup *)      
    eapply tree_pred_crash_find_name_root in H5 as Hroot; eauto.
    eapply find_name_dirtree_inum; eauto.
    eapply tree_pred_crash_find_name_root in H5 as Hroot; eauto.
    eapply find_name_dirtree_isdir; eauto.

    destruct a0.
    prestep. norm'l.

    eapply tree_pred_crash_find_subtree_root in H5 as Hroot; eauto.
    destruct Hroot.

    intuition; inv_option_eq; deex.
    denote! (tree_crash _ _) as Htc.
    eapply tree_crash_flatmem_crash_xform in Htc.
    2: eapply treeseq_pred_nthd; eauto.
    2: eapply treeseq_pred_tree_rep_dir2flatmem2; eassumption.
    eapply tree_with_tmp_find_name in Htc; eauto.
    apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
    denote flatmem_crash_xform as Htc.
    unfold tree_with_tmp in Htc.
    apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
    denote flatmem_crash_xform as Htc.
    eapply pimpl_apply in Htc.
    2: repeat rewrite flatmem_crash_xform_sep_star.
    2: repeat rewrite flatmem_crash_xform_file.
    2: reflexivity.
    destruct_lift Htc.

    2: distinct_names.

    safecancel.

    instantiate (pathname := []).
    simpl. reflexivity.

    simpl.
    pred_apply.
    cancel.

    prestep; norm'l.
    safecancel.

    eassumption.

    step.  (* return *)
    or_l. cancel. eapply pimpl_any.

    xcrash. or_r. cancel.
    xcrash.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    unfold tree_rep; simpl.
    intuition; eauto.

    distinct_names.

    left.
    eexists.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.

    synced_file_eq. cancel.
(*     erewrite <- file_crash_data_length; eauto. *)
    eauto.
    eauto.

    step.
    or_r. repeat progress (xform_norm; safecancel).
    eassumption.

    rewrite latest_pushd. unfold treeseq_pred. constructor; [ | constructor ].
    unfold tree_rep_recover; simpl. intuition; eauto.
    distinct_names.
    left. unfold tree_with_src.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.

    synced_file_eq. cancel.

    xcrash. or_r. cancel.
    xcrash.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    3: constructor.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    left.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    (* erewrite <- file_crash_data_length; eauto. *)

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    right. left.
    unfold tree_with_src.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    eauto.

    xcrash. or_r. cancel.
    xcrash.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    left.
    eexists.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    (* erewrite <- file_crash_data_length; eauto. *)
    eauto.

    or_r. cancel. xcrash.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    3: constructor.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    left.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    (* erewrite <- file_crash_data_length; eauto. *)

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    right. left.
    unfold tree_with_src.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    eauto.

    step.   (* lookup failed? *)
    right.

    denote! (tree_crash _ _) as Htc.
    eapply tree_crash_flatmem_crash_xform in Htc.
    2: eapply treeseq_pred_nthd; eauto.
    2: eapply treeseq_pred_tree_rep_dir2flatmem2; eassumption.
    eapply tree_with_tmp_find_name_none in Htc; eauto.
    apply flatmem_crash_xform_or_dist in Htc; destruct Htc.

    {
      denote flatmem_crash_xform as Htc.
      unfold tree_with_src in Htc.
      apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
      denote flatmem_crash_xform as Htc.
      eapply pimpl_apply in Htc.
      2: repeat rewrite flatmem_crash_xform_sep_star.
      2: repeat rewrite flatmem_crash_xform_nothing.
      2: repeat rewrite flatmem_crash_xform_file.
      2: repeat rewrite flatmem_crash_xform_dir.
      2: repeat rewrite flatmem_crash_xform_lift_empty.
      2: reflexivity.
      destruct_lift Htc.

      pred_apply. synced_file_eq. cancel.
      eassumption.

      unfold treeseq_pred. constructor. 2: constructor.
      unfold tree_rep_recover. intuition; eauto.
      distinct_names.
      simpl.
      left. pred_apply.
      unfold tree_with_src. cancel.
    }

    {
      denote flatmem_crash_xform as Htc.
      unfold tree_with_dst in Htc.
      apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
      denote flatmem_crash_xform as Htc.
      eapply pimpl_apply in Htc.
      2: repeat rewrite flatmem_crash_xform_sep_star.
      2: repeat rewrite flatmem_crash_xform_nothing.
      2: repeat rewrite flatmem_crash_xform_file.
      2: repeat rewrite flatmem_crash_xform_dir.
      2: repeat rewrite flatmem_crash_xform_lift_empty.
      2: reflexivity.
      destruct_lift Htc.

      pred_apply. synced_file_eq. cancel.
      eassumption.

      unfold treeseq_pred. constructor. 2: constructor.
      unfold tree_rep_recover. intuition; eauto.
      distinct_names.
      simpl.
      right.
      unfold tree_with_dst. pred_apply.

      synced_file_eq. cancel.
    }

    distinct_names.

    (* crash condition *)
    denote! (tree_crash _ _) as Htc.
    eapply tree_crash_flatmem_crash_xform in Htc.
    2: eapply treeseq_pred_nthd; eauto.
    2: eapply treeseq_pred_tree_rep_dir2flatmem2; eassumption.

    {
      apply flatmem_crash_xform_or_dist in Htc; destruct Htc.
      {
        denote flatmem_crash_xform as Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        unfold tree_with_tmp in Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        eapply pimpl_apply in Htc.
        2: repeat rewrite flatmem_crash_xform_sep_star.
        2: repeat rewrite flatmem_crash_xform_nothing.
        2: repeat rewrite flatmem_crash_xform_file.
        2: repeat rewrite flatmem_crash_xform_dir.
        2: repeat rewrite flatmem_crash_xform_lift_empty.
        2: reflexivity.
        destruct_lift Htc.

        xcrash. or_r. cancel. xcrash.
        eassign ((mk_tree x (TSilist (nthd n ts)) (TSfree (nthd n ts)), @nil treeseq_one)); simpl in *.
        eapply treeseq_in_ds_crash; eauto.
        2: eauto.

        unfold treeseq_pred, tree_rep; intuition.
        constructor. 2: constructor.
        intuition; eauto. distinct_names.

        left. pred_apply. unfold tree_with_tmp. synced_file_eq. cancel.
        (* erewrite <- file_crash_data_length; eauto. *)
      }

      denote flatmem_crash_xform as Htc.
      apply flatmem_crash_xform_or_dist in Htc; destruct Htc.
      {
        denote flatmem_crash_xform as Htc.
        unfold tree_with_src in Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        eapply pimpl_apply in Htc.
        2: repeat rewrite flatmem_crash_xform_sep_star.
        2: repeat rewrite flatmem_crash_xform_nothing.
        2: repeat rewrite flatmem_crash_xform_file.
        2: repeat rewrite flatmem_crash_xform_dir.
        2: repeat rewrite flatmem_crash_xform_lift_empty.
        2: reflexivity.
        destruct_lift Htc.

        xcrash. or_r. cancel. xcrash.
        eassign ((mk_tree x (TSilist (nthd n ts)) (TSfree (nthd n ts)), @nil treeseq_one)); simpl in *.
        eapply treeseq_in_ds_crash; eauto.
        2: eauto.

        unfold treeseq_pred, tree_rep; intuition.
        constructor. 2: constructor.
        intuition; eauto. distinct_names.

        right. left. pred_apply. unfold tree_with_src. synced_file_eq. cancel.
      }

      {
        denote flatmem_crash_xform as Htc.
        unfold tree_with_dst in Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        eapply pimpl_apply in Htc.
        2: repeat rewrite flatmem_crash_xform_sep_star.
        2: repeat rewrite flatmem_crash_xform_nothing.
        2: repeat rewrite flatmem_crash_xform_file.
        2: repeat rewrite flatmem_crash_xform_dir.
        2: repeat rewrite flatmem_crash_xform_lift_empty.
        2: reflexivity.
        destruct_lift Htc.

        edestruct (dirfile_crash_exists dstfile).

        xcrash. or_r. cancel. xcrash.
        eassign ((mk_tree x (TSilist (nthd n ts)) (TSfree (nthd n ts)), @nil treeseq_one)); simpl in *.
        eapply treeseq_in_ds_crash; eauto.

        unfold treeseq_pred, tree_rep; intuition.
        constructor. 2: constructor.
        intuition; eauto. distinct_names.

        right. right. pred_apply. unfold tree_with_dst.
        synced_file_eq. synced_file_eq. cancel.
        eauto.
      }
    }

    cancel.
    xcrash. or_l.
    rewrite LOG.before_crash_idempred.
    cancel; auto.
    
  Grab Existential Variables.
    all: eauto.
    exact Mem.empty_mem.
  Qed.
Proof.
  intros.
  eapply tree_crash_find_name_root; eauto.
  destruct H.
  destruct H1.
  destruct H2.
  destruct H2.
  unfold tree_with_tmp in *. 
  destruct H2.
  eapply tree_rep_find_name_root; eauto.
  pred_apply; cancel; eauto.
  
  destruct H2.
  unfold tree_with_src in *. 
  destruct H2.
  eapply tree_rep_find_name_root; eauto.
  pred_apply; cancel; eauto.
  
  destruct H2.
  unfold tree_with_dst in *. 
  eapply tree_rep_find_name_root; eauto.
  pred_apply; cancel; eauto.
Qed.
Proof.
  unfold treeseq_in_ds; simpl; intros.
  destruct H.
  apply NEforall2_length in H; simpl in *; auto.
Qed.
Proof.
  intros.
  eapply tree_crash_find_subtree_root; eauto.
  unfold tree_rep in H.
  intuition; eauto.

  destruct H2.
  unfold tree_with_tmp in *. 
  destruct H2.
  eapply tree_rep_find_subtree_root with (Ftree := Ftree); eauto.
  pred_apply; cancel.

  unfold tree_with_src in *. 
  destruct H3.
  eapply tree_rep_find_subtree_root with (Ftree := Ftree); eauto.
  pred_apply; cancel.

  unfold tree_with_dst in *. 
  destruct H3.
  eapply tree_rep_find_subtree_root with (Ftree := Ftree); eauto.
  pred_apply; cancel.
Qed.
Proof.
  intros.
  unfold treeseq_in_ds.
  constructor; simpl.
  split.
  unfold TREESEQ.tree_rep.
  intuition; simpl.
  pred_apply; safecancel.
  unfold treeseq_one_safe; simpl.
  eapply dirtree_safe_refl.
  constructor.
  unfold tree_rep_latest; simpl.
  pred_apply; cancel.

  replace ms with (BFILE.ms_empty (MSLL ms)).
  cancel.
  destruct ms.
  unfold ATOMICCP.MSLL.
  unfold BFILE.MSinitial in *.
  intuition. simpl in *. subst.
  unfold BFILE.ms_empty; simpl.
  reflexivity.
Qed.
Proof.
  unfold treeseq_pred, tree_rep; intros.
  intuition.
  - deex.
    pred_apply. cancel.
  - pred_apply; cancel.
  - pred_apply; cancel.
Qed.
Proof.
  induction d; intros; simpl; auto.
  destruct a; simpl in *.
  destruct (string_dec s0 s).
  exfalso; auto.
  rewrite IHd; auto.
Qed.
Proof.
  induction ents; intros; simpl; auto.
  apply TND_dir.
  simpl.
  apply Forall_forall; intros x Hf; destruct Hf; subst.
  apply TND_file.
  inversion H1.
  simpl.
  econstructor; auto.
  apply NoDup_nil.
  
  destruct a.
  destruct (string_dec s tfn); simpl in *; auto.
  exfalso; auto.
  inversion H0; subst; simpl in *.
  inversion H3; subst.
  inversion H4; subst.
  assert (A: tree_names_distinct (TreeDir inum ents)).
  apply TND_dir; eauto.
  assert (A0: ~In tfn (map fst ents)).
  auto.
  
  apply TND_dir; simpl.
  constructor; auto.
  specialize (IHents tfn a0 df inum).
  specialize (IHents A0 A).
  inversion IHents; subst; auto. 
  
  specialize (IHents tfn a0 df inum).
  specialize (IHents A0 A).
  inversion IHents; subst; auto. 
  constructor; auto.
  rewrite add_to_list_not_in.
  rewrite map_app; simpl.
  unfold not; intros .
  apply in_app_iff in H1.
  destruct H1; auto.
  inversion H1; subst; auto.
  auto.
Qed.
  Proof.

    unfold atomic_cp_recover; intros.
    prestep. norml.
    safecancel.

    (* need to apply treeseq_tree_crash_exists before
     * creating evars in postcondition to create a
     * treeseq_in_ds on crashed disk. *)
    prestep. norm'l.
    
    denote! (crash_xform _ _) as Hcrash.
    eapply treeseq_tree_crash_exists with (msll' := (MSLL ms)) in Hcrash; eauto.
    destruct Hcrash.
    match goal with H: context [lift_empty] |- _ => destruct_lift H end.
    
    (* Split between last tree and rest *)
    unfold pushd in H6.
    apply treeseq_in_ds_snd_length in H7 as Hx.
    unfold LogReplay.diskstate in *; rewrite <- Hx in H12; simpl in H12.
    inversion H12.
    
    (* Last Tree *)
    rewrite nthd_pushd_latest' in *; auto.

    safecancel.
    eassign ((d, @nil (list valuset))).
    cancel.
    eassign ((mk_tree x (TSilist t) (TSfree t), @nil treeseq_one)).
    eapply treeseq_in_ds_crash_single; eauto.
    eapply tree_pred_crash_find_name_root_single in H6 as Hroot; eauto.
    eapply find_name_dirtree_inum; simpl; eauto.
    eapply tree_pred_crash_find_name_root_single in H6 as Hroot; eauto.
    eapply find_name_dirtree_isdir; simpl; eauto.
    
    
    destruct a0.
    prestep. norm'l.
    
    eapply tree_pred_crash_find_name_root_single in H6 as Hroot; eauto.
    destruct Hroot.

    intuition; inv_option_eq; deex.
    denote! (tree_crash _ _) as Htc.
    eapply tree_crash_flatmem_crash_xform in Htc.

    2: eapply treeseq_pred_tree_rep_dir2flatmem2_single; eassumption.
    eapply tree_with_tmp_find_name in Htc; eauto.
    apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
    denote flatmem_crash_xform as Htc.
    unfold tree_with_tmp in Htc.
    apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
    denote flatmem_crash_xform as Htc.
    eapply pimpl_apply in Htc.
    2: repeat rewrite flatmem_crash_xform_sep_star.
    2: repeat rewrite flatmem_crash_xform_file.
    2: reflexivity.
    destruct_lift Htc.

    2: distinct_names.
    
    repeat rewrite flatmem_crash_xform_dir in H4.
    repeat rewrite flatmem_crash_xform_lift_empty in H4.
    apply sep_star_assoc in H4.
    apply sep_star_comm in H4.
    apply sep_star_assoc in H4.
    apply sep_star_comm in H4.
    apply sep_star_assoc in H4.
    apply tree_rep_find_subtree_root in H4 as Hpath.
    destruct Hpath.
    simpl in H8. 
    
    safecancel.

    instantiate (pathname := []).
    simpl; eauto.

    simpl.
    pred_apply.
    cancel.

    prestep; norm'l.
    safecancel.

    eassumption.
    
    step.  (* return *)
    or_l. cancel. eapply pimpl_any.

    xcrash. or_r. cancel.
    xcrash.
    or_r; cancel; eauto.
    eassumption.

    unfold treeseq_pred. constructor; simpl; eauto.
    2: apply Forall_nil.
    unfold tree_rep; simpl.
    intuition; eauto.

    distinct_names.

    left.
    eexists.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.

    synced_file_eq. cancel.
    eauto.
    eauto.
    

    step.
    or_r. repeat progress (xform_norm; safecancel).
    rewrite sep_star_or_distr; or_r; repeat progress (xform_norm; safecancel).
    all: eauto.

    rewrite pushd_latest; unfold treeseq_pred. constructor; [ | constructor ].
    unfold tree_rep_recover; simpl. intuition; eauto.
    distinct_names.
    left. unfold tree_with_src.
    pred_apply' H24.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.

    xcrash. or_r. cancel.
    xcrash.
    or_r; cancel; eauto.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    3: constructor.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    left.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    right. left.
    unfold tree_with_src.
    pred_apply' H24.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    eauto.

    xcrash. or_r. cancel.
    xcrash.
    or_r; cancel; eauto.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    left.
    eexists.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    eauto.

    or_r. cancel. xcrash.
    or_r; cancel; eauto.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    3: constructor.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    left.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    right. left.
    unfold tree_with_src.
    pred_apply' H8.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    eauto.
    eapply rep_tree_names_distinct; eauto.

    step.   (* lookup failed? *)
    right.

    denote! (tree_crash _ _) as Htc.
    eapply tree_crash_flatmem_crash_xform in Htc.

    2: eapply treeseq_pred_tree_rep_dir2flatmem2_single; eassumption.
    eapply tree_with_tmp_find_name_none in Htc; eauto.
    apply flatmem_crash_xform_or_dist in Htc; destruct Htc.

    {
      denote flatmem_crash_xform as Htc.
      unfold tree_with_src in Htc.
      apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
      denote flatmem_crash_xform as Htc.
      eapply pimpl_apply in Htc.
      2: repeat rewrite flatmem_crash_xform_sep_star.
      2: repeat rewrite flatmem_crash_xform_nothing.
      2: repeat rewrite flatmem_crash_xform_file.
      2: repeat rewrite flatmem_crash_xform_dir.
      2: repeat rewrite flatmem_crash_xform_lift_empty.
      2: reflexivity.
      destruct_lift Htc.

      pred_apply. synced_file_eq. cancel.
      rewrite sep_star_or_distr; or_r; cancel.
      2:eassumption.

      unfold treeseq_pred. constructor. 2: constructor.
      unfold tree_rep_recover. intuition; eauto.
      distinct_names.
      simpl.
      left. pred_apply.
      unfold tree_with_src. cancel.
    }

    {
      denote flatmem_crash_xform as Htc.
      unfold tree_with_dst in Htc.
      apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
      denote flatmem_crash_xform as Htc.
      eapply pimpl_apply in Htc.
      2: repeat rewrite flatmem_crash_xform_sep_star.
      2: repeat rewrite flatmem_crash_xform_nothing.
      2: repeat rewrite flatmem_crash_xform_file.
      2: repeat rewrite flatmem_crash_xform_dir.
      2: repeat rewrite flatmem_crash_xform_lift_empty.
      2: reflexivity.
      destruct_lift Htc.

      pred_apply. synced_file_eq. cancel.
      rewrite sep_star_or_distr; or_r; cancel.
      2:eassumption.

      unfold treeseq_pred. constructor. 2: constructor.
      unfold tree_rep_recover. intuition; eauto.
      distinct_names.
      simpl.
      right.
      unfold tree_with_dst. pred_apply.

      synced_file_eq. cancel.
    }

    distinct_names.

    denote! (tree_crash _ _) as Htc.
    eapply tree_crash_flatmem_crash_xform in Htc.
    2: eapply treeseq_pred_tree_rep_dir2flatmem2_single; eassumption.

    {
      apply flatmem_crash_xform_or_dist in Htc; destruct Htc.
      {
        denote flatmem_crash_xform as Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        unfold tree_with_tmp in Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        eapply pimpl_apply in Htc.
        2: repeat rewrite flatmem_crash_xform_sep_star.
        2: repeat rewrite flatmem_crash_xform_nothing.
        2: repeat rewrite flatmem_crash_xform_file.
        2: repeat rewrite flatmem_crash_xform_dir.
        2: repeat rewrite flatmem_crash_xform_lift_empty.
        2: reflexivity.
        destruct_lift Htc.

        xcrash. or_r. cancel. xcrash.
        or_r; cancel; eauto.
        eassign ((mk_tree x (TSilist t) (TSfree t), @nil treeseq_one)); simpl in *.
        eapply treeseq_in_ds_crash_single; eauto.

        unfold treeseq_pred, tree_rep; intuition.
        constructor. 2: constructor.
        intuition; eauto. distinct_names.

        left. pred_apply. unfold tree_with_tmp. synced_file_eq. cancel.
      }

      denote flatmem_crash_xform as Htc.
      apply flatmem_crash_xform_or_dist in Htc; destruct Htc.
      {
        denote flatmem_crash_xform as Htc.
        unfold tree_with_src in Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        eapply pimpl_apply in Htc.
        2: repeat rewrite flatmem_crash_xform_sep_star.
        2: repeat rewrite flatmem_crash_xform_nothing.
        2: repeat rewrite flatmem_crash_xform_file.
        2: repeat rewrite flatmem_crash_xform_dir.
        2: repeat rewrite flatmem_crash_xform_lift_empty.
        2: reflexivity.
        destruct_lift Htc.

        xcrash. or_r. cancel. xcrash.
        or_r; cancel; eauto.
        eassign ((mk_tree x (TSilist t) (TSfree t), @nil treeseq_one)); simpl in *.
        eapply treeseq_in_ds_crash_single; eauto.


        unfold treeseq_pred, tree_rep; intuition.
        constructor. 2: constructor.
        intuition; eauto. distinct_names.

        right. left. pred_apply. unfold tree_with_src. synced_file_eq. cancel.
      }

      {
        denote flatmem_crash_xform as Htc.
        unfold tree_with_dst in Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        eapply pimpl_apply in Htc.
        2: repeat rewrite flatmem_crash_xform_sep_star.
        2: repeat rewrite flatmem_crash_xform_nothing.
        2: repeat rewrite flatmem_crash_xform_file.
        2: repeat rewrite flatmem_crash_xform_dir.
        2: repeat rewrite flatmem_crash_xform_lift_empty.
        2: reflexivity.
        destruct_lift Htc.

        edestruct (dirfile_crash_exists dfile).

        xcrash. or_r. cancel. xcrash.
        or_r; cancel; eauto.
        eassign ((mk_tree x (TSilist t) (TSfree t), @nil treeseq_one)); simpl in *.
        eapply treeseq_in_ds_crash_single; eauto.

        unfold treeseq_pred, tree_rep; intuition.
        constructor. 2: constructor.
        intuition; eauto. distinct_names.

        right. right. pred_apply. unfold tree_with_dst.
        synced_file_eq. synced_file_eq. cancel.
      }
    }

    (* Other Trees *)      
    
    rewrite nthd_pushd' in *; auto.

    safecancel.
    eassign ((d, @nil (list valuset))).
    cancel.
    eassign ((mk_tree x (TSilist (nthd n ts')) (TSfree (nthd n ts')), @nil treeseq_one)); simpl in *.
    eapply treeseq_in_ds_crash; eauto.
    eapply tree_pred_crash_find_name_root in H5 as Hroot; eauto.
    eapply find_name_dirtree_inum; simpl; eauto.
    eapply tree_pred_crash_find_name_root in H5 as Hroot; eauto.
    eapply find_name_dirtree_isdir; simpl; eauto.

    destruct a0.
    prestep. norm'l.
    
    eapply tree_pred_crash_find_subtree_root in H5 as Hroot; eauto.
    destruct Hroot.

    intuition; inv_option_eq; deex.
    denote! (tree_crash _ _) as Htc.
    eapply tree_crash_flatmem_crash_xform in Htc.
    2: eapply treeseq_pred_nthd; eauto.
    2: eapply treeseq_pred_tree_rep_dir2flatmem2; eassumption.
    eapply tree_with_tmp_find_name in Htc; eauto.
    apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
    denote flatmem_crash_xform as Htc.
    unfold tree_with_tmp in Htc.
    apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
    denote flatmem_crash_xform as Htc.
    eapply pimpl_apply in Htc.
    2: repeat rewrite flatmem_crash_xform_sep_star.
    2: repeat rewrite flatmem_crash_xform_file.
    2: reflexivity.
    destruct_lift Htc.

    2: distinct_names.

    safecancel.

    instantiate (pathname := []).
    simpl. reflexivity.

    simpl.
    pred_apply.
    cancel.

    prestep; norm'l.
    safecancel.

    eassumption.
    
    step.  (* return *)
    or_l. cancel. eapply pimpl_any.

    xcrash. or_r. cancel.
    xcrash.
    or_l; cancel; eauto.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    unfold tree_rep; simpl.
    intuition; eauto.

    distinct_names.

    left.
    eexists.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.

    synced_file_eq. cancel.
    eauto.
    eauto.

    step.
    or_r. repeat progress (xform_norm; safecancel).
    rewrite sep_star_or_distr; or_l; cancel.
    all: eauto.

    rewrite latest_pushd. unfold treeseq_pred. constructor; [ | constructor ].
    unfold tree_rep_recover; simpl. intuition; eauto.
    distinct_names.
    left. unfold tree_with_src.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.

    synced_file_eq. cancel.

    xcrash. or_r. cancel.
    xcrash.
    or_l; cancel; eauto.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    3: constructor.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    left.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    right. left.
    unfold tree_with_src.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    eauto.

    xcrash. or_r. cancel.
    xcrash.
    or_l; cancel; eauto.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    left.
    eexists.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    eauto.

    or_r. cancel. xcrash.
    or_l; cancel; eauto.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    3: constructor.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    left.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    right. left.
    unfold tree_with_src.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    eauto.

    step.   (* lookup failed? *)
    right.

    denote! (tree_crash _ _) as Htc.
    eapply tree_crash_flatmem_crash_xform in Htc.
    2: eapply treeseq_pred_nthd; eauto.
    2: eapply treeseq_pred_tree_rep_dir2flatmem2; eassumption.
    eapply tree_with_tmp_find_name_none in Htc; eauto.
    apply flatmem_crash_xform_or_dist in Htc; destruct Htc.

    {
      denote flatmem_crash_xform as Htc.
      unfold tree_with_src in Htc.
      apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
      denote flatmem_crash_xform as Htc.
      eapply pimpl_apply in Htc.
      2: repeat rewrite flatmem_crash_xform_sep_star.
      2: repeat rewrite flatmem_crash_xform_nothing.
      2: repeat rewrite flatmem_crash_xform_file.
      2: repeat rewrite flatmem_crash_xform_dir.
      2: repeat rewrite flatmem_crash_xform_lift_empty.
      2: reflexivity.
      destruct_lift Htc.

      pred_apply. synced_file_eq. cancel.
      rewrite sep_star_or_distr; or_l; cancel.
      2: eassumption.

      unfold treeseq_pred. constructor. 2: constructor.
      unfold tree_rep_recover. intuition; eauto.
      distinct_names.
      simpl.
      left. pred_apply.
      unfold tree_with_src. cancel.
    }

    {
      denote flatmem_crash_xform as Htc.
      unfold tree_with_dst in Htc.
      apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
      denote flatmem_crash_xform as Htc.
      eapply pimpl_apply in Htc.
      2: repeat rewrite flatmem_crash_xform_sep_star.
      2: repeat rewrite flatmem_crash_xform_nothing.
      2: repeat rewrite flatmem_crash_xform_file.
      2: repeat rewrite flatmem_crash_xform_dir.
      2: repeat rewrite flatmem_crash_xform_lift_empty.
      2: reflexivity.
      destruct_lift Htc.

      pred_apply. synced_file_eq. cancel.
      rewrite sep_star_or_distr; or_l; cancel.
      2: eassumption.

      unfold treeseq_pred. constructor. 2: constructor.
      unfold tree_rep_recover. intuition; eauto.
      distinct_names.
      simpl.
      right.
      unfold tree_with_dst. pred_apply.

      synced_file_eq. cancel.
    }

    distinct_names.

    (* crash condition *)
    denote! (tree_crash _ _) as Htc.
    eapply tree_crash_flatmem_crash_xform in Htc.
    2: eapply treeseq_pred_nthd; eauto.
    2: eapply treeseq_pred_tree_rep_dir2flatmem2; eassumption.

    {
      apply flatmem_crash_xform_or_dist in Htc; destruct Htc.
      {
        denote flatmem_crash_xform as Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        unfold tree_with_tmp in Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        eapply pimpl_apply in Htc.
        2: repeat rewrite flatmem_crash_xform_sep_star.
        2: repeat rewrite flatmem_crash_xform_nothing.
        2: repeat rewrite flatmem_crash_xform_file.
        2: repeat rewrite flatmem_crash_xform_dir.
        2: repeat rewrite flatmem_crash_xform_lift_empty.
        2: reflexivity.
        destruct_lift Htc.

        xcrash. or_r. cancel. xcrash.
        or_l; cancel; eauto.
        eassign ((mk_tree x (TSilist (nthd n ts')) (TSfree (nthd n ts')), @nil treeseq_one)); simpl in *.
        eapply treeseq_in_ds_crash; eauto.

        unfold treeseq_pred, tree_rep; intuition.
        constructor. 2: constructor.
        intuition; eauto. distinct_names.

        left. pred_apply. unfold tree_with_tmp. synced_file_eq. cancel.
      }

      denote flatmem_crash_xform as Htc.
      apply flatmem_crash_xform_or_dist in Htc; destruct Htc.
      {
        denote flatmem_crash_xform as Htc.
        unfold tree_with_src in Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        eapply pimpl_apply in Htc.
        2: repeat rewrite flatmem_crash_xform_sep_star.
        2: repeat rewrite flatmem_crash_xform_nothing.
        2: repeat rewrite flatmem_crash_xform_file.
        2: repeat rewrite flatmem_crash_xform_dir.
        2: repeat rewrite flatmem_crash_xform_lift_empty.
        2: reflexivity.
        destruct_lift Htc.

        xcrash. or_r. cancel. xcrash.
        or_l; cancel; eauto.
        eassign ((mk_tree x (TSilist (nthd n ts')) (TSfree (nthd n ts')), @nil treeseq_one)); simpl in *.
        eapply treeseq_in_ds_crash; eauto.

        unfold treeseq_pred, tree_rep; intuition.
        constructor. 2: constructor.
        intuition; eauto. distinct_names.

        right. left. pred_apply. unfold tree_with_src. synced_file_eq. cancel.
      }

      {
        denote flatmem_crash_xform as Htc.
        unfold tree_with_dst in Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        eapply pimpl_apply in Htc.
        2: repeat rewrite flatmem_crash_xform_sep_star.
        2: repeat rewrite flatmem_crash_xform_nothing.
        2: repeat rewrite flatmem_crash_xform_file.
        2: repeat rewrite flatmem_crash_xform_dir.
        2: repeat rewrite flatmem_crash_xform_lift_empty.
        2: reflexivity.
        destruct_lift Htc.

        edestruct (dirfile_crash_exists dstfile).

        xcrash. or_r. cancel. xcrash.
        or_l; cancel; eauto.
        eassign ((mk_tree x (TSilist (nthd n ts')) (TSfree (nthd n ts')), @nil treeseq_one)); simpl in *.
        eapply treeseq_in_ds_crash; eauto.

        unfold treeseq_pred, tree_rep; intuition.
        constructor. 2: constructor.
        intuition; eauto. distinct_names.

        right. right. pred_apply. unfold tree_with_dst.
        synced_file_eq. synced_file_eq. cancel.
      }
    }

    cancel.
    xcrash. or_l.
    rewrite LOG.before_crash_idempred.
    cancel; auto.
    
  Grab Existential Variables.
    all: eauto.
    exact Mem.empty_mem.
Qed.