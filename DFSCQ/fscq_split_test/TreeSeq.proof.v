  Proof.
    intros.
    apply dirtree_safe_refl.
  Qed.
  Proof.
    unfold treeseq_one_safe; intros.
    eapply dirtree_safe_trans; eauto.
  Qed.
  Proof.
    unfold treeseq_pred, NEforall, pushd; simpl; intros.
    intuition.
  Qed.
  Proof.
    unfold treeseq_in_ds; simpl; intuition.
    apply NEforall2_pushd; intuition.
    rewrite latest_pushd.
    eapply NEforall2_impl; eauto.
    intuition.
    intuition.
    unfold treeseq_one_safe in *; intuition.
    rewrite H2 in *.
    eapply dirtree_safe_trans; eauto.
    unfold tree_rep; unfold tree_rep_latest in *. pred_apply; cancel.
    eapply dirtree_safe_refl.
  Qed.
  Proof.
    intros.
    unfold tsupd.
    rewrite d_map_latest; eauto.
  Qed.
  Proof.
    unfold treeseq_pred; intros.
    eapply NEforall_impl; eauto.
  Qed.
  Proof.
    unfold treeseq_safe; intuition.
    - unfold treeseq_safe_fwd in *; intuition.
    - unfold treeseq_safe_bwd in *; intuition.
      specialize (H0 _ _ _ H3).
      inversion H0; eauto.
      right.
      unfold BFILE.ilist_safe in H5; destruct H5.
      eapply In_incl.
      apply H6.
      eauto.
    - eapply BFILE.ilist_safe_trans; eauto.
  Qed.
  Proof.
    intros.
    rewrite subtree_extract with (fnlist := pathname) (subtree := (TreeFile inum f)) in H0; eauto.
    unfold tree_pred in H0.
    destruct_lift H0.
    eapply list2nmem_sel in H0; eauto.
  Qed.
  Proof.
    intros.
    eapply rep_tree_names_distinct in H as Hdistinct.
    apply BFILE.block_belong_to_file_inum_ok in H1 as H1'.

    unfold rep in H.
    unfold BFILE.rep in H.
    destruct_lift H.

    denote find_subtree as Hf.
    denote tree_pred as Ht.
    eapply tree_file_flist in Hf; eauto.
    2: eapply pimpl_apply; [| exact Ht]; cancel.
    2: eassign Ftop; cancel.
    deex.

    erewrite listmatch_extract with (i := inum) in H.
    unfold BFILE.file_match at 2 in H.
    rewrite listmatch_length_pimpl with (a := BFILE.BFData _) in H.
    destruct_lift H.
    rewrite map_length in *.
    unfold BFILE.datatype, datatype in *.
    unfold BFILE.block_belong_to_file in H1.
    intuition.
    subst.
    denote dirfile_to_bfile as Hd.
    rewrite Hd in *.
    unfold dirfile_to_bfile in *. cbn in *.
    simplen.

    rewrite listmatch_length_pimpl in H.
    destruct_lift H.
    simplen.
  Qed.
  Proof.
    intros.
    unfold treeseq_in_ds in H.
    intuition.
  Qed.
  Proof.
    intros.
    unfold treeseq_in_ds in H.
    intuition.
    unfold tree_rep in H0.
    eapply NEforall2_d_in with (x := nthd n ts) in H0 as H0'.
    intuition.
    eassumption.
    reflexivity.
    reflexivity.
  Qed.
  Proof.
    intros.
    unfold treeseq_safe, treeseq_safe_fwd, treeseq_safe_bwd.
    intuition.
    apply BFILE.ilist_safe_refl.
  Qed.
  Proof.
    intros.
    eapply NEforall_d_in'; intros.
    eapply d_in_pushd in H0.
    intuition.
    rewrite H1.
    eapply treeseq_safe_refl.
    eapply NEforall_d_in; eauto.
  Qed.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.file_getattr_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H6 as Hpred; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.
    step.

    unfold treeseq_in_ds in *; intuition.
    eapply NEforall2_impl; eauto; intros; simpl in *; intuition.
    unfold treeseq_one_safe in *; msalloc_eq; eauto.
  Qed.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.lookup_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H7 as Hpred; eauto.
    step.

    unfold treeseq_in_ds in *; intuition.
    eapply NEforall2_impl; eauto; intros; simpl in *; intuition.
    unfold treeseq_one_safe in *; msalloc_eq; eauto.

    unfold treeseq_in_ds in *; intuition.
    eapply NEforall2_impl; eauto; intros; simpl in *; intuition.
    unfold treeseq_one_safe in *; msalloc_eq; eauto.
  Qed.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.read_fblock_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H7 as Hpred; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.
    eassumption.
    step.

    unfold treeseq_in_ds in *; intuition.
    eapply NEforall2_impl; eauto; intros; simpl in *; intuition.
    unfold treeseq_one_safe in *; msalloc_eq; eauto.
  Qed.
  Proof.
    unfold BFILE.block_belong_to_file.
    intros.
    eexists; intuition.
    unfold tree_rep in H; destruct_lift H.
    eapply rep_tree_names_distinct in H as Hdistinct.
    unfold rep in H; destruct_lift H.

    rewrite subtree_extract in H3; eauto.
    simpl in H3.
    destruct_lift H3.
    assert (inum < Datatypes.length dummy1).
    eapply list2nmem_inbound. 
    pred_apply; cancel.

    replace (DFData f) with (BFILE.BFData {|
             BFILE.BFData := DFData f;
             BFILE.BFAttr := DFAttr f;
             BFILE.BFCache := dummy4 |}) in H1 by reflexivity.

    erewrite list2nmem_sel with (x := {|
             BFILE.BFData := DFData f;
             BFILE.BFAttr := DFAttr f;
             BFILE.BFCache := dummy4 |}) (i := inum) (l := dummy1) in H1.
    2: pred_apply; cancel.

    clear H2.
    unfold BFILE.rep in H; destruct_lift H.
    rewrite listmatch_extract in H; eauto.

    unfold BFILE.file_match at 2 in H.
    erewrite listmatch_length_pimpl with (a := (BFILE.BFData dummy1 ⟦ inum ⟧)) in H.
    destruct_lift H.

    rewrite H17 in H1.
    rewrite map_length in H1.
    eauto.

  Grab Existential Variables.
    exact BFILE.bfile0.
  Qed.
  Proof.
    intros;
    unfold BFILE.block_belong_to_file in *.
    intuition.
  Qed.
  Proof.
    unfold pathname_prefix; intros. intro; deex.
    erewrite find_subtree_app_none in H.
    inversion H.
    eauto.
  Qed.
  Proof.
      unfold pathname_prefix; intros. intro; deex.
      erewrite find_subtree_app in H0; eauto.
      destruct suffix.
      eapply H. rewrite app_nil_r; eauto.
      rewrite find_subtree_file_none in H0.
      inversion H0.
  Qed.
  Proof.
    intros. unfold pathname_prefix; intro.
    deex.
    erewrite find_subtree_app in H0 by eauto.
    destruct suffix; simpl in *; try congruence.
    rewrite app_nil_r in *; eauto.
  Qed.
  Proof.
    unfold pathname_prefix; intros. intro; deex.
    erewrite find_subtree_app in * by eauto.
    destruct suffix; simpl in *; try congruence.
    rewrite app_nil_r in *; eauto.
  Qed.
  Proof.
    unfold pathname_prefix; intros. intro; deex.
    case_eq (find_subtree pn2 t); intros.
    destruct d.
    erewrite find_subtree_app in * by eauto. destruct suffix; simpl in *; try congruence. rewrite app_nil_r in *; eauto.
    erewrite find_subtree_update_subtree_child in * by eauto.
    destruct suffix; simpl in *; try congruence. rewrite app_nil_r in *; eauto.
    erewrite find_subtree_app_none in * by eauto. congruence.
  Qed.
  Proof.
    intros.
    subst tree'.
    eapply dir2flatmem2_find_subtree_ptsto in H as Hfind; eauto.
    eapply treeseq_safe_pushd; eauto.
    eapply NEforall_d_in'; intros.
    eapply NEforall_d_in in H5.
    2: instantiate (1 := x); eauto.
    destruct (list_eq_dec string_dec pathname pathname'); simpl.
    - rewrite e in *; simpl.
      unfold treeseq_safe in *.
      intuition; simpl.
      * unfold treeseq_safe_fwd in *.
        intros; simpl.
        specialize (H7 inum0 off bn).
        destruct H7.
        destruct H8.
        eexists x0.
        intuition.
        intuition.
        exists f'.
        erewrite find_update_subtree; eauto.
        rewrite Hfind in H10.
        inversion H10.
        unfold BFILE.treeseq_ilist_safe in *.
        intuition.
        specialize (H7 off bn).
        destruct H7.
        subst.
        eauto.
        subst.
        split; eauto.
      * unfold treeseq_safe_bwd in *; intros.
        destruct (BFILE.block_is_unused_dec (BFILE.pick_balloc (TSfree ts!!) (MSAlloc mscs)) bn).
        ++ deex.
           right.
           unfold BFILE.ilist_safe in H9; intuition.
           eapply In_incl.
           apply b.
           eauto.

        ++ 
        specialize (H5 inum off bn).
        destruct H5.
        ** eexists f.
        split; eauto.
        simpl in *.
        subst.
        erewrite find_update_subtree in H8 by eauto.
        deex.
        inversion H8.
        unfold BFILE.ilist_safe in H3.
        intuition.
        specialize (H13 inum off bn).
        subst.
        destruct H13; eauto.

        exfalso. eauto.

        ** 
        destruct H5.
        simpl in *.
        erewrite find_update_subtree in H8.
        intuition. deex.
        inversion H8; eauto.
        subst.
        left.
        eauto.
        eauto.
        **
        right; eauto.

     * eapply BFILE.ilist_safe_trans; eauto.

     - unfold treeseq_safe in *.
      intuition; simpl.
      (* we updated pathname, but pathname' is still safe, if it was safe. *)
      * unfold treeseq_safe_fwd in *; simpl.
        intros; deex.
        erewrite find_subtree_update_subtree_ne_path; eauto.
        intros.
        edestruct H7; eauto.
        intuition.
        eexists.
        intuition. eauto.
        destruct (addr_eq_dec inum inum0).
        ** subst.
          exfalso. apply n.
          eapply find_subtree_inode_pathname_unique; eauto.

        **
        unfold BFILE.treeseq_ilist_safe in H4; intuition.
        unfold BFILE.block_belong_to_file.
        rewrite <- H14.
        apply H13.
        intuition.
        **
          unfold pathname_prefix; intro; deex.
          edestruct H7; eauto; intuition.
          erewrite find_subtree_app in H12 by eauto.
          destruct suffix; simpl in *; try congruence.
          rewrite app_nil_r in *; eauto.
        **
          unfold pathname_prefix; intro; deex.
          edestruct H7; eauto; intuition.
          erewrite find_subtree_app in Hfind by eauto.
          destruct suffix; simpl in *; try congruence.
          rewrite app_nil_r in *; eauto.
      * unfold treeseq_safe_bwd in *; simpl; intros.
        deex; intuition.
        erewrite find_subtree_update_subtree_ne_path in *; eauto.

        destruct (addr_eq_dec inum inum0).
        ** subst.
          exfalso. apply n.
          eapply find_subtree_inode_pathname_unique; eauto.
        **

        eapply H5.
        eexists. intuition eauto.

        unfold BFILE.treeseq_ilist_safe in H4; intuition.
        unfold BFILE.block_belong_to_file.
        rewrite H12.
        apply H11.
        intuition.
        **
          unfold pathname_prefix; intro; deex.
          erewrite find_subtree_app in * by eauto.
          destruct suffix; simpl in *; try congruence.
          rewrite app_nil_r in *; eauto.
        **
          eapply find_subtree_update_subtree_file_not_pathname_prefix_2; eauto.
      * eapply BFILE.ilist_safe_trans; eauto.
  Qed.
  Proof.
    unfold tree_rep_latest; intros.
    rewrite mscs_same_except_log_rep by eassumption.
    cancel.
  Qed.
  Proof.
    unfold tree_rep_latest; intros.
    unfold rep. unfold Balloc.IAlloc.rep. unfold Balloc.IAlloc.Alloc.rep; simpl.
    msalloc_eq.
    apply pimpl_refl.
  Qed.
  Proof.
    unfold BFILE.mscs_same_except_log, treeseq_one_safe; intuition msalloc_eq.
    eauto.
  Qed.
  Proof.
    unfold treeseq_in_ds.
    intuition eauto.
    eapply NEforall2_impl; eauto.
    intuition. intuition. intuition.
    eapply mscs_same_except_log_treeseq_one_safe; eauto.
    eapply mscs_same_except_log_tree_rep_latest; eauto.
  Qed.
  Proof.
    split; eapply mscs_same_except_log_rep_treeseq_in_ds; eauto.
    apply BFILE.mscs_same_except_log_comm; eauto.
  Qed.
  Proof.
    unfold treeseq_in_ds, tree_rep_latest; intuition.
    eapply NEforall2_impl; eauto.
    intros; intuition.
    intuition.
    unfold treeseq_one_safe in *; intuition msalloc_eq.
    eauto.
  Qed.
  Proof.
    intros.
    eapply pimpl_ok2. 
    eapply AFS.file_set_attr_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H6 as Hpred; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.
    step.
    or_l. cancel.
    eapply treeseq_in_ds_eq; eauto.
    unfold BFILE.mscs_same_except_log; intuition.
    or_r.
    cancel.
    eapply treeseq_in_ds_pushd; eauto.
    unfold tree_rep.
    unfold treeseq_one_safe.
    simpl.
    rewrite H in H12.
    eassumption.
    rewrite H in *.
    eapply treeseq_in_ds_tree_pred_latest in H6 as Hpred.
    eapply treeseq_safe_pushd_update_subtree; eauto.
    distinct_names.
    distinct_inodes.
    rewrite rep_length in Hpred; destruct_lift Hpred.
    rewrite rep_length in H10; destruct_lift H10.
    congruence.

    unfold dirtree_safe in *.
    intuition.

    eapply dir2flatmem2_update_subtree.
    distinct_names'.
    eassumption.

    xcrash_solve.
    - xform_normr.
      or_l. cancel.
    - or_r. cancel. repeat (progress xform_norm; safecancel).
      eassumption.
      5: reflexivity.
      5: reflexivity.
      5: reflexivity.
      eapply treeseq_in_ds_pushd; eauto.
      unfold treeseq_one_safe.
      simpl.
      repeat rewrite <- surjective_pairing in *.
      rewrite H4 in *; eauto.
      eapply treeseq_in_ds_tree_pred_latest in H6 as Hpred.
      eapply treeseq_safe_pushd_update_subtree; eauto.
      distinct_names.
      distinct_inodes.
      rewrite rep_length in Hpred; destruct_lift Hpred.
      rewrite rep_length in H5; destruct_lift H5.
      congruence.
      unfold dirtree_safe in *.
      repeat rewrite <- surjective_pairing in *.
      rewrite H4 in *; eauto.
      intuition.
      eauto.
      repeat rewrite <- surjective_pairing in *.
      eauto.
      eapply dir2flatmem2_update_subtree.
      distinct_names'.
      eassumption.
  Qed.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.file_truncate_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H8 as Hpred; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.
    step.

    or_l. cancel.
    eapply treeseq_in_ds_mscs'; eauto.

    or_r.
    cancel.
    eapply treeseq_in_ds_pushd; eauto.
    unfold tree_rep.
    unfold treeseq_one_safe.
    simpl in *.
    rewrite H in H14.
    eassumption.
    eapply treeseq_safe_pushd_update_subtree; eauto.
    distinct_names'.
    eapply treeseq_in_ds_tree_pred_latest in H8 as Hpred.
    distinct_inodes.
    eapply treeseq_in_ds_tree_pred_latest in H8 as Hpred.
    rewrite rep_length in Hpred; destruct_lift Hpred.
    rewrite rep_length in H12; destruct_lift H12.
    congruence. 

    unfold dirtree_safe in *.
    intuition.
    rewrite H in H10; eauto.

    eapply dir2flatmem2_update_subtree; eauto.
    distinct_names'.
    xcrash_solve.
    - xform_normr. or_l. cancel.
    - or_r. cancel. repeat (progress xform_norm; safecancel).
      eassumption.
      5: reflexivity.
      5: reflexivity.
      5: reflexivity.
      eapply treeseq_in_ds_pushd; eauto.
      unfold treeseq_one_safe.
      simpl in *.
      rewrite H4 in *.
      repeat rewrite <- surjective_pairing in *.
      eassumption.
      eapply treeseq_safe_pushd_update_subtree; eauto.
      distinct_names'.
      eapply treeseq_in_ds_tree_pred_latest in H8 as Hpred.
      distinct_inodes.
      eapply treeseq_in_ds_tree_pred_latest in H8 as Hpred.
      rewrite rep_length in Hpred; destruct_lift Hpred.
      rewrite rep_length in H6; destruct_lift H6.
      congruence. 
      unfold dirtree_safe in *.
      repeat rewrite <- surjective_pairing in *.
      rewrite H4 in *; eauto.
      intuition.
      eauto.
      repeat rewrite <- surjective_pairing in *.
      eauto.
      eapply dir2flatmem2_update_subtree; eauto.
      distinct_names'.
  Qed.
  Proof.
    unfold tree_rep; intros.
    destruct t; simpl in *.
    unfold rep in H; destruct_lift H.
    eapply BFILE.block_is_unused_xor_belong_to_file with (m := m); eauto.
    pred_apply.
    cancel.
  Qed.
  Proof.
    intros.
    eapply NEforall_d_in in H3 as H3'; [ | apply nthd_in_ds with (n := n) ].
    unfold treeseq_safe in H3'.
    intuition.
    unfold treeseq_one_upd.
    unfold treeseq_safe_bwd in *.
    edestruct H6; eauto.
    - repeat deex.
      rewrite H8.
      unfold tree_rep; simpl.
      unfold tree_rep in H2. destruct_lift H2.
      eapply dirtree_update_block with (bn := bn) (m := (nthd n ds)) (v := v) in H2 as H2'; eauto.
      pred_apply.
      erewrite dirtree_update_inode_update_subtree; eauto.
      cancel.
      eapply rep_tree_inodes_distinct; eauto.
      eapply rep_tree_names_distinct; eauto.
      eapply tree_file_length_ok.
      eapply H2.
      eauto.
      eauto.
    - unfold tree_rep in *. destruct_lift H2.
      eapply dirtree_update_free with (bn := bn) (v := v) in H2 as H2'; eauto.
      case_eq (find_subtree pathname (TStree (nthd n ts))); intros; [ destruct d | ]; eauto.
      2: pred_apply; cancel.
      2: pred_apply; cancel.
      rewrite updN_oob.
      erewrite update_subtree_same; eauto.
      unfold tree_rep. pred_apply. cancel.
      eapply rep_tree_names_distinct; eauto.
      destruct d; simpl in *; eauto.

      destruct (lt_dec off (Datatypes.length (DFData d))); try omega.
      exfalso.
      edestruct treeseq_block_belong_to_file; eauto.
      eassign (nthd n ds). unfold tree_rep. pred_apply; cancel.

      unfold treeseq_safe_fwd in H4.
      edestruct H4; eauto; intuition.
      rewrite H11 in H; inversion H; subst.
      eapply block_belong_to_file_bn_eq in H0; [ | apply H12 ].
      subst.
      eapply block_is_unused_xor_belong_to_file; eauto.
      eassign (list2nmem (nthd n ds)). unfold tree_rep. pred_apply; cancel.
  Qed.
  Proof.
    intros.
    eapply NEforall_d_in in H3 as H3'; [ | apply latest_in_ds ].
    unfold treeseq_safe in H3'.
    intuition.
    unfold treeseq_one_upd.
    unfold treeseq_safe_bwd in *.
    edestruct H6; eauto.
    - repeat deex.
      rewrite H8.
      unfold tree_rep; simpl.
      unfold tree_rep in H2. destruct_lift H2.
      eapply dirtree_update_block with (bn := bn) (m := (ds !!)) (v := v) in H2 as H2'; eauto.
      pred_apply.
      erewrite dirtree_update_inode_update_subtree; eauto.
      eapply rep_tree_inodes_distinct; eauto.
      eapply rep_tree_names_distinct; eauto.
      eapply tree_file_length_ok.
      eapply H2.
      eauto.
      eauto.
    - unfold tree_rep in *. destruct_lift H2.
      eapply dirtree_update_free with (bn := bn) (v := v) in H2 as H2'; eauto.
      case_eq (find_subtree pathname (TStree (ts !!))); intros; [ destruct d | ]; eauto.
      rewrite updN_oob.
      erewrite update_subtree_same; eauto.
      eapply rep_tree_names_distinct; eauto.
      destruct d; simpl in *; eauto.

      destruct (lt_dec off (Datatypes.length (DFData d))); try omega.
      exfalso.
      edestruct treeseq_block_belong_to_file; eauto.
      eassign (ds !!). unfold tree_rep. pred_apply; cancel.

      unfold treeseq_safe_fwd in H4.
      edestruct H4; eauto; intuition.
      rewrite H8 in H; inversion H; subst.
      eapply block_belong_to_file_bn_eq in H0; [ | apply H9 ].
      subst.
      eapply block_is_unused_xor_belong_to_file; eauto.
      eassign (list2nmem (ds !!)). pred_apply. unfold tree_rep, tree_rep_latest. cancel.
  Qed.
  Proof.
    intros.
    unfold treeseq_one_upd.
    case_eq (find_subtree pathname (TStree t)); intros.
    destruct d; auto.
    destruct t; auto.
    destruct t; auto.
  Qed.
  Proof.
    unfold treeseq_one_safe; intros.
    repeat rewrite treeseq_one_upd_alternative; simpl.
    rewrite H2; clear H2 mscs'.
    unfold dirtree_safe in *; intuition.
    destruct (list_eq_dec string_dec pathname0 pathname); subst.
    - edestruct H3; eauto.
      left.
      intuition.
      repeat deex.
      exists pathname'.
      case_eq (find_subtree pathname (TStree tolder)); intros; eauto.
      destruct d; eauto.
      destruct (list_eq_dec string_dec pathname' pathname); subst.
      + erewrite find_update_subtree; eauto.
        rewrite H5 in H7; inversion H7. eauto.
      + rewrite find_subtree_update_subtree_ne_path; eauto.
        eapply find_subtree_file_not_pathname_prefix; eauto.
        eapply find_subtree_file_not_pathname_prefix; eauto.
    - edestruct H3; eauto.
      left.
      intuition.
      repeat deex.
      exists pathname'.
      case_eq (find_subtree pathname (TStree tolder)); intros; eauto.
      destruct d; eauto.
      destruct (list_eq_dec string_dec pathname' pathname); subst.
      + erewrite find_update_subtree; eauto.
        rewrite H5 in H7; inversion H7. eauto.
      + rewrite find_subtree_update_subtree_ne_path; eauto.
        eapply find_subtree_file_not_pathname_prefix; eauto.
        eapply find_subtree_file_not_pathname_prefix; eauto.
  Qed.
  Proof.
    unfold treeseq_one_safe; intros.
    repeat rewrite treeseq_one_upd_alternative; simpl.
    rewrite H1; simpl.
    rewrite H2; clear H2 mscs'.
    unfold dirtree_safe in *; intuition.
    destruct (list_eq_dec string_dec pathname0 pathname); subst.
    - erewrite find_update_subtree in H0; eauto.
      inversion H0; subst.
      edestruct H2; eauto.
    - rewrite find_subtree_update_subtree_ne_path in H0.
      edestruct H2; eauto.
      eassumption.
      eapply find_subtree_update_subtree_file_not_pathname_prefix_1; eauto.
      eapply find_subtree_update_subtree_file_not_pathname_prefix_2; eauto.
  Qed.
  Proof.
    intros.
    eapply treeseq_one_safe_trans.
    eapply treeseq_one_safe_dsupd_1; eauto.
    eapply treeseq_one_safe_dsupd_2; eauto.
    eapply treeseq_one_safe_refl.
  Qed.
  Proof.
    intros.
    unfold treeseq_in_ds in *; intuition.
    unfold tsupd.
    unfold dsupd.
    eapply NEforall2_d_map; eauto.
    simpl; intros.
    intuition; subst.
    eapply tree_rep_nth_upd; eauto.
    unfold treeseq_in_ds; intuition eauto.
    rewrite d_map_latest.
    unfold tree_rep in H9. destruct_lift H9.
    eapply treeseq_one_safe_dsupd; eauto.
    eapply rep_tree_names_distinct.
    eapply H1.
    eapply rep_tree_names_distinct.
    eapply H6.

    unfold tsupd in *. rewrite d_map_latest in *.
    unfold dsupd in *. rewrite d_map_latest in *.
    unfold tree_rep_latest.
    unfold treeseq_one_upd at 2.
    unfold treeseq_one_upd at 2.
    destruct (find_subtree pathname (TStree ts !!)); [ destruct d | ]; simpl in *; eauto.
  Qed.
  Proof.
    intros.
    unfold treeseq_in_ds in *; intuition.
    unfold tsupd.
    unfold dsupd.
    eapply NEforall2_d_map; eauto.
    simpl; intros.
    intuition; subst.
    eapply tree_rep_nth_upd; eauto.
    unfold treeseq_in_ds; intuition eauto.
    rewrite d_map_latest.
    unfold tree_rep in H7. destruct_lift H7.
    eapply treeseq_one_safe_dsupd; eauto.
    eapply rep_tree_names_distinct.
    eapply H1.
    eapply rep_tree_names_distinct.
    eapply H4.

    unfold tsupd. rewrite d_map_latest.
    unfold dsupd. rewrite d_map_latest.
    eapply tree_rep_latest_upd; eauto.
    unfold treeseq_in_ds; intuition eauto.
  Qed.
  Proof.
    unfold treeseq_safe_fwd in *; simpl in *; eauto. 
    intros.
    case_eq (find_subtree pathname (TStree (nthd n ts))); intros.
    destruct d.
    erewrite find_subtree_update_subtree_ne_path; eauto.
    rewrite H7 in H6.
    erewrite find_subtree_update_subtree_ne_path in H6; eauto.
    deex. eapply find_subtree_update_subtree_file_not_pathname_prefix_1; eauto.
    deex. eapply find_subtree_update_subtree_file_not_pathname_prefix_2; eauto.
    rewrite H7 in H6.
    deex. eapply find_subtree_update_subtree_file_not_pathname_prefix_1; eauto.
    rewrite H7 in H6.
    deex. eapply find_subtree_update_subtree_file_not_pathname_prefix_2; eauto.
    (* directory *)
    rewrite H7 in H6.
    deex.
    {
      destruct (pathname_decide_prefix pathname pathname'). deex. subst.
      +
       edestruct H5.
       eexists.
       intuition eauto.
       intuition.
       destruct suffix. rewrite app_nil_r in *. try congruence.
       erewrite find_subtree_app in H10 by eauto.
       simpl in *. try congruence.

      + erewrite find_subtree_update_subtree_ne_path; eauto.
        eapply find_subtree_dir_not_pathname_prefix_2; eauto.
    }
    (* None *)
    rewrite H7 in H6.
    deex.
    {
      destruct (pathname_decide_prefix pathname' pathname). deex. subst.
      +  (* pathname' was a directory and now a file. *)
        edestruct H5.
        eexists.
        intuition eauto.
        intuition.
        destruct suffix. rewrite app_nil_r in *. try congruence.
        erewrite find_subtree_app in H2 by eauto.
        simpl in *; congruence.

      + erewrite find_subtree_update_subtree_ne_path; eauto.
        eapply find_subtree_none_not_pathname_prefix_1; eauto.
    }
  Qed.
  Proof.
    unfold treeseq_safe_bwd in *; simpl; intros.
    deex; intuition.
    destruct (pathname_decide_prefix pathname pathname'). deex.
    destruct suffix. rewrite app_nil_r in *. try congruence.
    erewrite find_subtree_app in H9 by eauto.
    simpl in *; congruence.
    destruct (pathname_decide_prefix pathname' pathname). deex.
    destruct suffix. rewrite app_nil_r in *. try congruence.
    case_eq (find_subtree pathname' (TStree ts!!)); intros.
    destruct d.
    erewrite find_subtree_app in H3 by eauto.
    simpl in *. congruence.

    edestruct find_subtree_update_subtree_oob_general.
    exact H8.
    eassumption.
    intuition.
    rewrite H11 in H13; inversion H13; subst.
    simpl in *. congruence.

    rewrite find_subtree_app_none in H3 by eauto. congruence.
    assert (~ pathname_prefix pathname pathname').
    unfold pathname_prefix.
    intro. deex. eauto.
    assert (~ pathname_prefix pathname' pathname).
    unfold pathname_prefix.
    intro. deex. eauto.
    erewrite find_subtree_update_subtree_ne_path in *; eauto.
    case_eq (find_subtree pathname (TStree (nthd n ts))); intros.
    destruct d.
    erewrite find_subtree_update_subtree_ne_path; eauto.
    specialize (H7 inum0 off0 bn).
    edestruct H7.
    eexists.
    split; eauto.
    destruct (addr_eq_dec inum inum0).
    ** subst.
      exfalso.
      eapply find_subtree_inode_pathname_unique in H2; eauto.
    ** destruct H15.
      left.
      exists x; eauto.
    ** right; eauto.
    ** 
      specialize (H7 inum0 off0 bn).
      edestruct H7.
      exists f'.
      split; eauto.
      destruct H15.
      intuition.
      left.
      exists x.
      split; eauto.
      right; eauto.
  Qed.
  Proof.
    intros.
    eapply dir2flatmem2_find_subtree_ptsto in H0 as H0'; eauto.
    repeat rewrite treeseq_one_upd_alternative; simpl.
    rewrite H0' in *; simpl.
    destruct (list_eq_dec string_dec pathname' pathname); subst; simpl in *.
    - unfold treeseq_safe in *.
      intuition.
      + unfold treeseq_safe_fwd in *; intros; simpl in *.
        erewrite find_update_subtree in *; eauto.
        exists {|
             DFData := (DFData f) ⟦ off := v ⟧;
             DFAttr := DFAttr f; |}.
        specialize (H9 inum0 off0 bn0).
        case_eq (find_subtree pathname (TStree (nthd n ts))); intros.
        destruct d.
        -- rewrite H12 in *; simpl in *.
          erewrite find_update_subtree in *; eauto.
          destruct H10.
          intuition.
          inversion H13; subst. clear H13.
          edestruct H9.
          eexists d.
          split; eauto.
          intuition.
          rewrite H0' in H13.
          inversion H13; subst; eauto.
          edestruct H9.
          eexists d.
          intuition.
          inversion H13; subst; eauto.
          intuition.
        -- (* a directory *)
          rewrite H12 in *; subst; simpl in *.
          exfalso.
          edestruct H10.
          intuition.
          rewrite H12 in H14; inversion H14.
        -- (* None *)
          rewrite H12 in *; subst; simpl in *.
          exfalso.
          edestruct H10.
          intuition.
          rewrite H12 in H14; inversion H14.
      + unfold treeseq_safe_bwd in *. intros; simpl in *.
        erewrite find_update_subtree in *; eauto.
        destruct H10.
        intuition.
        inversion H12.
        subst.
        clear H12.
        case_eq (find_subtree pathname (TStree (nthd n ts))).
        intros.
        destruct d.
        -- (* a file *)
          specialize (H5 inum0 off0 bn0).
          destruct H5.
          eexists f.
          intuition.
 
          destruct H5.
          unfold BFILE.ilist_safe in H11.
          intuition.
          specialize (H14 inum0 off0 bn0).
          destruct H14; auto.

          left.
          eexists.
          split.
          intuition.
          rewrite H10 in H11.
          inversion H11; subst.
          eauto.
          intuition.

          right; eauto.

        -- (* a directory *)
        destruct (BFILE.block_is_unused_dec (BFILE.pick_balloc (TSfree ts!!) (MSAlloc mscs)) bn0).
        ++ right.
          unfold BFILE.ilist_safe in H11; intuition.
          eapply In_incl.
          apply b.
          eauto.
        ++ 
          specialize (H5 inum0 off0 bn0).
          destruct H5.
          eexists.
          split; eauto.
          destruct H5.
          intuition.
          rewrite H10 in H12.
          exfalso; inversion H12.
          right; eauto.

        -- (* None *)
          intros.
          right.
          specialize (H5 inum0 off0 bn0).
          edestruct H5.
          exists f; eauto.
          deex.
          exfalso.
          rewrite H10 in H14; congruence.
          eassumption.
   - (* different pathnames, but pathname' is still safe, if it was safe. *)
     unfold treeseq_safe in *.
     unfold treeseq_pred in H4.
     eapply NEforall_d_in with (x := (nthd n ts)) in H4 as H4'.  
     2: eapply nthd_in_ds.
     unfold tree_rep in H8; destruct_lift H8.
     intuition; simpl.
      *
        eapply seq_upd_safe_upd_fwd_ne; eauto.
        eapply rep_tree_names_distinct; eapply H8.
      * 
        eapply seq_upd_safe_upd_bwd_ne; eauto.
        eapply rep_tree_names_distinct; eapply H8.
  Qed.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.update_fblock_d_ok.
    safecancel.
    eapply treeseq_in_ds_tree_pred_latest in H8 as Hpred; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.


    pose proof (list2nmem_array (DFData f)).
    pred_apply.
    erewrite arrayN_except with (i := off).
    cancel.

    eapply list2nmem_inbound; eauto.

    safestep.

    eapply treeseq_in_ds_upd; eauto.

    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.

    unfold tsupd. rewrite d_map_latest.
    unfold treeseq_one_upd.
    erewrite dir2flatmem2_find_subtree_ptsto; eauto; simpl.
    2: distinct_names'.
    denote! (DFAttr _ = DFAttr _) as Hx; rewrite <- Hx; clear Hx.
    erewrite <- list2nmem_array_updN; eauto.
    destruct f'; eassumption.
    simplen.

    eapply NEforall_d_in'; intros.
    apply d_in_d_map in H4; deex; intuition.
    eapply NEforall_d_in in H7 as H7'; try eassumption.
    unfold tsupd; rewrite d_map_latest.
    unfold treeseq_in_ds in H8.
    eapply d_in_nthd in H6 as H6'; deex.
    eapply NEforall2_d_in  with (x := (nthd n ts)) in H9 as Hd'; eauto.
    intuition.
    eapply treeseq_upd_safe_upd; eauto.
    unfold tree_rep_latest in *; distinct_names.
    unfold tree_rep_latest in *; distinct_inodes.

    unfold tsupd.
    unfold treeseq_one_upd.
    eapply list2nmem_sel in H5 as H5'.
    rewrite H5'; eauto.

    eapply list2nmem_sel in H5 as H5'.
    rewrite H5'; eauto.
    3: eassumption.

    unfold tsupd.
    erewrite d_map_latest; eauto.
    unfold treeseq_one_upd.
    eapply dir2flatmem2_find_subtree_ptsto in H0 as H0'.
    rewrite H0'; simpl.

    eapply list2nmem_sel in H5 as H5'.
    rewrite <- H5'.

    assert( f' = {|
           DFData := (DFData f) ⟦ off := (v, vsmerge vs) ⟧;
           DFAttr := DFAttr f |}).
    destruct f'.
    f_equal.
    simpl in H15.
    eapply list2nmem_array_updN in H15.
    rewrite H15.
    subst; eauto.
    eapply list2nmem_ptsto_bound in H5 as H5''; eauto.
    eauto.
    eauto.
    rewrite H4.
    eapply dir2flatmem2_update_subtree; eauto.
    distinct_names'.
    distinct_names'.

    pred_apply.
    rewrite arrayN_ex_frame_pimpl; eauto.
    eapply list2nmem_sel in H5 as H5'.
    rewrite H5'.
    cancel.

    xcrash_rewrite.
    xcrash_rewrite.
    xform_norm.
    cancel.
    or_r.
    eapply pimpl_exists_r; eexists.
    repeat (xform_deex_r).
    xform_norm; safecancel.
    eapply list2nmem_sel in H5 as H5'.
    rewrite H5'; eauto.
    eauto.

    eapply list2nmem_sel in H5 as H5'.
    rewrite H5'; eauto.
    eapply treeseq_in_ds_upd'; eauto.

    eapply dir2flatmem2_find_subtree_ptsto; eauto.
    distinct_names'.

    eassumption.

  Grab Existential Variables.
    all: eauto.
  Qed.
  Proof.
    induction vsl; eauto.
    simpl.
    unfold synced_list; simpl.
    f_equal.
    eauto.
  Qed.
  Proof.
    induction n; simpl; eauto; intros.
    destruct vsl; eauto.
    simpl; eauto.
  Qed.
  Proof.
    induction n; eauto.
  Qed.
  Proof.
    induction vsl; simpl; intros; eauto.
    rewrite synced_up_to_n_nil; eauto.
    destruct n; try omega.
    simpl; f_equal.
    eapply IHvsl.
    omega.
  Qed.
  Proof.
    induction synclen; simpl; intros; eauto.
    f_equal.
    destruct l; simpl.
    rewrite synced_up_to_n_nil; eauto.
    erewrite IHsynclen; simpl in *; eauto.
    omega.
  Qed.
  Proof.
    intros.
    destruct (le_dec synclen (Datatypes.length l)).
    eapply cons_synced_up_to_n'; eauto.
    rewrite updN_oob by (simpl; omega).
    rewrite synced_up_to_n_too_long by omega. rewrite <- synced_list_up_to_n.
    rewrite synced_up_to_n_too_long by (simpl; omega). rewrite <- synced_list_up_to_n.
    firstorder.
  Qed.
  Proof.
    induction off; simpl; intros; eauto.
    - rewrite IHoff by omega; simpl.
      f_equal.
      f_equal.
      rewrite updN_comm by omega.
      rewrite selN_updN_ne by omega.
      auto.
  Qed.
  Proof.
    induction off; simpl; eauto; intros.
    rewrite IHoff by omega; simpl.
    rewrite selN_updN_ne by omega.
    auto.
  Qed.
  Proof.
    induction off; intros; simpl; auto.
    rewrite <- IHoff; clear IHoff.
    rewrite synced_file_alt_helper2_oob by omega.
    f_equal.
    f_equal.
    rewrite synced_file_alt_helper_selN_oob by omega.
    auto.
  Qed.
  Proof.
    intros.
    rewrite <- synced_file_alt_helper_helper2_equiv.
    eapply synced_file_alt_helper_selN_oob; auto.
  Qed.
  Proof.
    induction off; simpl; intros; auto.
    rewrite length_updN.
    eauto.
  Qed.
  Proof.
    unfold synced_dirfile, synced_file_alt; intros.
    rewrite synced_list_up_to_n.
    unfold datatype.
    remember (@Datatypes.length valuset (DFData f)) as synclen.
    assert (synclen <= Datatypes.length (DFData f)) by simplen.
    clear Heqsynclen.
    generalize dependent f.
    induction synclen; simpl; intros.
    - destruct f; eauto.
    - rewrite <- IHsynclen; simpl.
      f_equal.
      destruct (DFData f).
      simpl in *; omega.
      eapply cons_synced_up_to_n.
      rewrite length_updN. omega.
  Qed.
  Proof.
    unfold treeseq_one_upd; intros.
    rewrite H0.
    destruct t; simpl in *; f_equal.
    rewrite update_subtree_same; eauto.
    rewrite H0.
    f_equal.
    f_equal.
    destruct f; simpl in *.
    f_equal.
    rewrite <- H2.
    rewrite updN_selN_eq; eauto.
  Qed.
  Proof.
    unfold treeseq_one_file_sync, treeseq_one_file_sync_alt; intros.
    case_eq (find_subtree pathname (TStree t)); eauto.
    destruct d; eauto.
    intros.
    rewrite synced_file_alt_equiv. unfold synced_file_alt.
    remember (@Datatypes.length datatype (DFData d)) as synclen; intros.
    assert (synclen <= Datatypes.length (DFData d)) by simplen.
    clear Heqsynclen.

    remember (map fst (DFData d)) as synced_blocks.
    generalize dependent synced_blocks.
    generalize dependent t.
    generalize dependent d.
    induction synclen; intros.
    - simpl.
      destruct t; destruct d; simpl in *; f_equal.
      eapply update_subtree_same; eauto.
    - simpl.
      erewrite <- IHsynclen.
      f_equal.
      + unfold treeseq_one_upd. rewrite H0; simpl.
        rewrite update_update_subtree_same. reflexivity.
      + unfold treeseq_one_upd. rewrite H0. destruct t; eauto.
      + unfold treeseq_one_upd. rewrite H0. destruct t; eauto.
      + simpl. rewrite length_updN. omega.
      + unfold treeseq_one_upd. rewrite H0. simpl.
        eapply tree_names_distinct_update_subtree.
        eauto. constructor.
      + subst; simpl.
        unfold treeseq_one_upd. rewrite H0; simpl.
        erewrite selN_map.
        erewrite find_update_subtree; eauto.
        unfold datatype in *; omega.
      + subst; simpl.
        rewrite map_updN; simpl.
        erewrite selN_eq_updN_eq; eauto.
        erewrite selN_map; eauto.
  Grab Existential Variables.
    exact $0.
  Qed.
  Proof.
    unfold d_map; destruct ts; intros.
    f_equal; simpl.
    - eapply treeseq_one_file_sync_alt_equiv.
      eapply H.
    - eapply map_ext_in; intros.
      eapply treeseq_one_file_sync_alt_equiv.
      destruct H; simpl in *.
      eapply Forall_forall in H1; eauto.
  Qed.
  Proof.
    intros.
    subst tree_newest.
    rewrite synced_file_alt_equiv.
    unfold synced_file_alt.
    rewrite synced_file_alt_helper_helper2_equiv.
    rewrite <- H0.
    assert (Datatypes.length al <= Datatypes.length (DFData f)) by omega.
    clear H0.

    induction al using rev_ind; simpl; intros.
    - rewrite update_subtree_same; eauto.
      distinct_names.
    - rewrite vssync_vecs_app.
      unfold vssync.
      erewrite <- update_update_subtree_same.
      eapply pimpl_trans; [ apply pimpl_refl | | ].
      2: eapply dirtree_update_block.
      erewrite dirtree_update_inode_update_subtree.
      rewrite app_length; simpl.
      rewrite plus_comm; simpl.

      rewrite synced_file_alt_helper2_selN_oob by omega.
      replace (selN (vssync_vecs m al) x ($0, nil)) with
              (selN (DFData f) (Datatypes.length al) ($0, nil)).

      reflexivity.

      erewrite <- synced_file_alt_helper2_selN_oob.
      eapply dirtree_rep_used_block_eq.
      eapply IHal.
      {
        intros. specialize (H1 i).
        rewrite selN_app1 in H1 by omega.
        eapply H1. rewrite app_length. omega.
      }
      rewrite app_length in *; omega.

      erewrite find_update_subtree. reflexivity. eauto.
      {
        specialize (H1 (Datatypes.length al)).
        rewrite selN_last in H1 by omega.
        eapply H1. rewrite app_length. simpl. omega.
      }
      omega.

      3: eapply find_update_subtree; eauto.

      eapply rep_tree_inodes_distinct. eapply IHal.
      {
        intros. specialize (H1 i).
        rewrite selN_app1 in H1 by omega.
        eapply H1. rewrite app_length. omega.
      }
      rewrite app_length in *; omega.

      eapply rep_tree_names_distinct. eapply IHal.
      {
        intros. specialize (H1 i).
        rewrite selN_app1 in H1 by omega.
        eapply H1. rewrite app_length. omega.
      }
      rewrite app_length in *; omega.

      {
        rewrite synced_file_alt_helper2_length.
        rewrite app_length in *; simpl in *; omega.
      }

      eapply IHal.
      {
        intros. specialize (H1 i).
        rewrite selN_app1 in H1 by omega.
        eapply H1. rewrite app_length. omega.
      }
      rewrite app_length in *; omega.

      eapply find_update_subtree; eauto.
      specialize (H1 (Datatypes.length al)).
      rewrite selN_last in * by auto.
      eapply H1.
      rewrite app_length; simpl; omega.
  Qed.
  Proof.
    intros.
    edestruct d_in_nthd; eauto; subst.
    unfold treeseq_in_ds in H; intuition.
    eapply NEforall2_d_in in H3; try reflexivity; intuition.
    unfold tree_rep in H.
    unfold rep in H.
    destruct_lift H.
    rewrite subtree_extract in H6 by eauto.
    simpl in *.
    destruct_lift H6.
    eapply BFILE.block_belong_to_file_off_ok; eauto.
    eapply pimpl_apply; [ | exact H ]. cancel.
    pred_apply.
    cancel.
    simpl; eauto.
  Qed.
  Proof.
    intros.
    edestruct d_in_nthd; eauto; subst.
    unfold treeseq_in_ds in H; intuition.
    eapply NEforall2_d_in in H3; try reflexivity; intuition.
    unfold tree_rep in H.
    unfold rep in H.
    destruct_lift H.
    rewrite subtree_extract in H6 by eauto.
    simpl in *.
    destruct_lift H6.
    replace (DFData f) with (BFILE.BFData {|
             BFILE.BFData := DFData f;
             BFILE.BFAttr := DFAttr f;
             BFILE.BFCache := dummy4 |}) by reflexivity.
    erewrite list2nmem_sel with (x := {|
             BFILE.BFData := DFData f;
             BFILE.BFAttr := DFAttr f;
             BFILE.BFCache := dummy4 |}).
    eapply BFILE.block_belong_to_file_bfdata_length; eauto.
    eapply pimpl_apply; [ | exact H ]; cancel.
    pred_apply; cancel.
  Qed.
  Proof.
    intros.
    case_eq (length (DFData b)); intros; try omega.
    edestruct H0; intuition.
    eexists; intuition eauto.
    eapply block_belong_to_file_off_ok with (off := n0); eauto; try omega.
    eapply nthd_in_ds.

    eapply Nat.le_succ_l.
    eapply block_belong_to_file_bfdata_length; eauto.
    eapply latest_in_ds.

    rewrite H1 in H5; inversion H5; subst.
    eauto.
  Qed.
  Proof.
    intros.
    eapply NEforall_d_in in H4 as H4'; [ | apply nthd_in_ds with (n := n) ].
    unfold treeseq_safe in H4'.
    unfold treeseq_one_file_sync.
    intuition.
    case_eq (find_subtree pathname (TStree (nthd n ts))); intros.
    destruct d.
    - (* a file *)
      unfold tree_rep; simpl.

      rewrite <- firstn_skipn with (l := al) (n := length (DFData d)).
      remember (skipn (Datatypes.length (DFData d)) al) as al_tail.

      assert (forall i, i < length al_tail -> selN al_tail i 0 = selN al (length (DFData d) + i) 0).
      subst; intros.
      apply skipn_selN.

      assert (length (DFData d) + length al_tail <= length al).
      subst.
      rewrite <- firstn_skipn with (l := al) (n := (length (DFData d))) at 2.
      rewrite app_length.
      eapply Plus.plus_le_compat; try omega.
      rewrite firstn_length.
      rewrite H0.
      rewrite min_l; eauto.
      eapply treeseq_safe_fwd_length; eauto.

      clear Heqal_tail.

      induction al_tail using rev_ind.

      + (* No more tail remaining; all blocks correspond to file [b] *)
        clear H9.
        rewrite app_nil_r.
        unfold tree_rep in H3; destruct_lift H3.
        eexists.
        eexists.
        eapply dirtree_update_safe_pathname_vssync_vecs_file; eauto.

        * rewrite firstn_length.
          rewrite Nat.min_l; eauto.

          case_eq (Datatypes.length (DFData d)); intros; try omega.

        * intros.
          rewrite firstn_length in H9.
          apply PeanoNat.Nat.min_glb_lt_iff in H9.
          intuition.

          rewrite selN_firstn by auto.
          edestruct H7.
          eexists; intuition eauto.

          **
            deex.
            rewrite H6 in H13. inversion H13; subst.
            eauto.

          **
            exfalso.
            edestruct H5; intuition.
            eexists; intuition eauto.
            eapply block_belong_to_file_off_ok with (off := i); eauto; try omega.
            eapply nthd_in_ds.

            rewrite H in H14; inversion H14; subst.
            eapply block_belong_to_file_bn_eq in H15.
            2: eapply H1; eauto.
            rewrite H15 in H9.

            eapply block_is_unused_xor_belong_to_file; eauto.
            eassign (list2nmem (nthd n ds)). unfold tree_rep; pred_apply; cancel.
            eapply block_belong_to_file_off_ok; eauto.
            eapply nthd_in_ds.

      + unfold tree_rep in H3; destruct_lift H3.
        rewrite app_assoc. rewrite vssync_vecs_app.
        unfold vssync.
        edestruct IHal_tail.
        shelve. shelve.
        destruct H11.
        eexists.
        eexists.
        eapply dirtree_update_free.
        eassumption.
        shelve.
        Unshelve.
        intros.
        specialize (H9 i).
        rewrite selN_app1 in H9 by omega. apply H9. rewrite app_length. omega.

        rewrite app_length in *; simpl in *; omega.

        shelve.

        edestruct H7 with (off := length (DFData d) + length al_tail).
        eexists. intuition eauto.
        eapply H1.
        rewrite app_length in *; simpl in *; omega.

        (* [treeseq_safe_bwd] says that the block is present in the old file.  Should be a contradiction. *)
        deex.
        eapply block_belong_to_file_bfdata_length in H14; eauto.
        rewrite H13 in H6; inversion H6; subst. omega.
        eapply nthd_in_ds.

        (* [treeseq_safe_bwd] says the block is unused. *)
        rewrite <- H9 in H12.
        rewrite selN_last in H12 by omega.
        eapply H12.
        rewrite app_length. simpl. omega.

    - (* TreeDir *)
      assert (length al <= length (DFData f)) by omega.
      clear H0.
      induction al using rev_ind; simpl; eauto.

      rewrite vssync_vecs_app.
      unfold vssync.
      edestruct IHal. shelve. shelve. eexists.
      destruct H0.
      eexists.
      eapply dirtree_update_free.
      eassumption.
      shelve. Unshelve.
      intros. specialize (H1 i).
      rewrite selN_app1 in H1 by omega. apply H1. rewrite app_length. omega.
      rewrite app_length in *; simpl in *; omega.

      shelve.

      edestruct H7.
      eexists; intuition eauto.
      eapply H1 with (i := length al); rewrite app_length; simpl; omega.

      deex; congruence.
      rewrite selN_last in H0; eauto.

    - (* None *)
      assert (length al <= length (DFData f)) by omega.
      clear H0.
      induction al using rev_ind; simpl; eauto.

      rewrite vssync_vecs_app.
      unfold vssync.
      edestruct IHal. shelve. shelve. eexists.
      destruct H0.
      eexists.
      eapply dirtree_update_free.
      eassumption.
      shelve. Unshelve.
      intros. specialize (H1 i).
      rewrite selN_app1 in H1 by omega. apply H1. rewrite app_length. omega.
      rewrite app_length in *; simpl in *; omega.

      shelve.

      edestruct H7.
      eexists; intuition eauto.
      eapply H1 with (i := length al); rewrite app_length; simpl; omega.

      deex; congruence.
      rewrite selN_last in H0; eauto.
  Qed.
  Proof.
    intros.
    eapply NEforall_d_in in H4 as H4'; [ | apply latest_in_ds ].
    unfold treeseq_safe in H4'.
    unfold treeseq_one_file_sync.
    intuition.
    case_eq (find_subtree pathname (TStree (ts !!))); intros.
    destruct d.
    - (* a file *)
      unfold tree_rep; simpl.

      rewrite <- firstn_skipn with (l := al) (n := length (DFData d)).
      remember (skipn (Datatypes.length (DFData d)) al) as al_tail.

      assert (forall i, i < length al_tail -> selN al_tail i 0 = selN al (length (DFData d) + i) 0).
      subst; intros.
      apply skipn_selN.

      assert (length (DFData d) + length al_tail <= length al).
      subst.
      rewrite <- firstn_skipn with (l := al) (n := (length (DFData d))) at 2.
      rewrite app_length.
      eapply Plus.plus_le_compat; try omega.
      rewrite firstn_length.
      rewrite H0.
      rewrite min_l; eauto.
      eapply treeseq_safe_fwd_length; eauto.

      rewrite <- latest_nthd; eauto.
      rewrite <- latest_nthd; eauto.

      clear Heqal_tail.

      induction al_tail using rev_ind.

      + (* No more tail remaining; all blocks correspond to file [b] *)
        clear H9.
        rewrite app_nil_r.
        unfold tree_rep in H3; destruct_lift H3.
        eapply dirtree_update_safe_pathname_vssync_vecs_file; eauto.

        * rewrite firstn_length.
          rewrite Nat.min_l; eauto.

          case_eq (Datatypes.length (DFData d)); intros; try omega.

        * intros.
          rewrite firstn_length in H9.
          apply PeanoNat.Nat.min_glb_lt_iff in H9.
          intuition.
          simpl.

          rewrite selN_firstn by auto.
          edestruct H7.
          exists f; intuition eauto.

          **
            deex.
            rewrite H6 in H13. inversion H13; subst.
            eauto.

          **
            exfalso.
            edestruct H5; intuition.
            eexists; intuition eauto.
            eapply block_belong_to_file_off_ok with (off := i); eauto; try omega.
            eapply latest_in_ds.

            rewrite H in H14; inversion H14; subst.
            eapply block_belong_to_file_bn_eq in H15.
            2: eapply H1; eauto.
            rewrite H15 in H9.

            eapply block_is_unused_xor_belong_to_file; eauto.
            eassign (list2nmem (ds !!)). pred_apply. unfold tree_rep, tree_rep_latest. cancel.
            eapply block_belong_to_file_off_ok; eauto.
            eapply latest_in_ds.

      + rewrite app_assoc. rewrite vssync_vecs_app.
        unfold vssync.
        eapply dirtree_update_free.
        eapply IHal_tail.
        intros.
        specialize (H9 i).
        rewrite selN_app1 in H9 by omega. apply H9. rewrite app_length. omega.

        rewrite app_length in *; simpl in *; omega.

        edestruct H7 with (off := length (DFData d) + length al_tail).
        exists f. intuition eauto.
        eapply H1.
        rewrite app_length in *; simpl in *; omega.

        (* [treeseq_safe_bwd] says that the block is present in the old file.  Should be a contradiction. *)
        deex.
        eapply block_belong_to_file_bfdata_length in H13; eauto.
        rewrite H12 in H6; inversion H6; subst. omega.
        eapply latest_in_ds.

        (* [treeseq_safe_bwd] says the block is unused. *)
        rewrite <- H9 in H11.
        rewrite selN_last in H11 by omega.
        eapply H11.
        rewrite app_length. simpl. omega.

    - (* TreeDir *)
      assert (length al <= length (DFData f)) by omega.
      clear H0.
      induction al using rev_ind; simpl; eauto.

      rewrite vssync_vecs_app.
      unfold vssync.
      eapply dirtree_update_free.
      eapply IHal.
      intros. specialize (H1 i).
      rewrite selN_app1 in H1 by omega. apply H1. rewrite app_length. omega.
      rewrite app_length in *; simpl in *; omega.

      edestruct H7.
      eexists; intuition eauto.
      eapply H1 with (i := length al); rewrite app_length; simpl; omega.

      deex; congruence.
      rewrite selN_last in H0; eauto.

    - (* None *)
      assert (length al <= length (DFData f)) by omega.
      clear H0.
      induction al using rev_ind; simpl; eauto.

      rewrite vssync_vecs_app.
      unfold vssync.
      eapply dirtree_update_free.
      eapply IHal.
      intros. specialize (H1 i).
      rewrite selN_app1 in H1 by omega. apply H1. rewrite app_length. omega.
      rewrite app_length in *; simpl in *; omega.

      edestruct H7.
      eexists; intuition eauto.
      eapply H1 with (i := length al); rewrite app_length; simpl; omega.

      deex; congruence.
      rewrite selN_last in H0; eauto.
  Qed.
  Proof.
    intros.
    rewrite treeseq_one_file_sync_alt_equiv.
    unfold treeseq_one_file_sync_alt.
    inversion H.
    destruct H2.
    rewrite H2.
    remember (Datatypes.length (DFData x0)) as len; clear Heqlen.
    remember (ts !!) as y. rewrite Heqy at 1.

    assert (tree_names_distinct (TStree y)) as Hydistinct.
    rewrite Heqy.
    distinct_names'.

    assert (treeseq_one_safe ts !! y mscs').
    subst; eapply treeseq_one_safe_refl.
    clear Heqy. clear H2.
    generalize dependent y.
    induction len; simpl; intros; eauto.
    eapply IHlen.

    repeat deex.
    do 2 eexists.
    unfold treeseq_one_upd.
    rewrite H; simpl.
    erewrite find_update_subtree; eauto.

    repeat deex.

    unfold treeseq_one_upd.
    rewrite H; simpl.
    eapply tree_names_distinct_update_subtree; eauto.
    constructor.
 
    repeat deex.
    eapply treeseq_one_safe_dsupd_2; eauto.
    distinct_names'.
  Qed.
  Proof.
    unfold treeseq_in_ds; intros.
    intuition.
    eapply NEforall2_d_in in H1; intuition.
    unfold treeseq_one_safe.
    rewrite H0.
    eauto.
  Qed.
  Proof.
    intros.
    rewrite treeseq_one_file_sync_alt_equiv.
    unfold treeseq_one_file_sync_alt.
    case_eq (find_subtree pathname (TStree (nthd n ts))); intros.
    2: eapply treeseq_in_ds_one_safe; eauto.
    destruct d.
    2: eapply treeseq_in_ds_one_safe; eauto.

    remember (Datatypes.length (DFData d)) as len; clear Heqlen.
    remember (nthd n ts) as y.
    assert (treeseq_one_safe y (nthd n ts) mscs').
    subst; eapply treeseq_one_safe_refl.
    remember H1 as H1'. clear HeqH1'. rewrite Heqy in H1'.

    assert (tree_names_distinct (TStree y)) as Hydistinct.
    rewrite Heqy.
    distinct_names'.

    clear Heqy.

    assert (exists b0, find_subtree pathname (TStree y) = Some (TreeFile n0 b0) (* /\ map fst (BFILE.BFData b) = map fst (BFILE.BFData b0) *)).
    eexists; intuition eauto.
    clear H1.

    generalize dependent y.
    induction len; simpl; intros; eauto.

    eapply treeseq_one_safe_trans; eauto.
    eapply treeseq_in_ds_one_safe; eauto.

    eapply IHlen.
    destruct H3; intuition.
    eapply treeseq_one_safe_dsupd_1; eauto.

    destruct H3; intuition.

    unfold treeseq_one_upd.
    rewrite H1; simpl.
    eapply tree_names_distinct_update_subtree; eauto.
    constructor.
 
    destruct H3.
    eexists.
    unfold treeseq_one_upd.
    rewrite H1; simpl.
    erewrite find_update_subtree by eauto. reflexivity.

    distinct_names'.
  Qed.
  Proof.
    intros.
    rewrite d_map_latest.
    eapply treeseq_one_safe_trans.
    eapply tree_safe_file_sync_2; eauto.
    eapply tree_safe_file_sync_1; eauto.
  Qed.
  Proof.
    unfold treeseq_in_ds.
    intros.
    simpl; intuition.
    unfold ts_file_sync, dssync_vecs.
    eapply NEforall2_d_map; eauto.
    simpl; intros.
    intuition; subst.
    eapply tree_rep_nth_file_sync; eauto.
    unfold treeseq_in_ds; intuition eauto.
    eapply tree_safe_file_sync; eauto.
    unfold treeseq_in_ds; intuition eauto.

    unfold dssync_vecs in *; rewrite d_map_latest in *.
    unfold ts_file_sync in *; rewrite d_map_latest in *.
    unfold tree_rep_latest.
    unfold treeseq_one_file_sync at 2.
    unfold treeseq_one_file_sync at 2.
    destruct (find_subtree pathname (TStree ts !!)); [ destruct d | ]; simpl in *; eauto.
  Qed.
  Proof.
    unfold treeseq_in_ds.
    intros.
    simpl; intuition.
    unfold ts_file_sync, dssync_vecs.
    eapply NEforall2_d_map; eauto.
    simpl; intros.
    intuition; subst.
    eapply tree_rep_nth_file_sync; eauto.
    unfold treeseq_in_ds; intuition eauto.
    eapply tree_safe_file_sync; eauto.
    unfold treeseq_in_ds; intuition eauto.
    unfold BFILE.mscs_same_except_log in *; intuition eauto.

    unfold dssync_vecs; rewrite d_map_latest.
    unfold ts_file_sync; rewrite d_map_latest.
    eapply tree_rep_latest_file_sync; eauto.
    unfold treeseq_in_ds; intuition eauto.
  Qed.
  Proof.
    intros.
    unfold treeseq_one_file_sync.
    case_eq (find_subtree pathname (TStree t)); intros.
    destruct d; auto.
    destruct t; auto.
    destruct t; auto.
  Qed.
  Proof.
      unfold treeseq_safe_fwd in *; simpl in *; eauto. 
      intros.
      case_eq (find_subtree pathname (TStree ts!!)); intros.
      destruct d.
      specialize (H4 inum0 off bn).
      edestruct H4.
      case_eq (find_subtree pathname (TStree (nthd n ts))); intros.        
      destruct d0.
      rewrite H7 in H5.
      erewrite find_subtree_update_subtree_ne_path in H5; eauto.
      deex. eapply find_subtree_update_subtree_file_not_pathname_prefix_1; eauto.
      deex. eapply find_subtree_update_subtree_file_not_pathname_prefix_2; eauto.
      rewrite H7 in H5.
      deex; eauto.
      rewrite H7 in H5.
      deex; eauto.
      intuition.
      erewrite find_subtree_update_subtree_ne_path; eauto.
      deex. eapply find_subtree_file_not_pathname_prefix with (pn1 := pathname) (pn2 := pathname'); eauto.
      deex. eapply find_subtree_file_not_pathname_prefix with (pn1 := pathname') (pn2 := pathname) in H8; eauto.
      rewrite H2 in H6.
      exfalso.
      inversion H6.
      rewrite H2 in H6.
      exfalso.
      inversion H6.
  Qed.
  Proof.
        unfold treeseq_safe_bwd in *; simpl in *; eauto.
        intros.
        case_eq (find_subtree pathname (TStree (nthd n ts))); intros.        
        destruct d.
        erewrite find_subtree_update_subtree_ne_path; eauto.
        specialize (H4 inum0 off bn).
        edestruct H4.      
        case_eq (find_subtree pathname (TStree ts!!)); intros.
        destruct d0.
        rewrite H7 in H5.
        deex; eauto.
        erewrite find_subtree_update_subtree_ne_path in H8; eauto.
        eapply find_subtree_update_subtree_file_not_pathname_prefix_1; eauto.
        eapply find_subtree_update_subtree_file_not_pathname_prefix_2; eauto.
        rewrite H2 in H7.
        exfalso.
        inversion H7.
        rewrite H2 in H7.
        exfalso.
        inversion H7.
        deex.
        left.
        exists f0; eauto.
        right; eauto.
        rewrite H2 in H5.
        deex. eapply find_subtree_update_subtree_file_not_pathname_prefix_1; eauto.
        rewrite H2 in H5.
        deex. eapply find_subtree_update_subtree_file_not_pathname_prefix_2; eauto.
        (* directory *)
        case_eq (find_subtree pathname (TStree ts!!)); intros.
        destruct d.
        rewrite H7 in H5.
        deex.
        erewrite find_subtree_update_subtree_ne_path in H8; eauto.
        eapply find_subtree_update_subtree_file_not_pathname_prefix_1; eauto.
        eapply find_subtree_update_subtree_file_not_pathname_prefix_2; eauto.
        rewrite H2 in H7.
        exfalso.
        inversion H7.
        rewrite H2 in H7.
        exfalso.
        inversion H7.
        (* None *)
        case_eq (find_subtree pathname (TStree ts!!)); intros.
        destruct d.
        rewrite H7 in H5.
        deex.
        erewrite find_subtree_update_subtree_ne_path in H8; eauto.
        eapply find_subtree_update_subtree_file_not_pathname_prefix_1; eauto.
        eapply find_subtree_update_subtree_file_not_pathname_prefix_2; eauto.
        rewrite H2 in H7.
        exfalso.
        inversion H7.
        rewrite H2 in H7.
        exfalso.
        inversion H7.
  Qed.
  Proof.
    intros.
    eapply dir2flatmem2_find_subtree_ptsto in H0 as H0'; eauto.
    repeat rewrite treeseq_one_file_sync_alternative; simpl.
    destruct (list_eq_dec string_dec pathname' pathname); subst; simpl in *.
    - unfold treeseq_safe in *.
      intuition.
      + unfold treeseq_safe_fwd in *; intros; simpl in *.
        intuition.
        specialize (H2 inum0 off bn).
        deex.
        case_eq (find_subtree pathname (TStree (nthd n ts))); intros; simpl.
        destruct d.
        -- (* a file *)
          rewrite H10 in H12; simpl.
          erewrite find_update_subtree in H12; eauto.
          inversion H12.
          subst n0; subst f0; clear H12.
          edestruct H2.
          eexists d.
          intuition.
          intuition.
          rewrite H14.
          exists (synced_dirfile x); eauto.
       -- (* a directory *)
          rewrite H10 in H12; simpl.
          exfalso.
          rewrite H10 in H12.
          inversion H12.
       -- (* None *)
          rewrite H10 in H12; simpl.
          exfalso.
          rewrite H10 in H12.
          inversion H12.
      + unfold treeseq_safe_bwd in *; intros; simpl in *.
        destruct H10.
        specialize (H4 inum0 off bn).
        case_eq (find_subtree pathname (TStree ts!!)); intros; simpl.
        destruct d.
        -- (* a file *)
          rewrite H12 in H10; simpl.
          erewrite find_update_subtree in H10; eauto.
          intuition.
          inversion H13.
          subst n0; subst x.
          clear H13.
          edestruct H4.
          eexists d.
          intuition; eauto.
          deex.
          rewrite H13.
          left.
          exists (synced_dirfile f0).
          erewrite find_update_subtree; eauto.
          right; eauto.
        -- (* a directory *)
          rewrite H12 in H10.
          intuition.
          exfalso.
          rewrite H13 in H12.
          inversion H12.
        -- (* None *)
          rewrite H12 in H10.
          intuition.
          exfalso.
          rewrite H13 in H12.
          inversion H12.
    - (* different pathnames, but pathname' is still safe, if it was safe. *)
      unfold treeseq_safe in *.
      unfold treeseq_pred in H3.
      eapply NEforall_d_in with (x := (nthd n ts)) in H3 as H3'.  
      2: eapply nthd_in_ds.
      unfold tree_rep in H7; destruct_lift H7.
      intuition; simpl.
      + 
        eapply treeseq_safe_fwd_ne; eauto.
        eapply rep_tree_names_distinct; eapply H7.
      + 
        eapply treeseq_safe_bwd_ne; eauto.
        eapply rep_tree_names_distinct; eapply H7.
  Qed.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.file_sync_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H7 as Hpred; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.
    step.

    eapply treeseq_in_ds_file_sync; eauto.
    eapply dir2flatmem2_find_subtree_ptsto in H4 as H4'.
    eassumption.
    distinct_names'.

    unfold ts_file_sync. rewrite d_map_latest.
    unfold treeseq_one_file_sync.
    erewrite dir2flatmem2_find_subtree_ptsto; try eassumption.
    distinct_names'.

    unfold ts_file_sync.
    rewrite d_map_latest.

    eapply treeseq_in_ds_tree_pred_latest in H7 as Hpred; eauto.
    eapply NEforall_d_in'; intros.
    apply d_in_d_map in H8; deex; intuition.
    eapply NEforall_d_in in H6 as H6'; try eassumption.
    eapply d_in_nthd in H9 as H9'; deex.

    msalloc_eq.
    eapply treeseq_sync_safe_sync.
    denote dssync_vecs as Hx; exact Hx.
    all: eauto.
    distinct_names.
    distinct_inodes.

    unfold treeseq_in_ds in H7. intuition.
    eapply NEforall2_d_in  with (x := (nthd n ts)) in H as Hd'; eauto.
    intuition.

    unfold ts_file_sync.
    rewrite d_map_latest.
    unfold treeseq_one_file_sync.
    eapply dir2flatmem2_find_subtree_ptsto in H4 as H4'; eauto.
    rewrite H4'; simpl.
    eapply dir2flatmem2_update_subtree; eauto.
    distinct_names'.
    distinct_names'.
  Qed.
  Proof.
    intros.
    unfold latest.
    simpl; reflexivity.
  Qed.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.tree_sync_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H5 as Hpred; eauto.
    step.

    unfold treeseq_in_ds.
    unfold NEforall2.
    simpl in *.
    split.
    split.
    unfold treeseq_in_ds in H5; intuition;
      eapply NEforall2_latest in H0; intuition.
    eapply treeseq_one_safe_refl.
    unfold treeseq_in_ds in H5; intuition;
      eapply NEforall2_latest in H0; intuition.
    eapply mscs_parts_eq_tree_rep_latest; eauto.
    unfold treeseq_in_ds in H5; intuition.
  Qed.
  Proof.
    unfold treeseq_safe; intuition.

    - unfold treeseq_safe_fwd.
      intros; simpl.
      deex.
      exists f; eauto.
      intuition.
      eapply find_rename_oob; eauto.

      unfold BFILE.block_belong_to_file in *.
      rewrite H5 in *; eauto.

      intro. subst.

      erewrite <- find_subtree_app in H2 by eassumption.
      assert (pathname' = cwd ++ srcbase).
      eapply find_subtree_inode_pathname_unique; eauto.
      congruence.

      intro. subst.
      eapply find_subtree_before_prune in H4.
      deex.
      erewrite <- find_subtree_app in H4 by eassumption.
      assert (pathname' = cwd ++ dstbase).
      eapply find_subtree_inode_pathname_unique; eauto.
      congruence.
      eapply find_subtree_tree_names_distinct; eauto.
      eauto.

      eapply tree_inodes_in_rename_oob; eauto.

    - unfold treeseq_safe_bwd in *.
      intros.
      left.
      repeat deex; intuition.
      denote pathname' as Hp.
      eexists f'; intuition; simpl in *.
      eapply find_rename_oob'. 7: eauto.
      all: auto.
      unfold BFILE.block_belong_to_file in *.
      rewrite H5 in *; eauto.
      -- intro. subst.
        destruct (pathname_decide_prefix cwd pathname').
        + deex.
          erewrite find_subtree_app in Hp by eauto.
          eapply find_subtree_graft_subtree_oob' in Hp.
          2: eauto.
          eapply find_subtree_prune_subtree_oob' in Hp.
          2: eauto.
          assert (srcbase = suffix).
          eapply find_subtree_inode_pathname_unique with (tree := (TreeDir dnum tree_elem)); eauto.
          eapply find_subtree_tree_inodes_distinct; eauto.
          eapply find_subtree_tree_names_distinct; eauto.
          congruence.
          intro; apply H6.  apply pathname_prefix_trim; eauto.
          intro; apply H7.  apply pathname_prefix_trim; eauto.
        + 
          eapply find_subtree_update_subtree_oob' in Hp.
          assert (cwd++srcbase = pathname').

          erewrite <- find_subtree_app in H2 by eauto.
          eapply find_subtree_inode_pathname_unique; eauto.
          contradiction H9; eauto.
          eauto.
      -- intro. subst.
       destruct (pathname_decide_prefix cwd pathname').
        + deex.
          erewrite find_subtree_app in Hp by eauto.
          eapply find_subtree_graft_subtree_oob' in Hp.
          2: eauto.
          eapply find_subtree_prune_subtree_oob' in Hp.
          2: eauto.
          eapply find_subtree_before_prune in H4; eauto.
          deex.
          assert (dstbase = suffix).
          eapply find_subtree_inode_pathname_unique with (tree := (TreeDir dnum tree_elem)); eauto.
          eapply find_subtree_tree_inodes_distinct; eauto.
          eapply find_subtree_tree_names_distinct; eauto.
          congruence.
          eapply find_subtree_tree_names_distinct; eauto.
          intro; apply H6.  apply pathname_prefix_trim; eauto.
          intro; apply H7.  apply pathname_prefix_trim; eauto.
        + 
          eapply find_subtree_update_subtree_oob' in Hp.
          eapply find_subtree_before_prune in H4; eauto.
          deex.
          assert (cwd++dstbase = pathname').
          erewrite <- find_subtree_app in H4 by eauto.
          eapply find_subtree_inode_pathname_unique; eauto.
          contradiction H9; eauto.
          eapply find_subtree_tree_names_distinct; eauto.
          eauto.
      --
        replace inum with (dirtree_inum (TreeFile inum f')) by reflexivity.
        eapply find_subtree_inum_present; eauto.
    - simpl.
      unfold dirtree_safe in *; intuition.
  Qed.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.rename_ok.
    cancel. 
    eapply treeseq_in_ds_tree_pred_latest in H7 as Hpred; eauto.
    eassumption.
    step.

    or_l. cancel. eapply treeseq_in_ds_mscs'; eauto.

    unfold AFS.rename_rep, AFS.rename_rep_inner.
    cancel.
    or_r.

    (* a few obligations need subtree *)
    eapply sep_star_split_l in H4 as H4'.
    destruct H4'.
    eapply dir2flatmem2_find_subtree_ptsto in H8.
    erewrite find_subtree_app in H8.
    2: eassumption.
    erewrite find_subtree_app in H8.
    2: eassumption.
    2: distinct_names'.

    cancel.

    - eapply treeseq_in_ds_pushd; eauto.
      unfold treeseq_one_safe; simpl.
      rewrite H in H11.
      eassumption.

    - eapply treeseq_safe_pushd; eauto.
      eapply NEforall_d_in'; intros.
      eapply NEforall_d_in in H13; eauto.
      eapply treeseq_safe_trans; eauto.

      (* clear all goals mentioning x0 *)
      clear H13 H15 x0.

      eapply treeseq_safe_rename; eauto.
      distinct_names'.
      distinct_inodes'.
      rewrite H in *; eauto.

    - eapply dir2flatmem2_rename; eauto.
      distinct_names'.
      distinct_inodes'.

    - unfold AFS.rename_rep_inner in *.
      xcrash_solve.
      or_l. cancel. xform_normr. cancel.
      or_r. cancel. repeat (progress xform_norm; safecancel).

      eassumption.
      3: reflexivity.
      4: reflexivity.
      3: pred_apply; cancel.

      + eapply treeseq_in_ds_pushd; eauto.
        unfold treeseq_one_safe; simpl.
        rewrite <- surjective_pairing in H11.
        rewrite H0 in H11.
        eassumption.

      + eapply treeseq_safe_pushd; eauto.
        eapply NEforall_d_in'; intros.
        eapply NEforall_d_in in H22; eauto.
        eapply treeseq_safe_trans; eauto.

        eapply treeseq_safe_rename; eauto.
        distinct_names'.
        distinct_inodes'.
        rewrite H0 in *; eauto.

      + eapply dir2flatmem2_rename; eauto.
        distinct_names'.
        distinct_inodes'.
  Qed.
  Proof.
    intros.
    eapply treeseq_safe_pushd; eauto.
    eapply NEforall_d_in'; intros.
    eapply NEforall_d_in in H6; eauto.
    eapply treeseq_safe_trans; eauto.
    unfold treeseq_safe; intuition.
    - unfold treeseq_safe_fwd.
      intros; simpl.
      deex.
      exists f; eauto.
      intuition.

      eapply find_subtree_prune_subtree_oob in H9; eauto.

      unfold BFILE.block_belong_to_file in *.
      rewrite H3 in *; eauto.
      intros; subst.
      assert (pathname' = pathname).
      eapply find_subtree_inode_pathname_unique; eauto.
      congruence.

      replace inum with (dirtree_inum (TreeFile inum f)) by reflexivity.
      eapply find_subtree_inum_present; eauto.

      eapply tree_inodes_in_delete_oob; eauto.

    - unfold treeseq_safe_bwd.
      intros.
      left.
      deex.
      eexists f'; intuition; simpl in *.
      eapply find_subtree_prune_subtree_oob' in H9; eauto. 

      unfold BFILE.block_belong_to_file in *.
      rewrite H3 in *; eauto.
      intros; subst.
      assert (pathname' = pathname).
      eapply find_subtree_inode_pathname_unique with (tree := 
        (update_subtree pathname 
                    (TreeDir dnum 
                     (delete_from_list name tree_elem)) (TStree ts !!))); eauto.

      destruct (TStree ts !!).

      eapply find_subtree_file_dir_exfalso in H2.
      exfalso; eauto.
      eapply tree_inodes_distinct_prune; eauto.
      eapply tree_names_distinct_prune_subtree'; eauto.
      subst.
      erewrite find_update_subtree in H9; eauto.
      congruence.

      apply find_subtree_inum_present in H9; simpl in H9.
      eapply In_incl; eauto.
      eapply incl_appr'.
      eapply incl_count_incl.
      eapply permutation_incl_count.
      eapply tree_inodes_after_prune'; eauto.

      erewrite <- find_subtree_dirlist.
      erewrite <- find_subtree_app with (p0 := pathname); eauto.
      eapply dir2flatmem2_find_subtree_ptsto with (tree := TStree ts !!).
      eauto.
      pred_apply; cancel.

      replace inum with (dirtree_inum (TreeFile inum f')) by reflexivity.
      eapply find_subtree_inum_present; eauto.

    - simpl.
      unfold dirtree_safe in *; intuition.
  Qed.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.delete_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H7 as Hpred; eauto.
    eassumption.
    step.
    or_l. cancel.
    eapply treeseq_in_ds_mscs'; eauto.
    or_r. cancel.

    - eapply treeseq_in_ds_pushd; eauto.
      unfold treeseq_one_safe; simpl.
      rewrite H in H13.
      eassumption.

    - eapply treeseq_safe_delete; eauto.
      distinct_names'.
      distinct_inodes'.
      rewrite H in *.
      eauto.

    - eapply dir2flatmem2_delete_file; eauto; distinct_names'.

    - xcrash_solve.
      or_l. cancel. xform_normr. cancel.
      or_r. cancel. repeat (progress xform_norm; safecancel).
      eassumption.
      3: reflexivity.
      4: reflexivity.
      4: reflexivity.
      3: pred_apply; cancel.
      clear H1. clear H2. clear H.

      + eapply treeseq_in_ds_pushd; eauto.
        unfold treeseq_one_safe; simpl.
        rewrite <- surjective_pairing in H11.
        rewrite H5 in *; eauto.

      + eapply treeseq_safe_delete; eauto.
        distinct_names'.
        distinct_inodes'.
        rewrite H5 in *; eauto.

      + eapply dir2flatmem2_delete_file; eauto; distinct_names'.
  Qed.