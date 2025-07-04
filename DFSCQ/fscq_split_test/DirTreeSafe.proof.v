  Proof.
    unfold dirtree_safe; intuition eauto.
    apply BFILE.ilist_safe_refl.
  Qed.
  Proof.
    unfold dirtree_safe; intros.
    intuition.
    eapply BFILE.ilist_safe_trans; eauto.
    edestruct H3; eauto.
    - intuition; repeat deex. 
      edestruct H2; eauto.
    - right.
      unfold BFILE.ilist_safe in *.
      unfold BFILE.block_is_unused in *; eauto.
      intuition.
  Qed.
  Proof.
    unfold dirtree_safe; intuition.
    apply BFILE.ilist_safe_refl.
    left; split; auto.
    exists pathname. eexists.
    destruct pathname; simpl in *; try congruence.
    inversion H.
    subst; eauto.
  Qed.
  Proof.
    unfold dirtree_safe, BFILE.ilist_safe; intuition.
    specialize (H3 _ _ _ H5); intuition.
    specialize (H4 _ _ _ H6); intuition.
    eapply H2; eauto.
  Qed.
  Proof.
    intros; apply dirtree_safe_ilist_trans; auto.
    apply dirtree_safe_file.
  Qed.
  Proof.
    unfold dirtree_safe; intuition.
    destruct (pathname_decide_prefix pathname pathname0); repeat deex.
    - edestruct H2; eauto.
      eapply find_subtree_helper1. 2: eauto. eauto.
      left; intuition. repeat deex.
      do 2 eexists.
      erewrite find_subtree_app; eauto.
    - clear H2.
      unfold BFILE.ilist_safe in H0.
      destruct H1.
      specialize (H2 _ _ _ H3).
      intuition.
      left.
      intuition.
      exists pathname0; eexists.
      erewrite <- find_subtree_update_subtree_oob'; eauto.
  Qed.
  Proof.
    intros.
    unfold dirtree_safe, BFILE.ilist_safe in H1.
    intuition.
    specialize (H4 _ _ _ _ _ H H0).
    intuition; repeat deex.
    - (**
       * The block still belongs to the same inode in this earlier disk.
       *)
      eexists; split.
      2: right; intuition.
      eapply dirtree_update_block; eauto.
      eauto.
    - (**
       * The block is now in the free list.
       *)
      eexists; split.
      2: left; reflexivity.
      eapply dirtree_update_free; eauto.
  Qed.
  Proof.
    intros; destruct v.
    edestruct dirtree_update_safe_inum; eauto.
    intuition; subst; eauto.
    destruct (in_dec addr_eq_dec inum (tree_inodes tree)).
    - (* inum is in the tree.. *)
      edestruct tree_inodes_pathname_exists; eauto; repeat deex.
      eapply rep_tree_names_distinct; eauto.
      eapply rep_tree_inodes_distinct; eauto.
      destruct (lt_dec off (length (DFData f'))).
      + (* in-bounds write *)
        erewrite dirtree_update_inode_update_subtree in H4; eauto.
        eexists; split.
        eauto.
        right; eauto.
        eapply rep_tree_inodes_distinct; eauto.
        eapply rep_tree_names_distinct; eauto.
      + (* out-of-bounds write *)
        erewrite dirtree_update_inode_oob in H4; eauto.
        eapply rep_tree_inodes_distinct; eauto.
        eapply rep_tree_names_distinct; eauto.
    - (* inum is not in the tree *)
      repeat deex.
      erewrite dirtree_update_inode_absent in H4 by eauto.
      eauto.
  Qed.
  Proof.
    intros.
    edestruct dirtree_update_safe_pathname; eauto.
    intuition.
    eapply pimpl_apply; try eassumption. cancel.
    eapply pimpl_apply; try eassumption. cancel.
  Qed.
  Proof.
    unfold dirtree_safe, BFILE.ilist_safe; intuition.
    specialize (H1 _ _ _ H2); destruct H1.
    2: right; intuition.
    left; intuition.

    (**
     * Need to prove that the new directory's filename didn't change the existing
     * pathname for [inum0].  This should follow from the fact that the new inode
     * corresponds to a directory, not a file.
     **)
    destruct pathname; simpl in *; try congruence.
    destruct (string_dec name s); subst; eauto.
    destruct pathname; simpl in *; try congruence.
    exists (s :: pathname). eexists. eauto.
  Qed.
  Proof.
    unfold dirtree_safe, BFILE.ilist_safe; intuition.
    denote (forall _, _ ) as Hx; denote (BFILE.block_belong_to_file) as Hy.
    specialize (Hx _ _ _ Hy); destruct Hx.
    2: right; intuition.  (* Unused block. *)
    destruct pathname.
    simpl in *; congruence.

    denote tree_names_distinct as Hz; inversion Hz; subst.
    apply find_subtree_ents_rev_nodup in H1.
    rewrite rev_app_distr in H1; simpl in *.
    destruct (string_dec name s); subst; eauto.

    - (* Same filename; contradiction because the file is empty *)
      exfalso.
      destruct pathname; simpl in *; try congruence.

      inversion H1; subst.
      unfold BFILE.rep in H; destruct_lift H.
      unfold BFILE.block_belong_to_file in Hy; intuition subst.
      extract.
      eapply list2nmem_sel in H0; rewrite <- H0 in *.
      setoid_rewrite ListPred.listmatch_length_pimpl in H at 2.
      destruct_lift H; rewrite map_length in *.
      denote (0 = _) as Heq; rewrite <- Heq in *.
      denote (off < _) as Hlt; inversion Hlt.
    - (* Different filename *)
      left; intuition.
      do 2 eexists.
      rewrite <- rev_involutive with (l := tree_elem).
      apply find_subtree_ents_rev_nodup.
      rewrite map_rev.
      apply NoDup_rev_1; auto.
      eassign (s :: pathname); simpl; eauto.

    - rewrite map_app; simpl.
      apply NoDup_app_comm; simpl.
      constructor; auto.

    Unshelve. all: eauto; exact unit.
  Qed.
  Proof.
    unfold dirtree_safe; intros.
    intuition.
    specialize (H2 _ _ _ _ _ H H3).
    intuition; repeat deex.
    left; intuition.
    destruct (list_eq_dec string_dec pathname pathname'); subst.
    - rewrite H4 in H0. inversion H0.
      repeat eexists.
      erewrite find_update_subtree; eauto.
    - repeat eexists.
      erewrite find_subtree_update_subtree_ne_file; eauto.
  Qed.
  Proof.
    unfold dirtree_safe; intuition.
    unfold BFILE.ilist_safe in *; intuition.
    specialize (H4 _ _ _ H2); intuition.
    left; split; auto.
    repeat eexists.
    eapply find_subtree_delete'; eauto.
    inversion H; auto.
  Qed.
  Proof.
    cbn; intros.
    eapply dirtree_safe_ilist_trans; eauto.
    unfold dirtree_safe; intuition.
    apply BFILE.ilist_safe_refl.
    left; split; auto.

    destruct (pathname_decide_prefix (dstpath ++ [dstname]) pathname).
    - repeat deex.
      exists (srcpath ++ [srcname] ++ suffix); exists f.
      denote tree_graft as Hx.
      rewrite <- app_assoc in Hx.
      erewrite find_subtree_app in Hx by (
        erewrite <- tree_graft_not_in_dirents by auto;
        eapply find_update_subtree; eauto).

      erewrite find_subtree_app by eauto.
      erewrite find_subtree_app.

      2: apply find_dirlist_find_subtree_helper; eauto.
      erewrite find_subtree_app in Hx; eauto.
      apply find_subtree_leaf_in.
      apply in_app_iff.
      right; simpl; auto.
      rewrite map_app; apply NoDup_app_comm; simpl.
      constructor; auto.

      eapply tree_names_distinct_nodup.
      eapply tree_names_distinct_prune_subtree; eauto.
      eapply tree_names_distinct_nodup.
      eapply tree_names_distinct_subtree; eauto.

    - exists pathname, f.
      destruct (pathname_decide_prefix dstpath pathname).
      + (* in dstpath, but not in dstpath/dstname *)
        deex.
        eapply find_subtree_rename_oob; eauto.
        intro.
        eapply H8.
        unfold pathname_prefix in H9.
        deex.
        exists suffix0.
        rewrite app_assoc; eauto. 
      + (* not in dstpath *)
        apply find_subtree_update_subtree_oob' in H6; auto.
        unfold tree_prune, delete_from_dir in H6.
        destruct (pathname_decide_prefix (srcpath++[srcname]) pathname); repeat deex.
        * (* srcpath++srcname is a prefix of pathname *)
          exfalso.
          erewrite <- app_assoc in H6.
          erewrite find_update_subtree_suffix in H6; eauto.
          rewrite <- cons_app in H6.
          rewrite find_subtree_delete_same' in H6; try congruence.
          eapply tree_names_distinct_nodup.
          eapply tree_names_distinct_subtree; eauto.
        * (* pathname outside of srcpath++srcname and dst tree, but maybe in srcpath *)
          erewrite find_subtree_rename_oob_srcname_dst.
          3: eapply pathname_prefix_neq with (path' := (dstpath++[dstname])); eauto.
          all: eauto.
  Qed.
  Proof.
    cbn; intros.
    eapply dirtree_safe_ilist_trans; eauto.
    unfold dirtree_safe; intuition.
    apply BFILE.ilist_safe_refl.
    left; split; auto.
    destruct (pathname_decide_prefix (dstpath ++ [dstname]) pathname).
    - repeat deex.
      exists (srcpath ++ [srcname] ++ suffix); exists f.
      denote tree_graft as Hx.
      rewrite <- app_assoc in Hx.
      unfold tree_graft, tree_prune, add_to_dir in Hx.
      erewrite find_update_subtree_suffix in Hx; eauto.
      rewrite <- cons_app in Hx.
      erewrite find_subtree_add_to_dir_same in Hx.
      erewrite find_subtree_app; eauto.
      erewrite find_subtree_app; eauto.
      apply find_dirlist_find_subtree_helper; eauto.
      eapply tree_names_distinct_nodup with (dnum := n).
      eapply tree_names_distinct_subtree; eauto.
    - exists pathname, f.
      destruct (pathname_decide_prefix dstpath pathname).
      + (* in dstpath, but not in dstpath/dstname *)
        deex.
        eapply find_subtree_rename_oob; eauto.
        intro.
        eapply H8.
        unfold pathname_prefix in H9.
        deex.
        exists suffix0.
        rewrite app_assoc; eauto.          
      + (* not in dstpath *)
        apply find_subtree_update_subtree_oob' in H6; auto.
        unfold tree_prune, delete_from_dir in H6.
        destruct (pathname_decide_prefix (srcpath++[srcname]) pathname); repeat deex.
        * (* srcpath++srcname is a prefix of pathname *)
          exfalso.
          erewrite <- app_assoc in H6.
          erewrite find_update_subtree_suffix in H6; eauto.
          rewrite <- cons_app in H6.
          rewrite find_subtree_delete_same' in H6; try congruence.
          eapply tree_names_distinct_nodup.
          eapply tree_names_distinct_subtree; eauto.
        * (* pathname outside of srcpath++srcname and dst tree, but maybe in srcpath *)
          erewrite find_subtree_rename_oob_srcname_dst.
          3: eapply pathname_prefix_neq with (path' := (dstpath++[dstname])); eauto.
          all: eauto.
    - unfold dirtree_safe in *; eapply BFILE.ilist_safe_trans; intuition eauto.
  Qed.
   Proof.
    unfold dirtree_safe; intuition.
    destruct (pathname_decide_prefix pathname p); repeat deex.
    {
      destruct suffix; try rewrite app_nil_r in *.
      - erewrite find_update_subtree in H0 by eauto. inversion H0; subst. eauto.
      - case_eq (find_subtree pathname tree); intros. destruct d.
        + erewrite find_subtree_app in H1 by eauto; simpl in *; congruence.
        + erewrite find_subtree_app in H1 by eauto.
          erewrite update_subtree_app in H0 by eauto.
          erewrite find_update_subtree in H0 by eauto.
          simpl in *; congruence.
        + erewrite find_subtree_app_none in H1 by eauto; congruence.
    }

    destruct (pathname_decide_prefix p pathname); repeat deex.
    {
      exfalso.
      destruct suffix; try rewrite app_nil_r in *.
      apply H5. exists nil. rewrite app_nil_r; auto.
      erewrite find_subtree_app in H0.
      2: erewrite find_update_subtree; eauto.
      simpl in *; congruence.
    }

    rewrite find_subtree_update_subtree_ne_path in H0; eauto.
  Qed.