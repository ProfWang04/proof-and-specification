  Proof.
    induction t1 using dirtree_ind2; simpl; intros.
    inversion H; subst. inversion H0; subst. econstructor.
      unfold file_crash in *. repeat deex. do 2 eexists. eapply file_crash_trans; eauto.
    inversion H0; subst. inversion H1; subst. constructor. congruence.
    generalize dependent st'. generalize dependent st'0.
    induction tree_ents; simpl; intros.
    - destruct st'; simpl in *; try congruence.
    - destruct st'; destruct st'0; simpl in *; try congruence.
      inversion H6. inversion H8. inversion H. inversion H4. inversion H5. subst; simpl in *.
      constructor; eauto.
      eapply IHtree_ents. eauto.
      all: try match goal with | [ |- Forall2 _ _ _ ] => eauto end.
      all: eauto.
      constructor; eauto.
      constructor; eauto.
  Qed.
  Proof.
    induction tree_ents; simpl; intros.
    - rewrite flist_crash_xform_emp. cancel.
      eassign (@nil (string * dirtree)); cancel.
      constructor.
      constructor.
    - destruct a. rewrite flist_crash_xform_sep_star.
      inversion H; subst.
      rewrite H2.
      rewrite IHtree_ents by eauto.
      cancel.
      eassign ((s, t') :: tree_ents').
      cancel.
      constructor; eauto.
      simpl; congruence.
  Qed.
  Proof.
    induction tree_ents; intros; destruct tree_ents'; simpl in *; try congruence.
    destruct a; destruct p; simpl in *.
    inversion H; clear H.
    inversion H0; clear H0.
    inversion H1; clear H1.
    subst.
    rewrite IHtree_ents; eauto.
  Qed.
  Proof.
    unfold tree_dir_names_pred; intros.
    rewrite flist_crash_xform_exists. norml; unfold stars; simpl.
    rewrite flist_crash_xform_exists. norml; unfold stars; simpl.
    repeat rewrite flist_crash_xform_sep_star.
    repeat rewrite flist_crash_xform_lift_empty.
    rewrite flist_crash_xform_ptsto.
    cancel.
    eapply SDIR.crash_rep; eauto.
    pred_apply.
    apply tree_dir_names_pred'_unchanged; eauto.
  Qed.
  Proof.
    inversion 1; auto.
  Qed.
  Proof.
    inversion 1; auto.
  Qed.
  Proof.
    induction t using dirtree_ind2; simpl; intros.
    - rewrite flist_crash_xform_exists.
      setoid_rewrite flist_crash_xform_sep_star.
      setoid_rewrite flist_crash_xform_ptsto.
      setoid_rewrite flist_crash_xform_lift_empty.
      norml. destruct f'. cancel.
      instantiate (t' := TreeFile inum (mk_dirfile _ _)). cbn. cancel.
      econstructor; eauto.
      unfold file_crash. do 2 eexists. eauto.
    - rewrite flist_crash_xform_sep_star.
      rewrite flist_crash_xform_dirlist_pred by eauto.
      cancel.
      eassign (TreeDir inum tree_ents').
      cancel.
      apply flist_crash_xform_tree_dir_names_pred; eauto.
      eapply Forall2_to_map_eq. apply tree_crash_preserves_dirtree_inum. eauto.
      eapply Forall2_to_map_eq. apply tree_crash_preserves_dirtree_isdir. eauto.
      constructor; eauto.
  Qed.
  Proof.
    unfold IAlloc.Alloc.rep, IAlloc.Alloc.Alloc.rep; intros.
    cancel.
    match goal with H: _ <=p=> _ |- _ => rewrite H end.
    repeat match goal with
      Hb: context [BFILE.file_crash],
      Hother: _ |- _ => clear Hother
    end.
    induction frees; simpl.
    rewrite flist_crash_xform_emp; auto.
    rewrite flist_crash_xform_sep_star. rewrite flist_crash_xform_exists.
    rewrite IHfrees.
    norml; unfold stars; simpl.
    rewrite flist_crash_xform_sep_star.
    rewrite flist_crash_xform_lift_empty.
    rewrite flist_crash_xform_ptsto. cancel. eauto.
  Qed.
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite BFILE.xform_rep.
    rewrite IAlloc.xform_rep.
    rewrite flist_crash_xform_freelist.
    norml; unfold stars; simpl.
    eapply flist_crash_flist_crash_xform in H0; eauto.
    apply flist_crash_xform_sep_star in H0. rewrite flist_crash_xform_sep_star in H0.
    rewrite flist_crash_xform_tree_pred in H0.
    destruct_lift H0.
    unfold IAlloc.rep; cancel.
    rewrite <- BFILE.rep_clear_freelist.
    rewrite <- BFILE.rep_clear_icache.
    rewrite <- IAlloc.rep_clear_cache.
    cancel.
    eauto.
    pred_apply.
    cancel; auto.
    intros; eapply BFILE.freepred_file_crash; eauto.
  Grab Existential Variables.
    all: exact (LOG.mk_memstate0 (Cache.BUFCACHE.cache0 1)).
  Qed.
  Proof.
    induction fnlist.
    - simpl; intros.
      eexists; intuition eauto.
      inversion H0; subst; auto.
    - intros.
      inversion H0.
      destruct t; try congruence.
      inversion H; subst.
      generalize dependent st'.
      induction l; intros.
      + simpl in *. congruence.
      + destruct st'; try solve [ simpl in *; congruence ].
        destruct p.
        unfold find_subtree_helper in H2 at 1.
        destruct a0.
        simpl in H2.
        destruct (string_dec s0 a).
        * subst.
          edestruct IHfnlist.
          2: apply H2.
          inversion H6; eauto.
          eexists.
          intuition eauto.
          inversion H4; subst.
          simpl; destruct (string_dec s s); try congruence.
        * edestruct IHl.

          eauto.
          eauto.
          all: try solve [ inversion H4; exact H5 ].
          all: try solve [ inversion H6; eauto ].

          constructor. inversion H4; eauto.
          inversion H. inversion H8; eauto.

          exists x. intuition.
          simpl.
          inversion H4; subst. destruct (string_dec s a); try congruence.
          apply H3.
  Qed.
  Proof.
    induction fnlist.
    - simpl; intros.
      congruence.
    - intros.
      inversion H0. rewrite H2.
      destruct t; inversion H; subst.
      eauto.

      generalize dependent st'.
      induction l; intros.
      + destruct st'; simpl in *; try congruence.
      + destruct st'; try solve [ simpl in *; congruence ].
        destruct p.
        unfold find_subtree_helper in H2 at 1.
        destruct a0.
        simpl in H2.
        destruct (string_dec s0 a).
        * subst.
          edestruct IHfnlist.
          2: apply H2.
          inversion H6; eauto.
          inversion H4; subst.
          simpl; destruct (string_dec s s); try congruence.
        * edestruct IHl.

          eauto.
          eauto.
          all: try solve [ inversion H4; exact H5 ].
          all: try solve [ inversion H6; eauto ].

          constructor. inversion H4; eauto.
          inversion H. inversion H8; eauto.

          simpl.
          inversion H4; subst. destruct (string_dec s a); try congruence.
  Qed.
  Proof.
    intros.
    destruct t.
    - destruct H0.
      inversion H0.
    - destruct H0.
      unfold find_subtree in *. simpl in *.
      destruct t'.
      inversion H0.
      inversion H0.
      subst; simpl.
      exfalso.
      inversion H.
      inversion H0.
      subst; simpl.
      inversion H.
      subst; simpl; eauto.
  Qed.
  Proof.
    intros.
    destruct t.
    - unfold find_name in H0; subst; simpl.
      unfold find_subtree in H0.
      inversion H0.
    - destruct t'.
      unfold find_name in H0.
      destruct (find_subtree [] (TreeDir n l)).
      destruct d.
      inversion H0.
      inversion H0.
      subst; simpl.
      exfalso.
      inversion H.
      congruence.
      inversion H.
      subst; simpl; eauto.
  Qed.
  Proof.
    unfold BFILE.file_crash; intros.
    eexists.
    exists (map fst (BFILE.BFData file)).
    intuition.
    split; intros.
    rewrite map_length; eauto.
    unfold vsmerge. constructor.
    erewrite selN_map; eauto.
  Qed.
  Proof.
    induction tree using dirtree_ind2; intros.
    edestruct file_crash_exists as [ [] H].
    eexists (TreeFile _ (mk_dirfile _ _)).
    econstructor; cbn. unfold file_crash. do 2 eexists. eauto.
    induction tree_ents.
    eexists; constructor; eauto. constructor.
    destruct a; simpl in *.
    inversion H.
    edestruct IHtree_ents; eauto.
    inversion H4.
    repeat deex.
    exists (TreeDir inum ((s, tree') :: st')).
    constructor. simpl; f_equal; auto.
    constructor; auto.
  Unshelve.
    exact None.
  Qed.
  Proof.
    induction pn; simpl; intros; eauto.
    destruct tree; simpl in *.
    - inversion H; subst. eauto.
    - inversion H; subst. constructor; eauto.
      + generalize dependent st'.
        induction l; simpl; intros; destruct st'; simpl in *; try congruence.
        inversion H; subst.
        inversion H6; subst.
        inversion H7; subst.
        f_equal.
        destruct a0; destruct p; simpl in *. rewrite H2 in *; clear H2.
        destruct (string_dec s0 a); subst; simpl in *; auto.
        apply IHl; try eassumption. constructor; eauto.
      + generalize dependent st'.
        induction l; simpl; intros; destruct st'; simpl in *; try congruence.
        inversion H; subst.
        inversion H6; subst.
        inversion H7; subst.
        constructor.
        destruct a0; destruct p; simpl in *. rewrite H2 in *; clear H2.
        destruct (string_dec s0 a); subst; simpl in *; auto.
        eapply IHl; try eassumption. constructor; eauto.
  Qed.
  Proof.
    induction t using dirtree_ind2; simpl in *; intros.
    inversion H; constructor.
    inversion H0; subst.
    inversion H1; subst.
    constructor; try congruence.
    eapply forall_forall2_l in H; try ( eapply forall2_length; eauto ).
    eapply forall_forall2_l in H5; try ( eapply forall2_length; eauto ).
    eapply forall2_forall_r; try ( eapply forall2_length; eauto ).
    eapply forall2_impl. apply H.
    eapply forall2_impl. apply H5.
    eapply forall2_impl. apply H6.
    apply forall2_lift; try ( eapply forall2_length; eauto ).
    intros; eauto.
  Qed.
  Proof.
    induction t using dirtree_ind2; simpl; intros.
    - inversion H; subst. constructor.
    - inversion H0; subst.
      generalize dependent st'.
      induction tree_ents; intros; destruct st'; simpl in *; try congruence.
      destruct a. destruct p.
      inversion H5; subst.
      inversion H; subst.
      repeat rewrite cons_app with (l := app _ _).
      eapply permutation_trans. apply permutation_app_comm. rewrite <- app_assoc.
      eapply permutation_trans. 2: apply permutation_app_comm. rewrite <- app_assoc.
      eapply permutation_app_split. eauto.
      eapply permutation_trans. apply permutation_app_comm.
      eapply permutation_trans. 2: apply permutation_app_comm.
      eapply IHtree_ents; eauto.
      constructor; eauto.
      inversion H0; subst. inversion H10; subst. eauto.
      inversion H0; subst. inversion H10; subst. eauto.
  Qed.
  Proof.
    unfold tree_inodes_distinct; intros.
    eapply NoDup_incl_count; eauto.
    eapply permutation_incl_count.
    apply permutation_comm.
    eapply tree_crash_tree_inodes_permutation; eauto.
  Qed.
  Proof.
    induction pn; simpl; intros.
    {
      edestruct (tree_crash_exists tree). do 2 eexists; intuition eauto.
    }
    destruct tree; simpl in *.
    {
      inversion H0; subst.
      edestruct (tree_crash_exists subtree). do 2 eexists; intuition eauto.
    }
    inversion H0; clear H0; subst.
    generalize dependent st'.
    induction l; simpl; intros; destruct st'; simpl in *; try congruence.
    {
      edestruct (tree_crash_exists subtree). do 2 eexists; intuition eauto.
      constructor; eauto. auto.
    }
    destruct a0; destruct p; simpl in *.
    inversion H3; clear H3; subst.
    inversion H5; clear H5; subst.
    destruct (string_dec s a); subst; simpl in *.
    {
      clear IHl.
      edestruct IHpn. 2: eauto. eauto. deex.
      exists (TreeDir n ((a, x) :: st')). simpl. destruct (string_dec a a); try congruence. eexists.
      inversion H. inversion H8. subst.
      rewrite update_subtree_notfound with (l := l) in *; eauto.
      intuition eauto.
      constructor; simpl. f_equal; eauto. eauto.

      rewrite update_subtree_notfound; eauto.
      eapply tree_crash_tree_names_distinct in H.
      2: eapply TCDir with (st' := (a, x) :: st').
      inversion H. inversion H10; eauto.
      simpl. f_equal. eauto.
      constructor. eauto. eauto.
    }
    {
      clear IHpn.
      edestruct IHl; clear IHl; eauto. deex.
      destruct x; simpl in *; try congruence.
      exists (TreeDir n ((s, d0) :: l0)). eexists.
      inversion H1; subst.
      intuition eauto. constructor; simpl. f_equal. auto. constructor; eauto.
      simpl. destruct (string_dec s a); try congruence.
    }
  Qed.
  Proof.
    unfold file_crash; intros.
    repeat deex.
    eapply BFILE.file_crash_data_length in H; simpl in *.
    eauto.
  Qed.
  Proof.
    unfold file_crash, synced_dirfile; intros.
    repeat deex.
    edestruct BFILE.file_crash_synced; eauto.
    pose proof (BFILE.fsynced_synced_file (BFILE.mk_bfile (DFData f) (DFAttr f) c)).
    unfold BFILE.synced_file in H0; simpl in *.
    eauto.

    destruct f'; simpl in *.
    subst; eauto.
  Qed.
  Proof.
    unfold file_crash; intros.
    edestruct (file_crash_exists (BFILE.mk_bfile (DFData f) (DFAttr f) None)).
    destruct x.
    exists (mk_dirfile BFData BFAttr).
    do 2 eexists.
    simpl; eauto.
  Qed.