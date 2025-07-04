  Proof.
    intros. 
    rewrite cons_app.
    unfold dirlist_combine; subst; simpl.
    destruct a.
    rewrite app_nil_r; eauto.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    split; destruct a.
    destruct (string_dec s name); subst.
    edestruct H. eauto.
    cancel. apply IHl; auto.

    destruct (string_dec s name); subst.
    edestruct H. eauto.
    cancel. apply IHl; auto.
  Qed.
  Proof.
    split; induction l1; simpl; intros.
    cancel.
    destruct a; destruct d; cancel; eauto.
    cancel.
    destruct a; destruct d; cancel; rewrite sep_star_comm; eauto.
  Qed.
  Proof.
    induction l; simpl; intros.
    constructor.
    destruct a; simpl in *.
    destruct d.
    - constructor; [| eapply IHl; pred_apply' H; cancel ].
      intro Hin.
      apply in_map_iff in Hin. repeat deex. destruct x.
      apply in_split in H2. repeat deex.
      eapply ptsto_conflict_F with (a := s). pred_apply' H.
      rewrite tree_dir_names_pred'_app. simpl.
      destruct d; cancel.
    - constructor; [| eapply IHl; pred_apply' H; cancel ].
      intro Hin.
      apply in_map_iff in Hin. repeat deex. destruct x.
      apply in_split in H2. repeat deex.
      eapply ptsto_conflict_F with (a := s). pred_apply' H.
      rewrite tree_dir_names_pred'_app. simpl.
      destruct d; cancel.
      cancel.
  Qed.
  Proof.
    unfold tree_dir_names_pred; intros.
    cancel; eauto.
    eapply dir_names_distinct'.
    pred_apply' H1. cancel.
  Qed.
  Proof.
    induction a; simpl; intros.
    - split. cancel. cancel.
    - destruct a. split.
      cancel. apply IHa.
      cancel. rewrite IHa. cancel.
  Qed.
  Proof.
    induction fnlist; simpl; intros.
    - inversion H; subst. cancel.
    - destruct tree; try discriminate; simpl.
      rewrite dir_names_distinct at 1.
      cancel.
      induction l; simpl in *; try discriminate.
      destruct a0; simpl in *.
      destruct (string_dec s a); subst.
      + rewrite sep_star_assoc_2.
        rewrite sep_star_comm with (p1 := tree_pred xp subtree).
        rewrite IHfnlist; eauto.
        cancel.
        apply dirlist_pred_except_notfound; eauto.
        inversion H4; eauto.
      + cancel.
        rewrite sep_star_comm.
        eapply H0.
        inversion H4; eauto.
  Qed.
  Proof.
    induction fnlist; simpl; intros.
    - inversion H; subst. cancel.
    - destruct tree; try discriminate; simpl.
      rewrite dir_names_distinct at 1; cancel.
      induction l; simpl in *; try discriminate.
      destruct a0; simpl in *.
      destruct (string_dec s a); subst.
      + rewrite IHfnlist; eauto.
        cancel.
        apply dirlist_pred_except_notfound.
        inversion H3; eauto.
      + cancel.
        inversion H3; eauto.
  Qed.
  Proof.
    induction l; intros.
    - simpl in *. apply ptsto_valid' in H. congruence.
    - destruct a. destruct d. simpl in *.
      + apply ptsto_mem_except in H0 as H0'.
        rewrite IHl. cancel.
        eassign s0; eassign inum; cancel.

        apply sep_star_comm in H.
        pose proof (ptsto_diff_ne H0 H).
        destruct (string_dec s name). exfalso. apply H2; eauto. congruence. eauto.

        2: eauto.
        apply sep_star_comm in H.
        pose proof (ptsto_diff_ne H0 H).
        destruct (string_dec name s). exfalso. apply H1; eauto.
        congruence.
        apply sep_star_comm.
        eapply ptsto_mem_except_exF; eauto.
      + destruct (string_dec name s); subst.
        * apply ptsto_valid in H0. apply ptsto_valid' in H.
          rewrite H in H0. inversion H0. subst.
          cancel. instantiate (s0 := l0). cancel.
          destruct (string_dec s s); congruence.
        * apply ptsto_mem_except in H0. simpl.
          rewrite IHl. cancel.
          eassign s0; eassign inum; cancel.
          destruct (string_dec s name); try congruence; eauto.
          2: eauto.
          apply sep_star_comm. eapply ptsto_mem_except_exF; eauto.
          pred_apply; cancel.
  Qed.
  Proof.
    induction l; intros.
    - simpl in *. apply ptsto_valid' in H. congruence.
    - destruct a. destruct d; simpl in *.
      + destruct (string_dec name s); subst.
        * apply ptsto_valid in H0. apply ptsto_valid' in H.
          rewrite H in H0; inversion H0. subst. cancel.
          destruct (string_dec s s); congruence.
        * apply ptsto_mem_except in H0.
          rewrite IHl with (inum:=inum). cancel.
          destruct (string_dec s name); try congruence; eauto.
          2: eauto.
          apply sep_star_comm. eapply ptsto_mem_except_exF.
          pred_apply; cancel. congruence.
      + apply ptsto_mem_except in H0 as H0'.
        rewrite IHl with (inum:=inum). cancel.

        apply sep_star_comm in H.
        pose proof (ptsto_diff_ne H0 H).
        destruct (string_dec s name). exfalso. apply H2; eauto. congruence. eauto.

        2: eauto.
        apply sep_star_comm in H.
        pose proof (ptsto_diff_ne H0 H).
        destruct (string_dec name s). exfalso. apply H1; eauto.
        congruence.
        apply sep_star_comm. eapply ptsto_mem_except_exF; eauto.
  Qed.
  Proof.
    induction dlist; simpl; intros.
    apply ptsto_valid' in H. congruence.
    destruct a. unfold find_subtree_helper at 1.
    destruct (string_dec s name); subst.
    - apply ptsto_valid' in H. apply ptsto_valid in H0.
      rewrite H in H0; inversion H0.
      destruct d. simpl in *; subst; f_equal.
      destruct_lift H1; destruct_lift H2.
      apply sep_star_assoc_1 in H1.
      setoid_rewrite sep_star_comm in H1.
      apply sep_star_assoc_2 in H1.
      apply ptsto_valid' in H1. apply ptsto_valid' in H2.
      rewrite H1 in H2. inversion H2. subst; auto.
      destruct d; destruct bfsub; simpl in *; congruence.
      simpl in H0; congruence.
    - simpl in *.
      eapply IHdlist. exact inum.
      apply sep_star_comm. eapply ptsto_mem_except_exF.
      apply sep_star_comm; eauto. eauto.
      apply ptsto_mem_except in H0; eauto. 2: eauto.
      pred_apply' H1; cancel.
  Qed.
  Proof.
    intros; unfold find_name.
    erewrite find_subtree_file; eauto.
  Qed.
  Proof.
    induction l; simpl; intros.
    - left. intuition.
    - destruct a; simpl in *.
      destruct (string_dec s name); subst.
      + right.
        apply ptsto_valid in H0.
        destruct d; simpl in *.
        * left. do 2 eexists. intuition eauto.
        * right. do 3 eexists. intuition eauto.
          pred_apply. cancel.
      + apply ptsto_mem_except in H0.
        edestruct IHl with (m:=m) (rec:=rec) (name:=name); eauto.
        pred_apply. cancel.
        eassign F'. cancel.
        * left. intuition. unfold mem_except in *. destruct (string_dec name s); congruence.
        * right. unfold mem_except in *. destruct (string_dec name s); congruence.
  Qed.
  Proof.
    unfold find_name.
    induction fnlist; simpl; intros; auto.
    assert (H' := H); assert (H0' := H0).
    unfold tree_dir_names_pred in H, H0.
    destruct_lift H; destruct_lift H0.
    apply ptsto_valid' in H. apply ptsto_valid' in H0.
    rewrite H in H0; inversion H0; subst.
    pose proof (SDIR.rep_mem_eq H6 H9); subst.
    edestruct (find_subtree_helper_dec xp l0 a) with (F:=A) (rec:=find_subtree fnlist) as [HA|HA'];
      edestruct (find_subtree_helper_dec xp l1 a) with (F:=B) (rec:=find_subtree fnlist) as [HB|HB']; eauto;
      try destruct HA'; try destruct HB'; repeat deex; intuition; try congruence.
    - rewrite H1; rewrite H3. auto.
    - rewrite H4; rewrite H11.
      rewrite H3 in H2. inversion H2; subst.
      destruct fnlist; simpl; eauto.
    - rewrite H2; rewrite H1.
      rewrite H3 in H4. inversion H4; subst.
      eauto.
  Qed.
  Proof.
    unfold find_name.
    unfold find_subtree; fold find_subtree.
    induction dlist; simpl; intros.
    congruence.
    destruct a. unfold find_subtree_helper at 1.
    destruct (string_dec s name); subst.
    - destruct d; simpl in *.
      apply ptsto_valid in H0; rewrite H0 in *; congruence.
      apply ptsto_valid in H0. rewrite H0 in H; inversion H; subst.
      eapply find_name_subdir'' with (xp := xp).
      pred_apply' H1. cancel.
      pred_apply' H2. cancel.
    - apply ptsto_mem_except in H0.
      eapply IHdlist.
      2: eauto.
      unfold mem_except; destruct (string_dec name s); congruence.
      pred_apply' H1. cancel.
      pred_apply' H2. cancel.
  Qed.
  Proof.
    intros. apply ptsto_valid' in H.
    eapply find_name_subdir'; eauto.
  Qed.
  Proof.
    induction dlist; simpl; intros; auto.
    destruct a. unfold find_subtree_helper at 1.
    destruct (string_dec s name); subst.
    apply ptsto_valid in H0. congruence.
    eapply notindomain_mem_except' in H.
    apply ptsto_mem_except in H0.
    simpl in *. eapply IHdlist; eauto.
  Qed.
  Proof.
    unfold find_name; intros.
    erewrite find_subtree_none; eauto.
  Qed.
  Proof.
    induction ents; simpl; intros; auto.
    destruct a; simpl in *; intuition; subst.
    apply sep_star_assoc in H.
    apply ptsto_valid in H; congruence.
    eapply IHents; eauto.
    pred_apply' H; cancel.
  Qed.
  Proof.
    intros.
    eapply dirname_not_in'; eauto.
    pred_apply' H; cancel.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    apply emp_mem_except; auto.
    destruct a.
    destruct (string_dec s name); subst.
    apply ptsto_mem_except in H; auto.
    simpl.
    eapply ptsto_mem_except_F; eauto.
  Qed.
  Proof.
    destruct dlist; simpl; intros; auto.
    unfold tree_dir_names_pred.
    cancel; eauto.
    apply emp_mem_except; eauto.

    destruct p.
    destruct (string_dec s name); subst.
    apply ptsto_mem_except in H.
    unfold tree_dir_names_pred.
    cancel; eauto.

    unfold tree_dir_names_pred; simpl.
    cancel; eauto.
    eapply ptsto_mem_except_F; eauto; intros.
    apply dir_names_pred_delete'; auto.
  Qed.
  Proof.
    induction dlist; simpl; intros; auto.
    destruct_lift H0.
    apply ptsto_valid in H0; congruence.

    destruct a.
    destruct (string_dec s name); subst.
    destruct_lift H0.
    apply ptsto_valid in H.
    apply ptsto_valid in H0.
    rewrite H in H0; inversion H0.
    destruct d; simpl in *; try congruence.
    cancel.

    simpl.
    apply ptsto_mem_except in H.
    rewrite <- sep_star_assoc.
    rewrite IHdlist with (inum:=inum); eauto.
    cancel.
    eapply ptsto_mem_except_exF; eauto.
  Qed.
  Proof.
    intros; destruct l; simpl in *; auto.
    destruct p.
    apply ptsto_valid in H1; congruence.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    destruct a; inversion H; subst.
    destruct (string_dec s name); subst.
    rewrite dirlist_pred_except_notfound with (fnlist := nil); eauto.
    split; cancel.
    split; cancel; apply IHl; auto.
  Qed.
  Proof.
    intros.
    apply pimpl_star_emp in H.
    apply dir_names_distinct' in H.
    split; apply dirlist_pred_except_delete_eq'; eauto.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    destruct_lift H0.
    apply ptsto_valid in H0; congruence.

    destruct a.
    destruct (string_dec s name); subst; eauto.
    apply ptsto_valid in H; apply ptsto_valid in H0.
    rewrite H in H0; inversion H0; subst; eauto.

    apply ptsto_mem_except in H.
    eapply IHl; eauto.
    eapply ptsto_mem_except_exF; eauto.
  Qed.
  Proof.
    intros; destruct_lift H.
    eapply find_dirlist_exists'; eauto.
    pred_apply; cancel.
  Qed.
  Proof.
    induction l; simpl; intros; try congruence.
    destruct a. destruct (string_dec s name).

    inversion H; inversion H0; subst.
    erewrite dirlist_pred_except_notfound with (name := name); eauto.
    instantiate (1 := nil); cancel.

    inversion H0; subst; clear H0.
    rewrite <- sep_star_assoc.
    setoid_rewrite <- sep_star_comm at 3.
    rewrite sep_star_assoc.
    rewrite <- IHl; eauto.
  Qed.
  Proof.
    intros.
    apply pimpl_star_emp in H as Hx.
    apply dir_names_distinct' in Hx.
    pose proof (find_dirlist_exists l H H0); deex.
    cancel.
    apply dirlist_extract'; auto.
  Qed.
  Proof.
    intros.
    unfold pimpl; intros.
    pose proof (dirlist_extract xp l H H0 m0 H1).
    destruct_lift H2.
    destruct dummy; simpl in *; subst; try congruence.
    pred_apply; cancel.
    eassign l0; cancel.
  Qed.
  Proof.
    induction ents; simpl; intros; auto.
    apply ptsto_valid in H0; congruence.
    destruct a; simpl.
    destruct (string_dec s name); subst.

    apply ptsto_valid in H; apply ptsto_valid in H0.
    rewrite H in H0; inversion H0; subst.
    eexists; intuition.

    apply ptsto_mem_except in H.
    simpl in *; eapply IHents; eauto.
    eapply ptsto_mem_except_exF; eauto.
  Qed.
  Proof.
    intros.
    eapply ptsto_subtree_exists'; eauto.
    pred_apply; cancel.
  Qed.
  Proof.
    simpl; intros.
    unfold tree_dir_names_pred.
    cancel; eauto.
  Qed.
  Proof.
    induction ents; intros; auto.
    inversion H.
    destruct a; simpl in *.
    destruct (string_dec s name); subst.
    inversion H; subst; auto.
    inversion H0; subst.
    rewrite IHents; eauto.
    cancel.
  Qed.
  Proof.
    intros.
    eapply NoDup_map_inv.
    eapply dir_names_distinct' with (m := m).
    pred_apply; cancel.
  Qed.
  Proof.
    intros; cancel.
  Qed.
  Proof.
    intros; cancel.
  Qed.
  Proof.
    intros; cancel.
  Qed.
  Proof.
    intros; cancel.
  Qed.
  Proof.
    intros; cancel.
  Qed.
  Proof.
    induction ents; simpl; intros; auto.
    destruct a; simpl in *; intuition.
    apply ptsto_valid in H; congruence.
    apply ptsto_mem_except in H.
    eapply IHents; eauto.
    apply notindomain_mem_except'; auto.
  Qed.
  Proof.
    induction ents; simpl; intros; auto.
    destruct a; intuition.
    destruct (string_dec s name); subst; simpl in *.
    inversion H0; subst; cancel.
    inversion H0; subst.
    rewrite <- IHents; eauto.
    cancel.
  Qed.
  Proof.
    intros.
    apply dirlist_pred_absorb_notin'; auto.
    eapply notindomain_not_in_dirents; eauto.
    eapply tree_dir_names_pred_nodup; eauto.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    apply sep_star_comm.
    apply ptsto_upd_disjoint; auto.

    destruct a.
    destruct (string_dec s name); subst; simpl.
    eapply ptsto_upd; eauto.

    generalize H.
    unfold_sep_star; intuition.
    repeat deex. exists m1. eexists.
    intuition.
    3: eapply IHl; eauto.

    apply functional_extensionality; intro.
    unfold Mem.upd, mem_union.
    destruct (string_dec x name); subst; auto.
    destruct (m1 name) eqn: Hx; auto.
    unfold ptsto in H2; intuition.
    pose proof (H3 _ n); congruence.

    unfold mem_disjoint, Mem.upd.
    intuition; repeat deex.
    destruct (string_dec a name); subst; auto.
    unfold ptsto in H2; intuition.
    pose proof (H6 _ n); congruence.
    unfold mem_disjoint in H0; repeat deex.
    firstorder.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    apply sep_star_comm.
    apply ptsto_upd_disjoint; auto.

    destruct a. destruct (string_dec s name); subst; simpl in *.
    apply sep_star_comm.
    apply ptsto_upd_disjoint; auto.

    generalize H.
    unfold_sep_star; intros; repeat deex.
    exists m1; eexists; intuition.
    3: eapply IHl; eauto.

    apply functional_extensionality; intro.
    unfold Mem.upd, mem_union.
    destruct (string_dec x name); subst; auto.
    destruct (m1 name) eqn: Hx; auto.
    unfold ptsto in H3; intuition.
    pose proof (H4 _ n); congruence.

    unfold mem_disjoint, Mem.upd.
    intuition; repeat deex.
    destruct (string_dec a name); subst; auto.
    unfold ptsto in H3; intuition.
    pose proof (H7 _ n); congruence.
    unfold mem_disjoint in H1; repeat deex.
    firstorder.
    eapply notindomain_mem_union; eauto.
  Qed.
  Proof.
    induction ents; intros; simpl; auto.
    destruct a. destruct (string_dec s name); subst; simpl.
    cancel.
    cancel.
    inversion H0.
    apply IHents; auto.
  Qed.
  Proof.
    induction ents; simpl; intros; auto.
    destruct a.
    destruct (string_dec s name); subst; simpl.
    inversion H; subst.
    apply dirlist_pred_add_notin; auto.
    destruct (string_dec s name); subst; simpl.
    congruence.
    cancel; apply IHents.
    inversion H; auto.
  Qed.
  Proof.
    destruct fnlist; simpl; intros.
    congruence.
    destruct d; auto.
  Qed.
  Proof.
    unfold pimpl; intros.
    assert ((emp * tree_dir_names_pred' l)%pred m) by (pred_apply; cancel).
    apply dir_names_distinct' in H0 as Hnodup.
    clear H0. pred_apply; cancel.
  Qed.
  Proof.
    induction l; simpl; intros.
    auto.
    destruct a; simpl.
    destruct (string_dec s name); subst; try intuition.
    split; cancel; apply IHl; eauto.
  Qed.
  Proof.
    intros; rewrite tree_dir_names_pred'_distinct; cancel.
    induction l; simpl; intros.
    cancel.

    destruct a.
    case_eq (update_subtree_helper (update_subtree fnlist subtree') name (s, d)); intros.
    unfold update_subtree_helper in H2.
    simpl in *.
    destruct (string_dec s name); subst.
    - inversion H2; clear H2; subst; simpl in *.
      erewrite <- tree_dir_names_pred_update'; eauto. cancel.
      apply tree_dir_names_pred_notfound. inversion H4; eauto.
    - inversion H2; clear H2; subst; simpl in *.
      cancel. apply H2. inversion H4; eauto.
  Qed.
  Proof.
    intros; rewrite tree_dir_names_pred'_distinct; cancel.
    induction l; simpl; intros.
    cancel.

    destruct a.
    case_eq (update_subtree_helper (update_subtree fnlist subtree') name (s, d)); intros.
    unfold update_subtree_helper in H2.
    simpl in *.
    destruct (string_dec s name); subst.
    - inversion H2; clear H2; subst; simpl in *.
      erewrite <- tree_dir_names_pred_update'; eauto. cancel.
      apply tree_dir_names_pred_notfound. inversion H4; eauto.
      erewrite <- update_subtree_preserve_name; eauto.
    - inversion H2; clear H2; subst; simpl in *.
      cancel. apply H2. inversion H4; eauto.
  Qed.
  Proof.
    unfold tree_dir_names_pred; intros; split; cancel; eauto.
    match goal with | [ H: SDIR.rep _ _ |- _ ] => clear H end.
    pred_apply.
    eapply tree_dir_names_pred'_update; eauto.
    match goal with | [ H: SDIR.rep _ _ |- _ ] => clear H end.
    pred_apply.
    eapply tree_dir_names_pred'_update_inv; eauto.
  Qed.
  Proof.
    induction l; simpl; intros.
    auto.
    destruct a; simpl. destruct (string_dec s name); subst.
    - edestruct H. eauto.
    - split; cancel; apply IHl; eauto.
  Qed.
  Proof.
    induction path; intros; eauto.
    destruct tree; simpl in *.
    cancel.
    rewrite <- tree_dir_names_pred_update; eauto.
    rewrite dir_names_distinct at 1; cancel.

    induction l0; simpl in *; intros; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s a); subst.
    destruct (string_dec a a); try congruence.

    inversion H3; subst.
    rewrite <- dirlist_pred_except_notfound; auto.
    rewrite <- dirlist_pred_except_notfound'; auto.
    cancel.
    eapply IHpath; eauto.
    contradict H2.
    erewrite <- update_subtree_preserve_name; eauto.

    destruct (string_dec s a); subst; try congruence.
    cancel.
    inversion H3; eauto.
  Qed.
  Proof.
    induction fnlist; simpl; intros.
    - inversion H; subst. cancel.
    - destruct tree; try discriminate; simpl.
      rewrite dir_names_distinct at 1; cancel.
      rewrite tree_dir_names_pred_update; eauto.
      cancel.

      induction l; simpl in *; intros; try congruence.
      destruct a0; simpl in *.
      destruct (string_dec s a); subst.
      + rewrite <- IHfnlist; eauto. cancel.
        inversion H6.
        apply dirlist_pred_except_notfound'; eauto.
      + cancel.
        inversion H6.
        rewrite <- H2; eauto.
        cancel.
  Qed.
  Proof.
    intros; unfold tree_prune.
    erewrite <- subtree_absorb; eauto.
    cancel.
    unfold tree_dir_names_pred.
    cancel; eauto.
    eapply dirlist_pred_extract; eauto.
    eapply tree_dir_names_pred_nodup; eauto.
  Qed.
  Proof.
    intros; unfold tree_graft.
    erewrite <- subtree_absorb; eauto.
    cancel.
    unfold tree_dir_names_pred.
    cancel; eauto.
    eapply dirlist_pred_absorb_notin; eauto.
    apply dir_names_pred_add; auto.
  Qed.
  Proof.
    intros; unfold tree_graft.
    erewrite <- subtree_absorb; eauto.
    cancel.
    unfold tree_dir_names_pred.
    cancel; eauto.
    rewrite tree_pred_except_update; eauto; cancel.
    rewrite sep_star_comm.
    rewrite dirlist_pred_absorb_notin; eauto.
    apply dirlist_pred_add_delete.
    eapply dir_names_distinct' with (m := dsmap').
    pred_apply; cancel.
    apply dir_names_pred_add_delete; auto.
  Qed.
  Proof.
    intros.
    rewrite subtree_extract in H by (eauto using find_update_subtree).
    cbn in *.
    destruct_lifts.
    unfold dirfile_to_bfile.
    eapply pimpl_apply in H; [ eapply list2nmem_sel with (i := inum) in H as Hs | cancel].
    eapply forall2_selN in H0 as Hf; eauto using list2nmem_inbound.
    unfold BFILE.file_crash in Hf.
    rewrite <- Hs in Hf. cbn in Hf.
    deex.
    denote Array.possible_crash_list as Hp.
    apply Array.possible_crash_list_synced_list_eq in Hp. subst.
    unfold BFILE.synced_file. cbn -[Array.synced_list].
    denote (selN _ _ _ = _) as Hx.
    rewrite <- Hx.
    apply list2nmem_array_pick.
    erewrite <- forall2_length by eauto.
    eauto using list2nmem_inbound.
  Unshelve.
    all: try exact BFILE.bfile0.
    all: eauto.
  Qed.