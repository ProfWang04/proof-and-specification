Proof.
  unfold dir2flatmem2; intros.
  destruct (find_subtree fnlist tree).
  destruct d.
  inversion H0; subst; auto.
  inversion H0.
  inversion H0.
Qed.
Proof.
  unfold dir2flatmem2; intros.
  destruct (find_subtree fnlist tree); eauto.
  destruct d; inversion H0; subst; auto; congruence.
Qed.
Proof.
  unfold dir2flatmem2; intros.
  destruct (find_subtree fnlist tree); [ destruct d | ]; try congruence.
  inversion H0; subst.
  eauto.
Qed.
Proof.
  intros.
  eapply ptsto_valid' in H0.
  eapply dir2flatmem2_find_subtree; eauto.
Qed.
Proof.
  intros.
  eapply ptsto_valid' in H0.
  eapply dir2flatmem2_find_subtree_none in H0; eauto.
Qed.
Proof.
  intros.
  eapply ptsto_valid' in H0.
  eapply dir2flatmem2_find_subtree_dir in H0; eauto.
Qed.
Proof.
  unfold find_name; intros.
  erewrite dir2flatmem2_find_subtree; eauto.
Qed.
Proof.
  unfold find_name; intros.
  erewrite dir2flatmem2_find_subtree_none; eauto.
Qed.
Proof.
  intros.
  eapply ptsto_valid' in H0.
  eapply dir2flatmem2_find_name; eauto.
Qed.
Proof.
  intros.
  eapply ptsto_valid' in H0.
  eapply dir2flatmem2_find_name_none; eauto.
Qed.
Proof.
  unfold dir2flatmem2; intros.
  apply functional_extensionality; intros.
  destruct (pathname_decide_prefix fnlist x); repeat deex; subst.
  {
    destruct suffix.
    - rewrite app_nil_r in *.
      erewrite find_update_subtree; eauto.
      rewrite upd_eq; auto.
    - rewrite upd_ne.
      repeat erewrite find_subtree_app.
      2: eauto.
      2: erewrite find_update_subtree; eauto.
      simpl; eauto.
      rewrite <- app_nil_r with (l := fnlist) at 2.
      intro H'. apply app_inv_head in H'. congruence.
  }
  destruct (pathname_decide_prefix x fnlist); repeat deex; subst.
  {
    destruct suffix.
    - rewrite app_nil_r in *.
      erewrite find_update_subtree; eauto.
      rewrite upd_eq; auto.
    - rewrite upd_ne.
      case_eq (find_subtree x tree); intros.
      destruct d.
      + erewrite find_subtree_app in * by eauto; simpl in *; congruence.
      + erewrite update_subtree_app by eauto. erewrite find_update_subtree by eauto.
        simpl; auto.
      + rewrite find_subtree_app_none in * by eauto; congruence.
      + rewrite <- app_nil_r with (l := x) at 1.
        intro H'. apply app_inv_head in H'. congruence.
  }
  rewrite find_subtree_update_subtree_ne_path; eauto.
  rewrite upd_ne; auto.
  contradict H1; subst; eauto. exists nil. rewrite app_nil_r. auto.
Qed.
Proof.
  intros.
  erewrite dir2flatmem2_update_subtree_upd; eauto.
  eapply ptsto_upd'; eauto.
  eapply dir2flatmem2_find_subtree_ptsto; eauto.
Qed.
Proof.
  intros.
  unfold dir2flatmem2.
  apply functional_extensionality; intros.
  destruct (pathname_decide_prefix base x).
  - destruct H2 as [suffix H2]; subst.
    destruct (pathname_decide_prefix [name] suffix).
    + destruct H2 as [suffix0 H2]; subst.
      rewrite app_assoc.
      erewrite find_subtree_app.
      2: erewrite find_subtree_tree_graft; eauto.
      destruct suffix0; simpl in *.
      * rewrite app_nil_r. rewrite upd_eq; eauto.
      * rewrite upd_ne; eauto.
        2: intro H'; rewrite <- app_nil_r in H'; apply app_inv_head in H'; congruence.
        intuition.
        -- erewrite find_subtree_app; eauto. simpl. eauto.
        -- erewrite find_subtree_app_none; eauto.
    + destruct suffix; simpl in *.
      * rewrite app_nil_r in *.
        rewrite upd_ne; eauto.
        rewrite H0.
        unfold tree_graft.
        erewrite find_update_subtree; eauto.
        rewrite <- app_nil_r with (l := base) at 1.
        intro H'.
        apply app_inv_head in H'. congruence.
      * assert (s <> name) by ( intro; subst; eauto ).
        unfold tree_graft.
        erewrite find_subtree_app.
        2: erewrite find_update_subtree; eauto.
        rewrite upd_ne; eauto.
        2: intro H'; apply app_inv_head in H'; congruence.
        erewrite find_subtree_app; [ | eauto ].

        clear H0.
        simpl.
        induction basedents; simpl in *.
        -- destruct (string_dec name s); congruence.
        -- destruct a.
           destruct (string_dec s0 name); subst; simpl in *.
          ++ destruct (string_dec name s); try congruence.
          ++ destruct (string_dec s0 s); try congruence.

  - clear H1.
    rewrite upd_ne.
    unfold tree_graft.
    2: intro; apply H2; eauto.
    case_eq (find_subtree x tree); intros.
    destruct d.
    + erewrite find_subtree_update_subtree_oob; eauto.
    + edestruct find_subtree_dir_after_update_subtree; eauto.
      rewrite H3; eauto.
    + erewrite find_subtree_none_after_update_subtree; eauto.
Qed.
Proof.
  intros.
  erewrite dir2flatmem2_graft_upd; eauto.
  eapply ptsto_upd'; eauto.
  left.
  eapply dir2flatmem2_find_subtree_ptsto; eauto.
Qed.
Proof.
  intros.
  erewrite dir2flatmem2_graft_upd; eauto.
  eapply ptsto_upd'; eauto.
  right.
  eapply dir2flatmem2_find_subtree_ptsto_none; eauto.
Grab Existential Variables.
  all: eauto.
Qed.
Proof.
  intros.
  unfold dir2flatmem2.
  apply functional_extensionality; intros.
  destruct (pathname_decide_prefix base x).
  - destruct H2 as [suffix H2]; subst.
    destruct (pathname_decide_prefix [name] suffix).
    + destruct H2 as [suffix0 H2]; subst.
      rewrite app_assoc.
      erewrite find_subtree_app_none.
      2: eapply find_subtree_pruned_none; eauto.

      destruct suffix0; simpl in *.
      * rewrite app_nil_r. rewrite upd_eq; eauto.
      * rewrite upd_ne; eauto.
        2: intro H'; rewrite <- app_nil_r in H'; apply app_inv_head in H'; congruence.
        intuition.
        -- erewrite find_subtree_app; eauto. simpl. eauto.
        -- erewrite find_subtree_app_none; eauto.

    + destruct suffix; simpl in *.
      * rewrite app_nil_r in *.
        rewrite upd_ne; eauto.
        rewrite H0.
        unfold tree_prune.
        erewrite find_update_subtree; eauto.
        rewrite <- app_nil_r with (l := base) at 1.
        intro H'.
        apply app_inv_head in H'. congruence.
      * assert (s <> name) by ( intro; subst; eauto ).
        unfold tree_prune.
        erewrite find_subtree_app.
        2: erewrite find_update_subtree; eauto.
        rewrite upd_ne; eauto.
        2: intro H'; apply app_inv_head in H'; congruence.
        erewrite find_subtree_app; [ | eauto ].

        clear H0.
        simpl.
        induction basedents; simpl in *.
        -- destruct (string_dec name s); congruence.
        -- destruct a.
           destruct (string_dec s0 name); subst; simpl in *.
          ++ destruct (string_dec name s); try congruence.
          ++ destruct (string_dec s0 s); try congruence.

  - clear H1.
    rewrite upd_ne.
    unfold tree_prune.
    2: intro; apply H2; eauto.
    case_eq (find_subtree x tree); intros.
    destruct d.
    + erewrite find_subtree_update_subtree_oob; eauto.
    + edestruct find_subtree_dir_after_update_subtree; eauto.
      rewrite H3; eauto.
    + erewrite find_subtree_none_after_update_subtree; eauto.
Qed.
Proof.
  intros.
  erewrite dir2flatmem2_prune_delete; eauto.
  eapply ptsto_upd'; eauto.
  left.
  eapply dir2flatmem2_find_subtree_ptsto; eauto.
Qed.
Proof.
  intros.
  unfold dir2flatmem2 in *.
  apply functional_extensionality; intros.
  destruct (pathname_decide_prefix base x).
  - deex.
    erewrite find_subtree_app.
    2: eapply find_update_subtree; eauto.
    eapply equal_f in H1.
    rewrite H1.
    destruct (list_eq_dec string_dec pn suffix); subst.
    + repeat rewrite upd_eq; eauto.
    + repeat rewrite upd_ne; eauto.
      erewrite find_subtree_app; eauto.
      intro. apply n. apply app_inv_head in H2; eauto.
  - rewrite upd_ne.
    2: intro; apply H2; eauto.
    case_eq (find_subtree x t); [ destruct d | ]; intros.
    + erewrite find_subtree_update_subtree_oob; eauto.
    + edestruct find_subtree_dir_after_update_subtree.
      3: eauto.
      2: eauto.
      eauto.
      rewrite H4; eauto.
    + rewrite find_subtree_none_after_update_subtree; eauto.
Qed.
Proof.
  intros.
  erewrite dirents2mem_update_subtree_upd; eauto.
  eapply ptsto_upd'; eauto.
Qed.
Proof.
  intros.
  eapply pimpl_trans in H0 as H'1; [ | | reflexivity ].
  eapply pimpl_trans in H0 as H'2; [ | | reflexivity ].
  eapply dir2flatmem2_find_subtree_ptsto with (fnlist := pn1) in H'1; eauto.
  eapply dir2flatmem2_find_subtree_ptsto with (fnlist := pn2) in H'2; eauto.
  2: cancel.
  2: cancel.

  intro.
  destruct H1; subst.
  erewrite find_subtree_app in H'2 by eauto.

  destruct x.

  - rewrite app_nil_r in *.
    eapply ptsto_conflict_F with (a := pn1).
    eapply pimpl_trans; [ reflexivity | | eauto ].
    cancel.
  - simpl in *; congruence.
Qed.
Proof.
  intros.
  eapply dir2flatmem2_prune_delete in H0.
  unfold tree_prune in H0.
  unfold delete_from_dir in H0.
  rewrite H0.
  eapply ptsto_upd'; eauto.
  eauto.
  left.
  eapply dir2flatmem2_find_subtree_ptsto; eauto.
Qed.
Proof.
  intros.
  erewrite <- update_update_subtree_same.
  eapply dirents2mem2_update_subtree_one_name.
  eapply pimpl_trans; [ reflexivity | | ].
  2: eapply dirents2mem2_update_subtree_one_name.
  5: eauto.
  3: eapply dir2flatmem2_prune_delete with (name := srcname) (base := srcbase).
  cancel.
  pred_apply; cancel.
  3: left.
  3: erewrite <- find_subtree_app by eauto.
  3: eapply dir2flatmem2_find_subtree_ptsto.

  eapply tree_names_distinct_subtree; eauto.

  eauto.
  eauto.
  pred_apply; cancel.
  eauto.

  3: erewrite find_update_subtree; eauto.

  erewrite <- find_subtree_dirlist in H4.
  erewrite <- find_subtree_app in H4 by eauto.
  erewrite <- find_subtree_app in H4 by eauto.
  erewrite dir2flatmem2_find_subtree_ptsto in H4.
  3: pred_apply; cancel.
  inversion H4; subst.

  erewrite dir2flatmem2_graft_upd; eauto.

  eapply tree_names_distinct_prune_subtree'; eauto.
  eapply tree_names_distinct_subtree; eauto.

  left.
  eapply find_subtree_prune_subtree_oob; eauto.

  intro. eapply pathname_prefix_trim in H6.
  eapply dirents2mem2_not_prefix; eauto.
  erewrite <- find_subtree_app by eauto.
  erewrite dir2flatmem2_find_subtree_ptsto.
  reflexivity. eauto.
  pred_apply; cancel.
  eauto.

  eapply tree_names_distinct_update_subtree; eauto.
  eapply tree_names_distinct_prune_subtree'; eauto.
  eapply tree_names_distinct_subtree; eauto.
Qed.