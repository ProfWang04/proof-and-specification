  Proof.
    induction l; simpl; intros; eauto.
    destruct a; simpl in *.
    destruct (string_dec s name); intuition.
    rewrite IHl; eauto.
  Qed.
  Proof.
    induction ents; intros; auto; simpl.
    destruct a; simpl in *; intuition.
    destruct (string_dec s name); subst; try congruence; auto.
  Qed.
  Proof.
    induction path; simpl. 
    try congruence.
    intros.
    induction ents; simpl; intros; auto.
    destruct a0; inversion H; subst; simpl in *.
    rewrite fold_right_app; simpl.
    destruct (string_dec s a); subst.
    - rewrite H0.
      apply find_subtree_ents_not_in.
      rewrite map_rev.
      rewrite <- in_rev; auto.
    - apply IHents; auto.
  Qed.
  Proof.
    intros.
    induction pn; simpl in *; subst; try congruence.
  Qed.
  Proof.
    induction p0; simpl; intros.
    inversion H; eauto.
    destruct tree; try congruence.
    induction l; simpl in *; intros; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s a); eauto.
  Qed.
  Proof.
    intros.
    erewrite find_subtree_app; eauto.
  Qed.
  Proof.
    induction p0; simpl; intros.
    inversion H; eauto.
    destruct tree; try congruence.
    induction l; simpl in *; intros; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s a); eauto.
  Qed.
  Proof.
    induction base; intros.
    simpl in *.
    contradict H. eauto.

    destruct pn.
    simpl in *. inversion H0; subst. eauto.
    destruct tree; simpl in *; try congruence.
    induction l; simpl in *; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s0 s); destruct (string_dec s0 a); subst; subst; simpl in *.
    - destruct (string_dec a a); try congruence.
      eapply IHbase; eauto.
      intro H'; apply H. deex. exists suffix. eauto.
    - destruct (string_dec s s); try congruence.
    - destruct (string_dec a s); try congruence.
      eauto.
    - destruct (string_dec s0 s); try congruence.
      eauto.
  Qed.
  Proof.
    induction base; intros.
    simpl in *.
    contradict H. eauto.

    destruct pn.
    simpl in *. inversion H0; subst. eauto.
    destruct tree; simpl in *; try congruence.
    destruct tree; simpl in *; try congruence.

    induction l; simpl in *; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s0 s); destruct (string_dec s0 a); subst; subst; simpl in *.
    - destruct (string_dec s s); try congruence.
      eapply IHbase; eauto.
      intro H'; apply H. deex. exists suffix. eauto.
    - destruct (string_dec s s); try congruence.
    - destruct (string_dec a s); try congruence; eauto.
    - destruct (string_dec s0 s); try congruence; eauto.
  Qed.
  Proof.
    induction base; simpl; intros.
    contradict H; eauto.

    destruct pn; simpl in *.
    - eexists; intuition eauto.
      destruct tree; destruct subtree'; simpl in *; try congruence.
      destruct tree; destruct subtree'; simpl in *; try congruence.

    - destruct tree; simpl in *; try congruence.
      induction l; simpl in  *; try congruence.

      destruct a0; simpl in *.
      destruct (string_dec s0 a); destruct (string_dec s0 s); subst; simpl in *.
      + destruct (string_dec s s); try congruence.
        eapply IHbase; eauto.
        intro H'. apply H. deex. eauto.
      + destruct (string_dec a s); try congruence. eauto.
      + destruct (string_dec s s); try congruence. eauto.
      + destruct (string_dec s0 s); try congruence. eauto.
  Qed.
  Proof.
    induction pathname; simpl in *; intros; eauto.
    destruct tree; try congruence.
    induction l; simpl in *; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s a); subst; simpl in *.
    - destruct (string_dec a a); try congruence.
      eauto.
    - destruct (string_dec s a); try congruence.
      apply IHl; eauto.
  Qed.
  Proof.
    induction rest; simpl; intros.
    auto.
    erewrite IHrest.
    unfold update_subtree_helper.
    destruct a.
    destruct (string_dec s name); eauto.
  Qed.
  Proof.
    induction fnlist; simpl; try congruence; intros.
    destruct tree; try congruence.
    induction l; simpl in *; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s a); subst; simpl.
    - destruct (string_dec a a); try congruence; eauto.
    - destruct (string_dec s a); try congruence; eauto.
  Qed.
  Proof.
    induction path; simpl; try congruence; intros.
    destruct tree; try congruence.
    induction l; simpl in *; try congruence.
    destruct a0; simpl in *.
    destruct (string_dec s a); subst; simpl.
    - destruct (string_dec a a); try congruence; eauto.
    - destruct (string_dec s a); try congruence; eauto.
  Qed.
  Proof.
    induction p2.
    - simpl; intros. inversion H0; simpl. destruct p1; try congruence. simpl; congruence.
    - intros.
      destruct tree; try solve [ simpl in *; congruence ].
      destruct p1; try solve [ inversion H ].
      destruct (string_dec s a); subst; simpl in *.
      + induction l; try solve [ simpl in *; congruence ].
        destruct a0. simpl in *.
        destruct (string_dec s a); subst; simpl.
        * destruct (string_dec a a); try congruence.
          eapply IHp2; eauto.
          intro; apply H1; congruence.
        * destruct (string_dec s a); try congruence.
          eauto.
      + clear IHp2.
        clear H.
        induction l; try solve [ simpl in *; congruence ].
        destruct a0. simpl in *.
        destruct (string_dec s0 a); subst; simpl.
        * destruct (string_dec a s); try congruence.
          simpl. destruct (string_dec a a); try congruence.
        * destruct (string_dec s0 s); subst; simpl in *.
          destruct (string_dec s a); try congruence. eauto.
          destruct (string_dec s0 a); try congruence; eauto.
  Qed.
  Proof.
    unfold tree_graft, add_to_dir.
    induction path; intros.
    induction ents; intros; simpl; auto.
    destruct a; destruct (string_dec s name); simpl in *; subst; intuition.
    inversion H; rewrite H3; auto.
    destruct tree; simpl; auto.
    f_equal. f_equal. f_equal.
    apply functional_extensionality; intros.
    apply IHpath; auto.
  Qed.
  Proof.
    intros; cbn.
    unfold find_dirlist in H0. 
    destruct (string_dec name name); try congruence.
  Qed.
  Proof.
    intros; cbn.
    unfold find_dirlist in H0. 
    destruct (string_dec name2 name1); try congruence.
  Qed.
  Proof.
    induction ents; simpl; intros; try congruence.
    destruct a.
    destruct (string_dec s name); subst.
    left; auto.
    right; simpl in *.
    eapply IHents.
    destruct (string_dec s name); try congruence; eauto.
  Qed.
  Proof.
    induction ents; simpl; intros; auto.
    destruct a; destruct (string_dec s name); subst.
    - inversion H; inversion H0; subst; simpl in *.
      destruct (string_dec name name); congruence.
    - inversion H0; subst; simpl in *.
      destruct (string_dec s name); subst.
      contradict H3; eapply find_dirlist_in; eauto.
      apply IHents; eauto.
  Qed.
  Proof.
    induction ents; simpl; intros; try congruence.
    destruct a.
    destruct (string_dec s name); subst.
    left; auto.
    right; simpl in *.
    eapply IHents.
    destruct (string_dec s name); try congruence; eauto.
  Qed.
  Proof.
    induction pathname; simpl in *; intuition.
    inversion H0.
    induction ents; simpl in *; try congruence.
    destruct a0 as [ename subtree]; simpl in *.
    destruct (string_dec ename name); subst.
    - inversion H; subst; destruct (string_dec name a); subst; auto.
      contradict H3.
      eapply find_subtree_helper_in; eauto.
    - inversion H; subst; simpl in *.
      destruct (string_dec ename a); destruct (string_dec a a); subst; try congruence.
      apply IHents; auto.
  Qed.
  Proof.
    unfold find_name; intros.
    destruct (find_subtree path tree); try destruct d;
      inversion H; subst; eauto.
  Qed.
  Proof.
    induction path; intros; auto.
    inversion H; subst.
    firstorder.
    destruct tree; firstorder.
  Qed.
  Proof.
    induction path; intros; auto.
    inversion H; subst.
    firstorder.
    destruct tree; firstorder.
  Qed.
  Proof.
    induction path; intros; auto.
    inversion H; subst.
    firstorder.
    destruct tree; firstorder.
  Qed.
  Proof.
    induction path; intros; auto.
    inversion H; subst.
    firstorder.
    destruct tree; firstorder.
  Qed.
  Proof.
    induction ents; simpl; intros; auto.
    destruct a; simpl.
    destruct (string_dec s name); subst; auto.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    unfold update_subtree_helper at 1.
    destruct a. destruct (string_dec s0 s); subst; auto.
    rewrite IHl. f_equal.
    rewrite IHl; auto.
  Qed.
  Proof.
    intros.
    induction l.
    - simpl; auto.
    - erewrite map_cons.
      unfold update_subtree_helper at 1.
      destruct a.
      destruct (string_dec s name).
      erewrite map_cons; erewrite IHl; simpl; auto.
      erewrite map_cons; erewrite IHl; simpl; auto.
  Qed.
  Proof.
    induction ents; simpl; intuition.
    - inversion H0; inversion H1; subst; simpl in *.
      destruct (string_dec name name); congruence.
    - inversion H0; subst; simpl in *.
      destruct (string_dec a0 name); subst.
      contradict H3.
      apply in_map_iff; eexists; split; eauto; simpl; auto.
      apply IHents; auto.
  Qed.
  Proof.
    intros.
    destruct path.
    - eexists tree; intros; subst.
      intuition.
    - case_eq (find_subtree (s :: path) tree); intros; subst.
      eexists d.
      intuition.
      erewrite find_subtree_app with (p0 := (s::path)) in H; eauto.
      exfalso.
      eapply find_subtree_app_none with (p1 := suffix) in H0.
      rewrite H0 in H.
      inversion H.
  Qed.
  Proof.
    intros.
    simpl.
    destruct (string_dec name name); try congruence.
  Qed.
  Proof.
    intros.
    simpl.
    destruct (string_dec s name); try congruence.
  Qed.
  Proof.
    intros.
    destruct pn.
    - unfold pathname_prefix in H.
      deex. exfalso. simpl in H. try congruence.
    - unfold pathname_prefix in H.
      deex.
      inversion H; subst.
      simpl.
      destruct (string_dec s0 s0); try congruence.
  Qed.
  Proof.
    intros.
    destruct pn; try congruence.
    unfold pathname_prefix in H0.
    destruct (string_dec s s0); subst; try congruence.
    - exfalso. apply H0. exists pn. rewrite cons_app with (l := pn).
      reflexivity.
    - simpl. destruct (string_dec s s0); try congruence.
  Qed.
  Proof.
    induction l; intros.
    - exfalso.
      simpl in H.
      inversion H.
    - destruct a; simpl.
      destruct (string_dec s name); subst.
      + simpl.
        destruct (string_dec name name); try congruence.
        rewrite find_subtree_head in H.
        inversion H; eauto.
      + simpl.
        destruct (string_dec s name); try congruence.
        unfold find_subtree in IHl at 2; simpl.
        case_eq (update_subtree ([name] ++ path) subtree (TreeDir n l)); intros.
        eapply IHl; eauto.
        rewrite find_subtree_head_ne in H; eauto.
        eapply IHl; eauto.
        rewrite find_subtree_head_ne in H; eauto.
  Qed.
  Proof.
    intros. case_eq tree; intros.
    - exfalso.
      subst.
      unfold find_subtree in H; simpl.
      inversion H.
    - erewrite update_subtree_update_trim_head_dir; eauto.
      subst; eauto.
  Qed.
  Proof.
    intros; simpl.
    destruct tree; subst; eauto.
    induction l; subst; simpl in *; eauto.
    destruct a; simpl.
    unfold find_subtree_helper at 1; simpl.
    destruct (string_dec s0 s); subst; simpl.
    + destruct (string_dec s name); simpl in *; try congruence.
    + destruct (string_dec s name); simpl in *; try congruence.
      destruct (string_dec s0 name); try congruence.
  Qed.
  Proof.
    induction path; intros; subst; auto.
    - rewrite app_nil_l.
      simpl in *.
      inversion H; eauto.
     - rewrite cons_app in *.
      eapply find_subtree_app' in H.
      deex.
      erewrite find_subtree_app with (subtree := 
        (update_subtree (path ++ suffix) subtree subtree_base)).
      eapply IHpath; eauto.
      eapply find_subtree_update_trim_head; eauto.
  Qed.
  Proof.
    intros.
    destruct tree.
    - rewrite cons_app.
      erewrite find_subtree_app.
      2: eauto.
      erewrite find_subtree_app.
      2: eauto.
      reflexivity.
    - rewrite cons_app. 
      erewrite find_subtree_app.
      erewrite find_subtree_app.
      2: eauto.
      eauto.
      setoid_rewrite cons_app at 2.
      erewrite find_subtree_update_subtree_child; eauto.
  Qed.
  Proof.
    intros.
    destruct pn; try congruence.
    destruct (string_dec a s); subst.
    + exfalso.
      eapply H0.
      unfold pathname_prefix.
      eexists pn.
      eauto.
    + erewrite update_subtree_update_trim_head_ne; eauto.
  Qed.
  Proof.
    intros.
    destruct tree; eauto.
    induction l; intros.
    - simpl in *; eauto.
    - destruct a0; simpl.
      destruct (string_dec s a); subst.
      + simpl.
        destruct (string_dec a a); try congruence.
        rewrite find_subtree_head in H.
        inversion H; eauto.
      + simpl.
        destruct (string_dec s a); try congruence.
        unfold find_subtree in IHl at 2; simpl.
        case_eq (update_subtree ([a] ++ suffix) subtree (TreeDir n l)); intros.
        eapply IHl; eauto.
        rewrite find_subtree_head_ne in H; eauto.
        eapply IHl; eauto.
        rewrite find_subtree_head_ne in H; eauto.
  Qed.
  Proof.
    induction l; intros; subst; eauto.
    destruct a.
    erewrite map_cons; simpl.
    intuition.
    subst. erewrite find_subtree_head in H.
    inversion H.
    eapply IHl; eauto.
    destruct (string_dec s name); subst.
    erewrite find_subtree_head in H. inversion H.
    rewrite find_subtree_head_ne in H; eauto.
  Qed.
  Proof.
    induction l; intros; auto.
    destruct a; simpl in *.
    inversion H; subst.
    destruct (string_dec s name); subst.
    apply find_subtree_ents_not_in; auto.
    simpl. rewrite IHl; auto.
    destruct (string_dec s name); congruence; auto.
  Qed.
  Proof.
    unfold delete_from_dir; eapply find_subtree_delete_same'.
  Qed.
  Proof.
    induction l; intros; auto.
    destruct a; simpl in *.
    inversion H; subst.
    destruct (string_dec s name); subst; simpl.
    destruct (string_dec name name'); subst; simpl; try congruence.
    destruct (string_dec name name); subst; simpl; try congruence.
    destruct (string_dec s name); subst; simpl; try congruence.
    destruct (string_dec s name'); subst; simpl; try congruence.
    destruct (string_dec s name); subst; simpl; try congruence.
    eapply IHl; eauto. 
  Qed.
  Proof.
    unfold delete_from_dir; eapply find_subtree_delete_ne'.
  Qed.
  Proof.
    induction l; simpl; auto; intros.
    destruct a.
    destruct (string_dec s name); simpl in *; intuition.
    right; eapply IHl; eauto.
  Qed.
  Proof.
    induction l; simpl; auto; intros.
    destruct a.
    destruct (string_dec s name); simpl in *; intuition.
    right; eapply IHl; eauto.
  Qed.
  Proof.
    induction l; simpl; auto; intros.
    inversion H; destruct a; subst; simpl in *.
    destruct (string_dec s name); try congruence.
    simpl; constructor.
    contradict H2.
    eapply In_delete_from_list_fst; eauto.
    apply IHl; auto.
  Qed.
  Proof.
    induction l; intros; auto.
    - unfold add_to_list.
      rewrite cons_app.
      erewrite find_subtree_app.
      2: {
        erewrite find_subtree_dirlist.
        unfold find_dirlist.
        destruct (string_dec name name); try congruence.
        eauto.
      }
      f_equal.
    -
      destruct a; simpl in *.
      destruct (string_dec s name); subst.
      simpl.
      destruct (string_dec name name); try congruence.
      simpl.
      destruct (string_dec name name); subst; try congruence.
      destruct (string_dec s name); subst; try congruence.
  Qed.
  Proof.
    unfold find_subtree, update_subtree, add_to_dir.
    induction tree_elem; intros; subst; simpl.
    - destruct (string_dec name name). reflexivity. exfalso. eauto.
    - destruct a.
      destruct (string_dec s name); subst; simpl.
      destruct (string_dec name name). reflexivity. exfalso. eauto.
      destruct (string_dec s name); subst; simpl.
      congruence.
      eauto.
  Qed.
  Proof.
    intros; subst; simpl.
    destruct tree.
    simpl in *.
    congruence. 
    induction l.
    - simpl in *. congruence.
    - destruct a0. simpl in *.
      destruct (string_dec s a).
      eexists. intuition; eauto.
      eauto.
  Qed.
  Proof.
    intros.
    subst; simpl.
    destruct tree.
    simpl in *.
    intuition.
    congruence.
    simpl in *.
    unfold fold_right in H.
    induction l.
    - simpl in *. intuition. congruence.
    - destruct a0. simpl in *.
      destruct (string_dec s a).
      simpl in *.
      destruct (string_dec s a).
      intuition.
      inversion H0.
      assumption.
      rewrite IHl.
      reflexivity.
      intuition.
      simpl in *.
      destruct (string_dec s a).
      congruence.
      eauto.
  Qed.
  Proof.
    induction prefix; intros.
    - rewrite app_nil_l.
      inversion H. 
      erewrite lookup_name by eauto.
      reflexivity.
    - edestruct lookup_firstelem_path; eauto.
      intuition.
      erewrite lookup_firstelem_path_r.
      eauto.
      intuition.
      eauto.
      erewrite IHprefix by eauto.
      reflexivity.
  Qed.
  Proof.
    intros.
    unfold tree_graft.
    erewrite lookup_path with (dnum := dnum) (tree_elem := tree_elem) by eauto.
    reflexivity.
  Qed.
  Proof.
    induction pn; simpl; intros; eauto.
    destruct tree; eauto.
    f_equal.
    induction l; eauto.
    destruct a0; simpl.
    rewrite IHl; f_equal.
    destruct (string_dec s a); subst; simpl.
    destruct (string_dec a a); congruence.
    destruct (string_dec s a); congruence.
  Qed.
  Proof.
    destruct t; simpl; intros; congruence.
  Qed.
  Proof.
    destruct t; simpl; intros; congruence.
  Qed.
  Proof.
    intros.
    rewrite cons_app.
    rewrite find_subtree_app_none; eauto.
  Qed.
  Proof.
    intros.
    destruct pn.
    simpl in *; try congruence.
    rewrite find_subtree_file_none in H.
    try congruence.
  Qed.
  Proof.
    unfold tree_graft; intros.
    destruct (pathname_decide_prefix base pn).
    - deex.
      erewrite find_subtree_app in H1 by eassumption.
      erewrite find_subtree_app.
      2: erewrite find_update_subtree; eauto.

      clear H.
      induction ents; simpl in *.
      + destruct suffix; simpl in *; congruence.
      + destruct suffix; simpl in *; try congruence.
        destruct a; simpl in *.
        destruct (string_dec s0 s); subst.
        * destruct (string_dec s name); subst.
          -- exfalso. apply H0. eexists; rewrite <- app_assoc; simpl; eauto.
          -- simpl in *.
             destruct (string_dec s s); subst; congruence.
        * specialize (IHents H1).
          destruct (string_dec s0 name); subst.
          -- simpl. destruct (string_dec name s); congruence.
          -- simpl. destruct (string_dec s0 s); congruence.
    - eapply find_subtree_update_subtree_oob; eauto.
  Qed.
  Proof.
    unfold tree_graft; intros.
    destruct (pathname_decide_prefix base pn).
    - deex.
      erewrite find_subtree_app in H1.
      erewrite find_subtree_app by eassumption.
      2: erewrite find_update_subtree; eauto.

      clear H.
      induction ents; simpl in *.
      + destruct suffix; simpl in *; try congruence.
        destruct (string_dec name s); subst; simpl in *; try congruence.
        contradict H0; eauto.
        exists suffix.
        rewrite <- app_assoc.
        simpl. eauto.
      + destruct suffix; simpl in *; try congruence.
        destruct a; simpl in *.
        destruct (string_dec s0 s); subst.
        * destruct (string_dec s name); subst.
          -- exfalso. apply H0. eexists; rewrite <- app_assoc; simpl; eauto.
          -- simpl in *.
             destruct (string_dec s s); subst; congruence.
        * destruct (string_dec s0 name); subst; simpl in *; try congruence.
          destruct (string_dec name s); subst; simpl in *; try congruence.
          destruct (string_dec s0 s); subst; simpl in *; try congruence.
          specialize (IHents H1).
          eauto.
    - eapply find_subtree_update_subtree_oob'; eauto.
  Qed.
  Proof.
    unfold tree_prune; intros.
    destruct (pathname_decide_prefix base pn).
    - deex.
      erewrite find_subtree_app in H1 by eassumption.
      erewrite find_subtree_app.
      2: erewrite find_update_subtree; eauto.

      clear H.
      induction ents; simpl in *.
      + destruct suffix; simpl in *; congruence.
      + destruct suffix; simpl in *; try congruence.
        destruct a; simpl in *.
        destruct (string_dec s0 s); subst.
        * destruct (string_dec s name); subst.
          -- exfalso. apply H0. eexists; rewrite <- app_assoc; simpl; eauto.
          -- simpl in *.
             destruct (string_dec s s); subst; congruence.
        * specialize (IHents H1).
          destruct (string_dec s0 name); subst.
          -- simpl. destruct (string_dec name s); congruence.
          -- simpl. destruct (string_dec s0 s); congruence.
    - eapply find_subtree_update_subtree_oob; eauto.
  Qed.
  Proof.
   unfold tree_prune; intros.
    destruct (pathname_decide_prefix base pn).
    - deex.
      erewrite find_subtree_app in H1.
      erewrite find_subtree_app by eassumption.
      2: erewrite find_update_subtree; eauto.

      clear H.
      induction ents; simpl in *.
      + destruct suffix; simpl in *; try congruence.
      + destruct suffix; simpl in *; try congruence.
        destruct a; simpl in *.
        destruct (string_dec s0 s); subst.
        * destruct (string_dec s name); subst.
          -- exfalso. apply H0. eexists; rewrite <- app_assoc; simpl; eauto.
          -- simpl in *.
             destruct (string_dec s s); subst; congruence.
        * destruct (string_dec s0 name); subst; simpl in *; try congruence.
          destruct (string_dec s0 s); subst; simpl in *; try congruence.
          specialize (IHents H1).
          eauto.
    - eapply find_subtree_update_subtree_oob'; eauto.
  Qed.
  Proof.
    intros.
    destruct (pathname_decide_prefix cwd pathname).
    + destruct (pathname_decide_prefix (cwd ++ srcbase ++ [srcname]) pathname).
      - (* pathname is inside src subtree; contradiction *)
        destruct H7.
        rewrite H7 in H.
        unfold prefix in H.
        destruct H.
        eexists x; eauto.
       - (* pathname isn't inside src subtree *)
        destruct (pathname_decide_prefix (cwd ++ dstbase ++ [dstname]) pathname).
        ++ (* pathname is inside dst tree; contradiction *)
          destruct H8.
          rewrite H8 in *.
          unfold pathname_prefix in H0.
          destruct H0.
          eexists x; eauto.
        ++ (* pathname isn't inside src and isn't inside dst tree, but inside cwd *)
          deex.
          erewrite find_subtree_app; eauto.
          erewrite find_subtree_graft_subtree_oob; eauto.
          intro; apply H0. apply pathname_prefix_trim. eauto.
          erewrite find_subtree_prune_subtree_oob; eauto.
          intro; apply H. apply pathname_prefix_trim. eauto.
          erewrite find_subtree_app in H1; eauto.
    + (* pathname is outside of cwd *)
      unfold tree_graft, tree_prune.
      erewrite find_subtree_update_subtree_oob; eauto.
  Qed.
  Proof.
    intros.
    destruct (pathname_decide_prefix cwd pathname).
    + destruct (pathname_decide_prefix (cwd ++ srcbase ++ [srcname]) pathname).
      - (* pathname is inside src subtree; contradiction *)
        destruct H7.
        rewrite H7 in H.
        unfold pathname_prefix in H.
        destruct H.
        eexists x; eauto.
       - (* pathname isn't inside src subtree *)
        destruct (pathname_decide_prefix (cwd ++ dstbase ++ [dstname]) pathname).
        ++ (* pathname is inside dst tree; contradiction *)
          destruct H8.
          rewrite H8 in *.
          unfold pathname_prefix in H0.
          destruct H0.
          eexists x; eauto.
        ++ (* pathname isn't inside src and isn't inside dst tree, but inside cwd *)
          deex.
          erewrite find_subtree_app in H5; eauto.
          erewrite find_subtree_app.
          2: eauto.
          erewrite find_subtree_prune_subtree_oob'.
          4: {
            eapply find_subtree_graft_subtree_oob'.
            3: eauto.
            eauto.
            intro; apply H0. apply pathname_prefix_trim. eauto.
          }
          all: eauto.
          intro; apply H. apply pathname_prefix_trim. eauto.
    + (* pathname is outside of cwd *)
      unfold tree_graft, tree_prune.
      erewrite find_subtree_update_subtree_oob'; eauto.
  Qed. 
  Proof.
    intros.
    induction tree_elem.
    - intros. simpl in H. congruence.
    - destruct a.
      destruct (string_dec s name).
      rewrite cons_app.
      rewrite map_app.
      apply in_app_iff.
      simpl.
      left.
      auto.
      rewrite cons_app.
      rewrite map_app.
      apply in_or_app.
      right.
      apply IHtree_elem.
      rewrite cons_app in H.
      rewrite fold_right_app in H.
      simpl in H.
      destruct (string_dec s name).
      congruence.
      assumption.
  Qed.