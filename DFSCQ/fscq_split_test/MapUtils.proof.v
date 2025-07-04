  Proof.
    intros; apply Map.elements_3w.
  Qed.
  Proof.
    intros.
    apply Map.find_1 in H.
    erewrite Map.find_1 in H by (apply Map.add_1; hnf; auto).
    congruence.
  Qed.
  Proof.
    intros. destruct H as [v].
    erewrite MapProperties.cardinal_2 with (m:=Map.remove k m) (m':=m) (x:=k) (e:=v).
    omega.
    apply Map.remove_1; hnf; auto.
    intro.
    destruct (OT.eq_dec k y); unfold OT.eq in *; subst.
    - rewrite MapFacts.add_eq_o; auto.
      erewrite Map.find_1; eauto.
    - rewrite MapFacts.add_neq_o; auto.
      rewrite MapFacts.remove_neq_o; auto.
  Qed.
  Proof.
    intros.
    erewrite MapProperties.cardinal_2 with (m:=m).
    omega.
    eauto.
    intro.
    reflexivity.
  Qed.
  Proof.
    intros. destruct H.
    erewrite MapProperties.cardinal_2 with (m:=Map.remove k m).
    omega.
    apply Map.remove_1; hnf; auto.
    intro.
    destruct (OT.eq_dec k y); unfold OT.eq in *; subst.
    - rewrite MapFacts.add_eq_o; auto.
      rewrite MapFacts.add_eq_o; auto.
    - rewrite MapFacts.add_neq_o; auto.
      rewrite MapFacts.add_neq_o; try omega; auto.
      rewrite MapFacts.remove_neq_o; auto.
  Qed.
  Proof.
    intros.
    replace (Map.cardinal m) with ((Map.cardinal m - 1) + 1).
    erewrite <- map_remove_cardinal; eauto.
    apply map_add_dup_cardinal'; auto.
    destruct H.
    assert (Map.cardinal m <> 0); try omega.
    erewrite MapProperties.cardinal_2 with (m:=Map.remove k m).
    omega.
    apply Map.remove_1; reflexivity.
    intro.
    destruct (OT.eq_dec k y); unfold OT.eq in *; subst.
    - rewrite MapFacts.add_eq_o; auto.
      erewrite Map.find_1; eauto.
    - rewrite MapFacts.add_neq_o; auto.
      rewrite MapFacts.remove_neq_o; auto.
  Qed.
  Proof.
    intros.
    eexists; apply Map.elements_2.
    rewrite H.
    apply InA_cons_hd.
    constructor; hnf; eauto.
  Qed.
  Proof.
    intros.
    apply MapOrdProperties.elements_Equal_eqlistA in H.
    generalize dependent (Map.elements m2).
    generalize dependent (Map.elements m1).
    induction l.
    - intros. inversion H. reflexivity.
    - intros. destruct l0; inversion H. subst.
      inversion H3. destruct a; destruct p; simpl in *; subst.
      f_equal; eauto.
  Qed.
  Proof.
    induction l; simpl; intros; constructor.
    inversion H; subst.
    contradict H2.
    apply in_map_fst_exists_snd in H2; destruct H2.
    apply InA_alt.
    exists (fst a, x); intuition.
    destruct a; simpl in *.
    cbv; auto.
    inversion H; subst.
    apply IHl; auto.
  Qed.
  Proof.
    intros.
    rewrite <- app_nil_l.
    eapply NoDupA_split.
    rewrite app_nil_l. intuition eauto.
  Qed.
  Proof.
    unfold KNoDup; intros.
    eapply NoDupA_cons_inv; eauto.
  Qed.
  Proof.
    intros.
    apply KNoDup_NoDup.
    apply Map.elements_3w.
  Qed.
  Proof.
    induction l; intros; auto; inversion H; subst.
    inversion H1.
    destruct a0; simpl in *; hnf in *; subst; auto.
    simpl. right.
    apply IHl; auto.
  Qed.
  Proof.
    unfold map0; intros.
    apply Map.is_empty_2 in H.
    hnf; intros.
    rewrite MapFacts.empty_o.
    apply MapFacts.not_find_in_iff.
    cbv in *; intros.
    destruct H0; eapply H; eauto.
  Qed.
  Proof.
    intros.
    apply in_map_fst_exists_snd in H.
    destruct H.
    apply InA_alt.
    exists (a, x).
    split; auto.
    hnf; auto.
  Qed.
  Proof.
    intros; destruct a; simpl in *.
    eapply in_selN_exists in H.
    do 2 destruct H.
    rewrite map_length in H.
    apply InA_alt.
    eexists; split.
    2: apply in_selN_map; eauto.
    rewrite H0.
    hnf; auto.
    Unshelve.
    all : eauto.
  Qed.
  Proof.
    intros; destruct a; simpl in *.
    unfold KIn in *.
    apply InA_alt in H.
    inversion H.
    destruct x.
    intuition.
    unfold Map.eq_key in H1; simpl in *.
    rewrite H1.
    replace k0 with (fst (k0, v0)) by auto.
    eapply in_map; eauto.
  Qed.
  Proof.
    intros; split; intros.
    apply in_map_fst_exists_snd in H.
    destruct H.
    apply MapFacts.elements_in_iff.
    exists x.
    apply In_InA; auto.
    apply MapFacts.elements_in_iff in H.
    destruct H.
    apply InA_alt in H.
    destruct H; intuition.
    hnf in H0; simpl in *; intuition; subst.
    destruct x0; simpl in *; hnf in *; subst.
    generalize dependent (Map.elements m).
    induction l; intros; simpl; auto.
    inversion H1; intuition.
    destruct a; inversion H.
    tauto.
  Qed.
  Proof.
    intros; hnf; intro.
    destruct (OT.eq_dec y k1); destruct (OT.eq_dec y k2); subst; try congruence.
    rewrite MapFacts.add_eq_o by auto.
    rewrite MapFacts.add_neq_o by auto.
    rewrite MapFacts.add_eq_o; auto.
    setoid_rewrite MapFacts.add_eq_o at 2; auto.
    rewrite MapFacts.add_neq_o by auto.
    rewrite MapFacts.add_eq_o; auto.
    repeat rewrite MapFacts.add_neq_o; auto.
  Qed.
  Proof.
    intros; hnf; intros.
    destruct (OT.eq_dec y a); subst; try congruence.
    rewrite MapFacts.add_eq_o by auto.
    rewrite MapFacts.add_eq_o; auto.
    rewrite MapFacts.add_neq_o by auto.
    repeat rewrite MapFacts.add_neq_o; auto.
  Qed.
  Proof.
    intros; destruct a, b.
    destruct (OT.eq_dec k k0); subst.
    left; hnf; auto.
    right; hnf. tauto.
  Qed.
  Proof.
    intros.
    rewrite MapFacts.elements_o in H.
    apply MapProperties.elements_Empty in H0.
    rewrite H0 in H; simpl in H.
    congruence.
  Qed.
  Proof.
    intros.
    apply MapFacts.Equal_mapsto_iff; intros; split; intro.
    eapply Map.remove_3; eauto.
    apply MapFacts.remove_mapsto_iff; intuition.
    contradict H; subst.
    apply MapFacts.in_find_iff.
    apply Map.find_1 in H0.
    congruence.
  Qed.
  Proof.
    intros.
    erewrite mapeq_elements; eauto.
    apply map_remove_not_in_equal; auto.
  Qed.
  Proof.
    intros.
    rewrite MapFacts.elements_o.
    apply MapProperties.elements_Empty in H.
    rewrite H; simpl; auto.
  Qed.
  Proof.
    intros.
    apply MapFacts.not_find_in_iff.
    apply map_empty_find_none; auto.
  Qed.
  Proof.
    intros; cbv; intros.
    eapply Map.find_1 in H0.
    congruence.
  Qed.
  Proof.
    intros.
    eapply find_none_empty; intros.
    rewrite MapFacts.remove_o.
    destruct (OT.eq_dec a a0); auto.
    apply map_empty_find_none; auto.
  Qed.
  Proof.
    intros.
    apply MapFacts.not_find_in_iff in H.
    intuition.
    eapply Map.elements_2 in H0.
    apply Map.find_1 in H0.
    congruence.
  Qed.
  Proof.
    intros.
    apply not_In_not_InA.
    apply Map.remove_1; hnf; auto.
  Qed.
  Proof.
    intros.
    destruct (OT.eq_dec x y); hnf in *; subst.
    apply Map.remove_1; hnf; auto.
    destruct (MapFacts.In_dec (Map.remove y m) x).
    contradict H.
    eapply MapFacts.remove_neq_in_iff; eauto.
    auto.
  Qed.
  Proof.
    intros.
    apply MapFacts.find_mapsto_iff in H.
    apply MapFacts.in_find_iff.
    congruence.
  Qed.
  Proof.
    intros.
    apply MapFacts.in_find_iff.
    apply MapFacts.in_find_iff in H; auto.
  Qed.
  Proof.
    intros.
    apply InA_alt in H.
    destruct H as [y [? ?]].
    destruct x, y.
    cbv in H; subst.
    exists v0; simpl.
    apply In_InA; auto.
  Qed.
  Proof.
    intros; rewrite Map.cardinal_1; auto.
  Qed.
  Proof.
    induction ents; simpl; auto; intros.
    apply InA_cons.
    destruct (eq_key_dec a0 a); intuition.
    right; eapply IHents.
    destruct (f a); eauto.
    inversion H; subst; try congruence.
  Qed.
  Proof.
    induction ents; simpl; auto; intros.
    inversion H; subst.
    destruct (f a); intros; eauto.
    constructor.
    contradict H2.
    eapply InA_filter; eauto.
    apply IHents; eauto.
  Qed.
  Proof.
    intros.
    destruct (Map.find a m) eqn: Heq.
    rewrite map_remove_cardinal.
    omega.
    eexists; eapply Map.find_2; eauto.
    erewrite MapProperties.cardinal_m; eauto.
    apply map_remove_not_in_equal.
    apply MapFacts.not_find_in_iff; auto.
  Qed.
  Proof.
    unfold Proper, respectful; intros; subst.
    apply mapeq_elements; auto.
  Qed.
  Proof.
    cbv.
    intros.
    rewrite M.add_spec.
    auto.
  Qed.
  Proof.
    cbv [SS.Subset].
    intros.
    rewrite SS.add_spec in *.
    intuition subst; eauto.
    match goal with H: _ |- _ => rewrite H end.
    auto.
  Qed.
  Proof.
    induction l; cbn.
    intuition.
    intros.
    rewrite SS.add_spec.
    intuition subst; eauto.
    left.
    reflexivity.
  Qed.
  Proof.
    induction l; cbn; auto.
    intuition.
    inversion H.
    rewrite SetFacts.empty_iff in H.
    intuition.
    rewrite SS.add_spec in *.
    intuition.
    inversion H1; subst; auto.
  Qed.
  Proof.
    induction l; cbn; intros.
    intuition auto.
    inversion H0.
    rewrite SS.remove_spec in *.
    intuition subst.
    eapply IHl; eauto.
    inversion H; subst.
    congruence.
    eapply IHl; eauto.
  Qed.
  Proof.
    induction l; cbn; intros.
    auto.
    rewrite SS.add_spec in *.
    intuition eauto.
    contradiction H.
    eauto.
  Qed.
  Proof.
    induction l; cbn; intros.
    auto.
    rewrite SS.remove_spec.
    intuition auto.
  Qed.
  Proof.
    cbv [SS.Subset].
    induction n, l; cbn; intros; auto.
    rewrite SS.remove_spec in *.
    intuition eauto.
    setoid_rewrite SS.add_spec in H.
    eapply in_fold_right_remove in H1.
    intuition eauto.
    eapply H in H0.
    intuition auto.
    eapply in_fold_right_not_added; eauto.
    rewrite SS.add_spec.
    eapply in_fold_right_remove in H0.
    intuition idtac.
    eapply H in H1.
    rewrite SS.add_spec in *.
    intuition auto.
    right.
    eapply IHn; eauto.
    eapply in_fold_right_remove_notin; eauto.
  Qed.
  Proof.
    cbv; intros.
    rewrite M.inter_spec in *.
    intuition.
  Qed.
  Proof.
    cbv; intros.
    rewrite M.inter_spec in *.
    intuition.
  Qed.
  Proof.
    cbv. intros.
    rewrite SetFacts.empty_iff in *.
    intuition.
  Qed.
  Proof.
    intros.
    rewrite <- NoDup_NoDupA_eq.
    apply AddrSet_AVL.elements_spec2w.
    intuition.
  Qed.
  Proof.
    intros.
    rewrite <- AddrSet_AVL.elements_spec1.
    rewrite InA_alt.
    intuition.
    eexists; eauto.
    destruct H; intuition (subst; auto).
  Qed.