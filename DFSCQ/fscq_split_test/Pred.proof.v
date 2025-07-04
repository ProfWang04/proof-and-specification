Proof.
  intros.
  inversion H.
  inversion H0.
  eauto.
Qed.
  Proof. auto. Qed.
End Sep_Star.

Proof.
  pred.
Qed.
Proof.
  split; unfold mem_disjoint, not; intros; repeat deex; eauto 10.
Qed.
Proof.
  unfold mem_disjoint, mem_union; intuition; repeat deex.
  case_eq (m2 a); intros.
  - apply H. eauto.
  - rewrite H1 in H3.
    apply H0. repeat eexists; eauto. rewrite H2. eauto.
Qed.
Proof.
  unfold mem_disjoint, mem_union; intuition; repeat deex.
  case_eq (m2 a); intros.
  - apply H. eauto.
  - case_eq (m1 a); intros.
    + apply H0. repeat eexists; eauto. rewrite H1. eauto.
    + rewrite H4 in H2. firstorder.
Qed.
Proof.
  unfold mem_disjoint, mem_union; intuition; repeat deex.
  apply H; exists a; destruct (m1 a); eauto.
Qed.
Proof.
  unfold mem_disjoint, mem_union; intuition; repeat deex.
  apply H; exists a. destruct (m1 a); destruct (m2 a); try congruence; eauto.
Qed.
Proof.
  unfold mem_disjoint, upd, not; intros; repeat deex;
    destruct (AEQ a0 a); subst; eauto 10.
Qed.
Proof.
  unfold mem_disjoint; intros; firstorder.
  pose proof (H a); firstorder.
  pose proof (H1 v); firstorder.
  destruct (m2 a); auto.
  pose proof (H2 v0); firstorder.
Qed.
Proof.
  unfold insert, mem_disjoint; intros.
  contradict H; repeat deex.
  destruct (AEQ a0 a) in H1; subst; try congruence.
  destruct (m1 a) eqn:?;
  exists a0; do 2 eexists; eauto.
Qed.
Proof.
  unfold mem_disjoint, mem_union; intros; apply functional_extensionality; intros.
  case_eq (m1 x); case_eq (m2 x); intros; eauto; destruct H; eauto.
Qed.
Proof.
  intros.
  rewrite mem_union_comm in H1 by auto.
  replace (mem_union m1 m2') with (mem_union m2' m1) in H1 by
    (apply mem_union_comm; apply mem_disjoint_comm; auto).
  apply functional_extensionality; intros.
  assert (mem_union m2 m1 x = mem_union m2' m1 x) by congruence.
  unfold mem_disjoint, mem_union in *.
  case_eq (m2 x); case_eq (m2' x); intros;
    replace (m2 x) in *; replace (m2' x) in *;
    eauto.
  destruct H.
  repeat eexists; eauto.
  destruct H0.
  repeat eexists; eauto.
Qed.
Proof.
  unfold mem_disjoint, mem_union; intros; rewrite H0; auto.
Qed.
Proof.
  unfold mem_union, upd; intros; apply functional_extensionality; intros.
  destruct (AEQ x a); eauto.
Qed.
Proof.
  unfold mem_union, mem_disjoint; intros; apply functional_extensionality; intuition.
  destruct (m1 x); auto.
Qed.
Proof.
  intros.
  unfold mem_union.
  destruct (m1 a); eauto.
Qed.
Proof.
  unfold mem_union; intros.
  destruct (m1 a) eqn:?; destruct (m2 a) eqn:?; intuition.
  congruence.
Qed.
Proof.
  intros.
  unfold mem_union.
  destruct (m1 a); eauto.
Qed.
Proof.
  intros.
  unfold mem_union.
  destruct (m1 a); eauto.
  congruence.
Qed.
Proof.
  unfold mem_union; intros.
  apply functional_extensionality; intros.
  destruct (AEQ a x); subst.
  repeat rewrite insert_eq; auto.
  rewrite H; auto.
  repeat rewrite insert_ne; auto.
Qed.
Proof.
  unfold mem_disjoint, mem_union; intuition repeat deex.
  destruct (m1 a) eqn:?.
  - inversion H2; subst.
    apply H; do 3 eexists; intuition eauto.
  - apply H0; do 3 eexists; intuition eauto.
Qed.
Proof.
  intros.
  apply mem_disjoint_comm.
  apply mem_disjoint_mem_union_split_l.
  apply mem_disjoint_comm; auto.
  apply mem_disjoint_comm; auto.
Qed.
Proof.
  unfold pimpl; unfold_sep_star; pred.
  exists m2; exists m1. intuition eauto using mem_union_comm. apply mem_disjoint_comm; auto.
Qed.
Proof.
  unfold piff; split; apply sep_star_comm1.
Qed.
Proof.
  unfold pimpl; unfold_sep_star; pred.
  eexists; eexists (mem_union _ _); intuition eauto.
  apply mem_union_assoc; auto.
  apply mem_disjoint_assoc_1; auto.
  eexists; eexists; intuition eauto.
  eapply mem_disjoint_union; eauto.
Qed.
Proof.
  unfold pimpl; unfold_sep_star; pred.
  eexists (mem_union _ _); eexists; intuition eauto.
  rewrite mem_union_assoc; auto.
  apply mem_disjoint_comm. eapply mem_disjoint_union. apply mem_disjoint_comm.
  rewrite mem_union_comm. eauto. apply mem_disjoint_comm. eauto.
  apply mem_disjoint_assoc_2; eauto.
  apply mem_disjoint_assoc_2; eauto.
  repeat eexists; eauto.
  apply mem_disjoint_comm. eapply mem_disjoint_union.
  rewrite mem_union_comm; [|apply mem_disjoint_comm;eassumption].
  apply mem_disjoint_comm; assumption.
Qed.
Proof.
  split; [ apply sep_star_assoc_1 | apply sep_star_assoc_2 ].
Qed.
Proof.
  unfold_sep_star; intros.
  do 2 eexists; intuition.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  unfold pimpl, exis; unfold_sep_star; intros.
  repeat deex.
  eapply H.
  do 3 eexists.
  intuition eauto.
Qed.
Proof.
  unfold pimpl, exis; unfold_sep_star; intros.
  repeat deex.
  do 2 eexists.
  intuition eauto.
Qed.
Proof.
  unfold pimpl, exis; unfold_sep_star; intros.
  repeat deex.
  do 3 eexists.
  intuition eauto.
Qed.
Proof.
  unfold pimpl, exis; unfold_sep_star; intros.
  repeat deex.
  do 3 eexists.
  intuition eauto.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  unfold piff; intuition; eapply pimpl_trans; eauto.
Qed.
Proof.
  unfold piff; intuition.
Qed.
Proof.
  unfold piff; intuition.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  unfold pimpl; unfold_sep_star; intros.
  do 2 deex.
  do 2 eexists.
  intuition eauto.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  unfold pimpl, lift_empty; unfold_sep_star; intros.
  repeat deex.
  assert (mem_union m1 m2 = m1).
  apply functional_extensionality; unfold mem_union; intros.
  case_eq (m1 x); pred.
  rewrite H. eauto.
Qed.
Proof.
  unfold pimpl, lift_empty, and; unfold_sep_star; intros.
  exists (fun _ => None).
  exists m.
  intuition firstorder.
  unfold mem_disjoint. intuition. repeat deex. congruence.
Qed.
Proof.
  intros.
  eapply pimpl_trans; [|apply sep_star_comm].
  apply sep_star_lift_r'.
  firstorder.
Qed.
Proof.
  unfold lift_empty; unfold_sep_star; intros.
  repeat deex.
  assert (mem_union m1 m2 = m1).
  apply functional_extensionality; unfold mem_union; intros.
  case_eq (m1 x); pred.
  congruence.
Qed.
Proof.
  unfold lift_empty; unfold_sep_star; intros.
  exists m. exists (fun _ => None).
  intuition.
  apply functional_extensionality; unfold mem_union; intros.
  destruct (m x); auto.
  unfold mem_disjoint; intro.
  repeat deex.
  congruence.
Qed.
Proof.
  unfold pimpl; unfold_sep_star; intros.
  repeat eexists; eauto.
  unfold mem_union; eauto.
  unfold mem_disjoint; pred.
Qed.
Proof.
  unfold pimpl; unfold_sep_star; intros.
  unfold emp in *; pred.
  assert (mem_union m1 m2 = m2).
  apply functional_extensionality; unfold mem_union; intros.
  case_eq (m1 x); intuition. rewrite H1 in H0; pred.
  pred.
Qed.
Proof.
  intros; split; [ apply pimpl_star_emp | apply star_emp_pimpl ].
Qed.
Proof.
  intros.
  eapply pimpl_trans.
  2: apply sep_star_comm.
  apply emp_star.
Qed.
Proof.
  unfold piff, pimpl; unfold_sep_star; intuition;
    repeat deex; repeat eexists; eauto.
Qed.
Proof.
  unfold piff, pimpl; unfold_sep_star; intuition;
    repeat deex; repeat eexists; eauto.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  unfold and, lift, lift_empty, pimpl; unfold_sep_star.
  intros; repeat deex.
  assert (mem_union m1 m2 = m1).
  apply functional_extensionality; intros.
  unfold mem_union. destruct (m1 x); eauto.
  congruence.
Qed.
Proof.
  unfold and, lift, lift_empty, pimpl; unfold_sep_star.
  intros; repeat deex.
  do 2 eexists; intuition; eauto.
  - unfold mem_union.
    apply functional_extensionality.
    intros; destruct (m x); auto.
  - unfold mem_disjoint, not; intros.
    repeat deex.
    congruence.
Qed.
Proof.
  unfold exact_domain, ptsto; intuition.
  destruct (AEQ a a0); subst; intuition; congruence.
  destruct (AEQ a a0); subst; intuition; congruence.
Qed.
Proof.
  unfold exact_domain, ptsto; intuition.
  destruct H as [? [? ?] ].
  destruct H0 as [? [? ?] ].
  destruct (AEQ a a0); subst; intuition; congruence.
  destruct H as [? [? ?] ].
  destruct H0 as [? [? ?] ].
  destruct (AEQ a a0); subst; intuition; congruence.
Qed.
Proof.
  unfold ptsto; intros; split; intros.
  destruct (AEQ a a); congruence.
  destruct (AEQ a' a); congruence.
Qed.
Proof.
  unfold ptsto, exis; intros.
  exists v; split; intros.
  destruct (AEQ a a); congruence.
  destruct (AEQ a' a); congruence.
Qed.
Proof.
  unfold ptsto; unfold_sep_star.
  intros; repeat deex.
  apply mem_union_addr; eauto.
Qed.
Proof.
  unfold ptsto; unfold_sep_star.
  intros; repeat deex.
  rewrite mem_union_comm; eauto.
  apply mem_union_addr; eauto.
  rewrite mem_disjoint_comm; eauto.
Qed.
Proof.
  unfold ptsto; intuition.
Qed.
Proof.
  unfold upd; unfold_sep_star; intros; repeat deex.
  exists m.
  exists (fun a' => if AEQ a' a then Some v else None).
  split; [|split].
  - apply functional_extensionality; intro.
    unfold mem_union; destruct (AEQ x a); subst; intuition.
    rewrite H0; auto.
    destruct (m x); auto.
  - unfold mem_disjoint in *. intuition. repeat deex.
    destruct (AEQ a0 a); subst; intuition; pred.
  - intuition; eauto.
    unfold ptsto; intuition.
    destruct (AEQ a a); pred.
    destruct (AEQ a' a); pred.
Qed.
Proof.
  unfold insert; unfold_sep_star; intros; repeat deex.
  exists m.
  exists (fun a' => if AEQ a' a then Some v else None).
  split; [|split].
  - apply functional_extensionality; intro.
    unfold mem_union; destruct (AEQ x a); subst; intuition.
    rewrite H0; auto.
    destruct (m x); auto.
  - unfold mem_disjoint in *. intuition. repeat deex.
    destruct (AEQ a0 a); subst; intuition; pred.
  - intuition; eauto.
    unfold ptsto; intuition.
    destruct (AEQ a a); pred.
    destruct (AEQ a' a); pred.
Qed.
Proof.
  unfold upd; unfold_sep_star; intros; repeat deex.
  exists (fun a' => if AEQ a' a then Some v else None).
  exists m2.
  split; [|split].
  - apply functional_extensionality; intro.
    unfold mem_union; destruct (AEQ x a); eauto.
    destruct H1; repeat deex.
    rewrite H1; auto.
  - unfold mem_disjoint in *. intuition. repeat deex.
    apply H.
    destruct H1; repeat deex.
    repeat eexists; eauto.
    destruct (AEQ a0 a); subst; eauto.
    pred.
  - intuition eauto.
    unfold ptsto; intuition.
    destruct (AEQ a a); pred.
    destruct (AEQ a' a); pred.
Qed.
Proof.
  intros.
  apply ptsto_valid in H as H'.
  generalize dependent H.
  unfold updSome; unfold_sep_star; intros; repeat deex.
  exists (fun a' => if AEQ a' a then Some v else None).
  exists m2.
  rewrite H'.
  split; [|split].
  - apply functional_extensionality; intro.
    unfold mem_union; destruct (AEQ x a); eauto.
    destruct H1; repeat deex.
    rewrite H1; auto.
  - unfold mem_disjoint in *. intuition. repeat deex.
    apply H.
    destruct H1; repeat deex.
    repeat eexists; eauto.
    destruct (AEQ a0 a); subst; eauto.
    pred.
  - intuition eauto.
    unfold ptsto; intuition.
    destruct (AEQ a a); pred.
    destruct (AEQ a' a); pred.
Qed.
Proof.
  intros.
  apply sep_star_comm.
  eapply ptsto_upd.
  apply sep_star_comm.
  eauto.
Qed.
Proof.
  unfold upd, ptsto; unfold_sep_star; intros; repeat deex.
  exists (fun a' => if AEQ a' a then Some v else None).
  exists (fun a' => if AEQ a' b then m a' else m2 a').
  split; [|split].
  - apply functional_extensionality; intros.
    unfold mem_union in *. pose proof (equal_f H1 x); clear H1; simpl in *.
    destruct (AEQ x a); subst.
    + rewrite H3 in H2. destruct (AEQ a b); congruence.
    + rewrite H5 in H2 by congruence.
      destruct (AEQ x b); congruence.
  - unfold mem_disjoint in *. intuition. repeat deex.
    apply H0; clear H0.
    destruct (AEQ a0 a); destruct (AEQ a0 b); subst; try congruence.
    repeat eexists; eauto.
  - intuition eauto.
    destruct (AEQ a a); congruence.
    destruct (AEQ a' a); congruence.
    firstorder.
Qed.
Proof.
  unfold delete; unfold_sep_star; intros; repeat deex.
  match goal with
  | [ |- F ?m ] => replace (m) with m2; eauto
  end.
  apply functional_extensionality; intro.
  unfold mem_union; destruct (AEQ x a); eauto.
  - subst.
    unfold mem_disjoint in *.
    case_eq (m2 a); intros; try congruence.
    exfalso. apply H.
    exists a. exists v0. exists v.
    unfold ptsto in *; intuition.
  - case_eq (m1 x); intros; try congruence.
    unfold ptsto in *; intuition.
    rewrite H4 in H0; eauto.
    congruence.
Qed.
Proof.
  intros.
  eapply ptsto_delete.
  apply sep_star_comm.
  eauto.
Qed.
Proof.
  intros.
  unfold_sep_star; unfold ptsto.
  exists (mem_except m a).
  exists (fun a' => if (AEQ a' a) then Some v else None).
  split; [ | split ].

  apply functional_extensionality; intros; auto.
  unfold mem_union, mem_except.
  destruct (AEQ x a); subst; auto.
  destruct (m x); auto.

  unfold mem_disjoint, mem_except.
  intuition; repeat deex.
  destruct (AEQ a0 a); subst; auto.
  inversion H1.
  inversion H2.

  unfold any, mem_except; intuition.
  destruct (AEQ a a); intuition.
  destruct (AEQ a' a); intuition.
  contradict H0; auto.
 Qed.
Proof.
  intros.
  repeat deex.
  apply H1 in H; clear H1.
  apply H2 in H0; clear H2.
  apply ptsto_valid in H.
  apply ptsto_valid in H0.
  repeat deex.
  congruence.
Qed.
Proof.
  intros; subst.
  apply pimpl_refl.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  intros.
  eapply pimpl_trans; [|apply pimpl_star_emp]; apply pimpl_any.
Qed.
Proof.
  intros; subst; firstorder.
Qed.
Proof.
  unfold_sep_star; unfold pimpl, indomain, mem_union.
  intros.
  repeat deex.
  edestruct H; eauto.
  rewrite H1.
  eauto.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  unfold_sep_star; unfold ptsto, mem_union, exis.
  intros.
  repeat deex.
  rewrite H2.
  auto.
Qed.
Proof.
  intros.
  apply sep_star_ptsto_some in H.
  rewrite H in H0.
  inversion H0; auto.
Qed.
Proof.
  intros.
  eapply sep_star_ptsto_some in H.
  repeat deex; eexists; eauto.
Qed.
Proof.
  split.
  - unfold_sep_star; unfold pimpl, or.
    intros; repeat deex.
    + left. do 2 eexists. eauto.
    + right. do 2 eexists. eauto.
  - apply pimpl_or_l.
    + apply pimpl_sep_star; [apply pimpl_refl|].
      apply pimpl_or_r; left; apply pimpl_refl.
    + apply pimpl_sep_star; [apply pimpl_refl|].
      apply pimpl_or_r; right; apply pimpl_refl.
Qed.
Proof.
  unfold_sep_star; unfold pimpl, and.
  intros; repeat deex; do 2 eexists; eauto.
Qed.
Proof.
  unfold_sep_star; unfold pimpl, and.
  intros; repeat deex; do 2 eexists; eauto.
Qed.
Proof.
  unfold_sep_star; unfold pimpl, lift_empty, mem_union.
  firstorder; rewrite H.
  destruct (x a) eqn:?; try congruence.
Qed.
Proof.
  unfold_sep_star; unfold pimpl, and, lift_empty, mem_union.
  intros; intuition; repeat deex.
  assert (m2 = m3).
  apply functional_extensionality; intros.
  apply equal_f with (x0 := x) in H1.
  rewrite H5, H8 in H1; auto.
  subst; do 2 eexists; intuition.
Qed.
Proof.
  unfold_sep_star; unfold pimpl, and, lift_empty, mem_union.
  intros; intuition; repeat deex.
  assert (m0 = m1).
  apply functional_extensionality; intros.
  apply equal_f with (x0 := x) in H1.
  destruct (m1 x); destruct (m0 x); try congruence.
  subst; do 2 eexists; intuition.
Qed.
Proof.
  intros. unfold_sep_star.
  exists (fun _ => None). exists m.
  intuition; hnf; try tauto; firstorder discriminate.
Qed.
Proof.
  unfold_sep_star; firstorder discriminate.
Qed.
Proof.
  unfold_sep_star; firstorder discriminate.
Qed.
Proof.
  unfold ptsto; intros; apply functional_extensionality; intros.
  destruct H; destruct H0.
  destruct (AEQ a x); subst; try congruence.
  erewrite H1; eauto.
  erewrite H2; eauto.
Qed.
Proof.
  unfold not; intros.
  subst.
  apply sep_star_ptsto_some in H.
  apply sep_star_ptsto_some in H0.
  congruence.
Qed.
Proof.
  intros.
  apply functional_extensionality; unfold emp in *; congruence.
Qed.
Proof.
  unfold_sep_star.
  intros.
  destruct H. destruct H. destruct H. destruct H0. destruct H1.
  cut (x = empty_mem).
  cut (x0 = empty_mem).
  intros; subst; intuition.

  unfold mem_union, empty_mem in *.
  apply functional_extensionality; intro fa.
  apply equal_f with (x1:=fa) in H.
  destruct (x0 fa); auto.
  destruct (x fa); auto.
  inversion H.

  unfold mem_union, empty_mem in *.
  apply functional_extensionality; intro fa.
  apply equal_f with (x1:=fa) in H.
  destruct (x fa); auto.
Qed.
Proof.
  unfold empty_mem, ptsto.
  intuition discriminate.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  intros; apply functional_extensionality; intros.
  firstorder.
Qed.
Proof.
  unfold pimpl; intros.
  apply emp_empty_mem_only in H0.
  subst; auto.
Qed.
Proof.
  unfold mem_union, empty_mem; intros.
  split.

  apply functional_extensionality; intros.
  apply equal_f with (x0 := x) in H.
  destruct (m1 x); auto.

  apply functional_extensionality; intros.
  apply equal_f with (x0 := x) in H.
  destruct (m1 x); auto.
  congruence.
Qed.
Proof.
  unfold_sep_star.
  unfold pimpl; intros.
  intuition.

  specialize (H m H0); repeat deex.
  apply emp_empty_mem_only in H0.
  rewrite H0.
  apply emp_mem_union in H0; intuition; subst; auto.

  specialize (H m H0); repeat deex.
  apply emp_empty_mem_only in H0.
  rewrite H0.
  apply emp_mem_union in H0; intuition; subst; auto.
Qed.
Proof.
  unfold emp, ptsto, pimpl, not; intros.
  specialize (H empty_mem).
  edestruct H.
  firstorder.
  unfold empty_mem in *; congruence.
Qed.
Proof.
  unfold mem_union; intros; apply functional_extensionality; intros.
  firstorder.
Qed.
Proof.
  unfold mem_union; intros; apply functional_extensionality; intros.
  destruct (m x); auto.
Qed.
Proof.
  unfold mem_disjoint, empty_mem, not. intros; repeat deex. congruence.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  intros; unfold notindomain.
  pose proof (H a); auto.
Qed.
Proof.
  unfold pimpl; intros.
  apply emp_notindomain; auto.
Qed.
Proof.
  unfold emp, mem_except; intros.
  destruct (AEQ a0 a); auto.
Qed.
Proof.
  unfold mem_except; intros.
  apply functional_extensionality; intros.
  destruct (AEQ x a); auto.
Qed.
Proof.
  intros.
  unfold mem_except.
  destruct (AEQ0 a a); congruence.
Qed.
Proof.
  unfold mem_except; intros; destruct (AEQ a a); congruence.
Qed.
Proof.
  unfold mem_except; intros; destruct (AEQ a' a); congruence.
Qed.
Proof.
  intros; apply functional_extensionality; intros.
  destruct (AEQ a x); subst.
  repeat rewrite upd_eq by auto; auto.
  repeat rewrite upd_ne by auto; rewrite mem_except_ne; auto.
Qed.
Proof.
  intros; apply functional_extensionality; intros.
  unfold insert, upd, mem_except.
  destruct (AEQ x a); subst; auto.
  rewrite H.
  destruct (AEQ a a); congruence.
Qed.
Proof.
  unfold mem_except, upd.
  intros; apply functional_extensionality; intros.
  destruct (AEQ x a); auto.
Qed.
Proof.
  unfold mem_except, insert.
  intros; apply functional_extensionality; intros.
  destruct (AEQ x a); eauto.
Qed.
Proof.
  intros.
  apply functional_extensionality; intros.
  unfold mem_except.
  destruct (AEQ x a); congruence.
Qed.
Proof.
  unfold mem_union, mem_except, ptsto.
  intuition.
  apply functional_extensionality; intros.
  destruct (AEQ x a2) eqn:Heq; auto.
  destruct (m1 x) eqn:Hx; auto; subst.
  pose proof (H2 a2 H) as Hy.
  rewrite Hx in Hy.
  inversion Hy.
Qed.
Proof.
  unfold mem_disjoint, mem_except; intuition.
  repeat deex.
  destruct (AEQ a0 a).
  inversion H2.
  apply H.
  firstorder.
Qed.
Proof.
  unfold notindomain, mem_union; split; intros; intuition.
  destruct (m1 a); auto.
  destruct (m1 a); auto.
  inversion H.
  rewrite H0; auto.
Qed.
Proof.
  unfold notindomain, indomain.
  firstorder.
  rewrite H in H0.
  inversion H0.
Qed.
Proof.
  unfold notindomain, mem_except; intros.
  destruct (AEQ a a'); firstorder.
Qed.
Proof.
  unfold notindomain, mem_except; intros.
  destruct (AEQ a a'); firstorder.
Qed.
Proof.
  unfold notindomain, mem_except; intros.
  apply functional_extensionality; intros.
  destruct (AEQ x a); subst; auto.
Qed.
Proof.
  unfold notindomain, mem_except; intros.
  destruct (AEQ a a); congruence.
Qed.
Proof.
  unfold mem_except; intros.
  destruct (AEQ a a'); firstorder.
Qed.
Proof.
  unfold notindomain, indomain; split; intros; destruct (m a);
    try congruence.
  destruct 1; discriminate.
  exfalso; eauto.
Qed.
Proof.
  unfold indomain; intros.
  destruct H.
  rewrite upd_ne in H; auto.
  eexists; eauto.
Qed.
Proof.
  unfold notindomain, indomain.
  intros; destruct (m a) eqn:Heq.
  left; exists v; auto.
  right; auto.
Qed.
Proof.
  unfold ptsto; unfold_sep_star.
  intuition; repeat deex.
  replace ((mem_except (mem_union m1 m2) a)) with m2; auto.

  unfold mem_except.
  apply functional_extensionality; intro.
  destruct (AEQ x a); subst.
  eapply mem_disjoint_either; eauto.

  unfold mem_union.
  pose proof (H4 x); intuition.
  rewrite H1; simpl; auto.
Qed.
Proof.
  unfold indomain, ptsto; unfold_sep_star; intros.
  exists (fun a' => if (AEQ a' a) then Some v else None).
  exists (mem_except m a).
  split; [ | split].

  apply functional_extensionality; intro.
  unfold mem_union, mem_except.
  destruct (AEQ x a); subst; auto.

  unfold mem_disjoint, mem_except; intuition; repeat deex.
  destruct (AEQ a0 a); congruence.

  intuition.
  destruct (AEQ a a); subst; try congruence.
  destruct (AEQ a' a); subst; try congruence.
Qed.
Proof.
  unfold indomain; intros.
  destruct H; exists x.
  destruct (AEQ a a'); subst.
  unfold mem_except in H.
  destruct (AEQ a' a'); congruence.
  eapply indomain_mem_except; eauto.
Qed.
Proof.
  unfold_sep_star.
  intros; repeat deex.
  eexists; exists (mem_except m2 a'); intuition eauto.
  eapply mem_except_union_comm; eauto.
  apply mem_disjoint_mem_except; auto.
Qed.
Proof.
  unfold_sep_star.
  intros; repeat deex.
  eexists; exists (mem_except m2 a'); intuition eauto.
  eapply mem_except_union_comm; eauto.
  apply mem_disjoint_mem_except; auto.
  exists (diskIs (mem_except m2 a')). firstorder.
Qed.
Proof.
  intros.
  apply functional_extensionality; intros.
  destruct (AEQ x a); destruct (AEQ x a'); subst; subst; auto.
  rewrite mem_except_ne; auto.
  repeat rewrite mem_except_eq; auto.
  repeat rewrite mem_except_eq; auto.
  rewrite mem_except_ne; auto.
  rewrite mem_except_eq; auto.
  repeat rewrite mem_except_ne; auto.
Qed.
Proof.
  unfold exact_domain; split; apply functional_extensionality; intros;
    specialize (H m1 m1' H3 H4 x);
    unfold mem_union in H0;
    apply equal_f with (x) in H0.
  - destruct (m1 x); destruct (m1' x); firstorder.
  - unfold mem_disjoint in *.
    firstorder.
    specialize (H1 x).
    specialize (H2 x).
    simpl in *.
    destruct (m1 x); destruct (m1' x); destruct (m2 x); destruct (m2' x); firstorder;
      exfalso; eauto.
Qed.
Proof.
  intros.
  apply and_comm.
  apply mem_disjoint_comm in H1.
  apply mem_disjoint_comm in H2.
  eapply exact_domain_disjoint_union; eauto.
  setoid_rewrite mem_union_comm at 1 2; auto.
Qed.
Proof.
  unfold septract; unfold_sep_star; unfold pimpl; intros; repeat deex.
  rewrite mem_union_comm in H3 by eauto.
  apply mem_disjoint_comm in H1.
  edestruct exact_domain_disjoint_union; try eassumption.
  congruence.
Qed.
Proof.
  unfold septract; unfold pimpl; intros; repeat deex.
  eauto.
Qed.
Proof.
  unfold septract; unfold pimpl; intros; repeat deex.
  eauto.
Qed.
Proof.
  unfold strictly_exact, exact_domain; intros.
  specialize (H m1 m2 H0 H1).
  subst; intuition.
Qed.
Proof.
  unfold strictly_exact, precise; eauto.
Qed.
Proof.
  unfold ptsto, strictly_exact; intros.
  apply functional_extensionality; intros; intuition.
  destruct (AEQ a x); subst; try congruence.
  rewrite H2 by eauto.
  rewrite H3 by eauto.
  eauto.
Qed.
Proof.
  unfold emp, strictly_exact; intros.
  apply functional_extensionality; intros; congruence.
Qed.
Proof.
  unfold exact_domain; unfold_sep_star; unfold mem_union; intros.
  repeat deex;
    specialize (H _ _ H5 H6 a);
    specialize (H0 _ _ H7 H9 a);
    destruct (m0 a); destruct (m2 a); intuition; congruence.
Qed.
Proof.
  unfold strictly_exact; unfold_sep_star; unfold mem_union; intros.
  repeat deex.
  specialize (H _ _ H4 H5).
  specialize (H0 _ _ H6 H8).
  subst.
  eauto.
Qed.
Proof.
  unfold precise; unfold_sep_star; intros; repeat deex.
  specialize (H m0 (mem_union m3 m2') m2 (mem_union m4 m1')).
  specialize (H0 m3 (mem_union m0 m2') m4 (mem_union m2 m1')).
  rewrite H; clear H; eauto.
  rewrite H0; clear H0; eauto.
  - rewrite <- mem_union_assoc; try apply mem_disjoint_comm; auto.
    rewrite <- mem_union_assoc; try apply mem_disjoint_comm; auto.
    rewrite <- (mem_union_comm H5).
    rewrite <- (mem_union_comm H4).
    auto.
    rewrite <- (mem_union_comm H4). apply mem_disjoint_comm. eauto.
    rewrite <- (mem_union_comm H5). apply mem_disjoint_comm. eauto.
  - rewrite (mem_union_comm H5) in H3.
    apply mem_disjoint_assoc_1; auto; try apply mem_disjoint_comm; auto.
  - rewrite (mem_union_comm H4) in H2.
    apply mem_disjoint_assoc_1; auto; try apply mem_disjoint_comm; auto.
  - repeat rewrite <- mem_union_assoc; auto.
Qed.
Proof.
  unfold foral_, strictly_exact; intros.
  specialize (H a).
  eauto.
Qed.
Proof.
  unfold pimpl, ptsto; intuition.
  specialize (H empty_mem).
  destruct H.
  apply emp_empty_mem.
  unfold empty_mem in H; congruence.
Qed.
Proof.
  unfold pimpl, ptsto, exis; intuition.
  specialize (H empty_mem).
  destruct H.
  apply emp_empty_mem.
  destruct H.
  unfold empty_mem in H; congruence.
Qed.
Proof.
  unfold_sep_star; unfold pimpl, and, lift_empty.
  intuition; repeat deex.
  assert (m2 = m3); subst.
  - apply functional_extensionality; intros.
    unfold mem_union in *.
    destruct (AEQ x a); subst.
    + eapply equal_f with (x := a) in H1.
      unfold ptsto in *; intuition.
      erewrite mem_disjoint_either with (m2 := m1) (m1 := m2) in H1; eauto.
      erewrite mem_disjoint_either with (m2 := m0) (m1 := m3) in H1; eauto.
      apply mem_disjoint_comm; eauto.
      apply mem_disjoint_comm; eauto.
    + unfold ptsto in *; intuition.
      rewrite H7; auto. rewrite H8; auto.
  - assert (m0 = m1); subst.
    apply mem_disjoint_comm in H0; apply mem_disjoint_comm in H.
    eapply mem_disjoint_union_cancel; eauto.
    rewrite mem_union_comm by eauto.
    setoid_rewrite mem_union_comm at 2; auto.
    exists (mem_union m1 m3), empty_mem; intuition.
    rewrite mem_union_empty_mem'; intuition.
    apply mem_disjoint_comm; apply mem_disjoint_empty_mem.
    do 2 eexists; intuition.
    eapply ptsto_eq with (a := a) (m := m3).
    exact H6. exact H4.
    exists emp; apply emp_star_r.
    exists emp; apply emp_star_r.
Qed.
Proof.
  split.
  exact (@piff_refl AT AEQ V).
  exact (@piff_comm AT AEQ V).
  exact (@piff_trans AT AEQ V).
Qed.
Proof.
  split.
  exact (@pimpl_refl AT AEQ V).
  exact (@pimpl_trans AT AEQ V).
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  intros p p' Hp q q' Hq m m' Hm H.
  subst.
  eapply pimpl_apply; [| eassumption ].
  apply pimpl_sep_star; assumption.
Qed.
Proof.
  intros p p' Hp q q' Hq m m' Hm H.
  subst.
  eapply pimpl_apply; [| eassumption ].
  apply pimpl_sep_star; assumption.
Qed.
Proof.
  intros p p' Hp q q' Hq m m' Hm H.
  subst.
  eapply pimpl_apply; [| eassumption ].
  apply pimpl_sep_star. 
  apply Hp.
  apply Hq.
Qed.
Proof.
  intros p p' Hp q q' Hq m m' Hm.
  subst; split; intros.
  - eapply pimpl_apply; [| eassumption ]. apply pimpl_sep_star. apply Hp. apply Hq.
  - eapply pimpl_apply; [| eassumption ]. apply pimpl_sep_star. apply Hp. apply Hq.
Qed.
Proof.
  congruence.
Qed.
Proof.
  congruence.
Qed.
Proof.
  intros a b H c d H'.
  split; ( apply pimpl_sep_star; [ apply H | apply H' ] ).
Qed.
Proof.
  intros a b H c d H'.
  apply pimpl_sep_star; assumption.
Qed.
Proof.
  intros a b H c d H'.
  apply pimpl_sep_star; assumption.
Qed.
Proof.
  congruence.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  congruence.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.
Proof.
  intros pf qf Heq.
  assert (pf = qf) by (apply functional_extensionality; congruence); subst.
  reflexivity.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  intros.
  setoid_rewrite H.
  reflexivity.
Qed.
Proof.
  intros a b Hab m1 m2 Hm.
  split; unfold Basics.impl, exis; intros; deex; eexists.
  eapply Hab; eauto.
  eapply Hab; eauto.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  congruence.
Qed.
Proof.
  unfold lift_empty.
  intros a b Hab m1 m2 Hm H; subst.
  intuition.
Qed.
Proof.
  unfold lift_empty.
  intros a b Hab m1 m2 Hm H; subst.
  intuition.
Qed.
Proof.
  unfold lift_empty.
  intros a b Hab m1 m2 Hm; subst.
  intuition.
Qed.
Proof.
  unfold pointwise_relation.
  intros a b Hab.
  apply functional_extensionality; auto.
Qed.
Proof.
  unfold pred_apply.
  intros ma mb Hmab p q Hpq H.
  subst.
  auto.
Qed.
Proof.
  unfold pred_apply.
  intros ma mb Hmab p q Hpq H.
  subst.
  auto.
Qed.
Proof.
  unfold pred_apply.
  intros ma mb Hmab p q Hpq.
  subst. destruct Hpq.
  intuition.
Qed.
Proof.
  intros.
  rewrite sep_star_comm1 in H.
  auto.
Qed.
Proof.
  intros.
  destruct H.
  apply sep_star_comm in H. apply ptsto_valid in H.
  unfold pimpl, diskIs, ptsto; unfold_sep_star; intros; subst.
  exists (fun a' => if AEQ a' a then None else m0 a').
  exists (fun a' => if AEQ a' a then Some v else None).
  intuition.
  - unfold mem_union; apply functional_extensionality; intros.
    destruct (AEQ x0 a); subst; auto.
    destruct (m0 x0); auto.
  - unfold mem_disjoint; unfold not; intros. repeat deex.
    destruct (AEQ a0 a); discriminate.
  - destruct (AEQ a a); congruence.
  - destruct (AEQ a' a); subst; congruence.
Qed.
Proof.
  intros.
  unfold pimpl, diskIs; intros; subst.
  apply sep_star_comm.
  apply mem_except_ptsto; eauto.
Qed.
Proof.
  unfold pimpl, diskIs, ptsto, upd; unfold_sep_star; intros; subst; repeat deex.
  apply functional_extensionality; intros.
  case_eq (AEQ x a); intros; subst.
  - rewrite mem_union_comm; auto.
    erewrite mem_union_addr; eauto.
    apply mem_disjoint_comm; auto.
  - unfold mem_union, mem_except.
    destruct (AEQ x a); try discriminate.
    case_eq (m x); auto; intros.
    rewrite H4; auto.
Qed.
Proof.
  intros.
  destruct H.
  apply sep_star_comm in H. apply ptsto_valid in H.
  unfold pimpl, diskIs, ptsto, upd; unfold_sep_star; intros; subst; repeat deex.
  apply functional_extensionality; intros.
  unfold mem_union, mem_except.
  destruct (AEQ x0 a); subst; try congruence.
  destruct (m x0); auto.
  rewrite H5; auto; discriminate.
Qed.
Proof.
  unfold diskIs, pimpl; intros; subst; eauto.
Qed.
Proof.
  intros F F' HF a a' Ha v v' Hv.
  subst.
  firstorder.
Qed.
Proof.
  intros F F' HF a a' Ha v v' Hv.
  subst.
  firstorder.
Qed.
Proof.
  unfold pred_except; intros.
  erewrite insert_mem_except by eauto.
  rewrite upd_nop; eauto.
  intuition.
  apply mem_except_is_none.
Qed.
Proof.
  intros; rewrite sep_star_comm.
  unfold pimpl; intros.
  assert (m a = Some v).
  specialize (H m H0).
  eapply ptsto_valid.
  eapply sep_star_comm.
  eauto.
  eapply mem_except_ptsto; auto.
  apply pred_except_mem_except; eauto.
Qed.
Proof.
  unfold piff, pimpl, pred_except.
  unfold_sep_star.
  split; intros; intuition; repeat deex.
  - exists (mem_except m1 a).
    exists m2.
    intuition.

    + apply functional_extensionality; intros.
      apply equal_f with (x0 := x) in H2.
      destruct (AEQ a x); subst.
      * rewrite H1. unfold mem_union, mem_except. destruct (AEQ x x); try congruence.
        unfold ptsto in H5. intuition. rewrite H6; auto.
      * unfold insert in H2.
        unfold mem_union, mem_except in *.
        destruct (AEQ x a); try congruence.

    + apply mem_disjoint_comm.
      apply mem_disjoint_mem_except.
      apply mem_disjoint_comm.
      assumption.

    + apply mem_except_is_none.

    + assert (m1 a = Some v).
      unfold insert, mem_union in *.
      apply equal_f with (x := a) in H2.
      destruct (AEQ a a); try congruence.
      rewrite H1 in *.
      rewrite H2.
      case_eq (m1 a); intros; auto.
      unfold ptsto in H5; intuition.
      rewrite H7; auto.

      erewrite insert_mem_except by eauto.
      rewrite upd_nop; eauto.

  - unfold mem_union.
    rewrite H3.
    firstorder.

  - exists (insert m1 a v).
    exists m2.
    intuition.

    + unfold insert, mem_union; apply functional_extensionality; intros.
      rewrite H3.
      destruct (AEQ x a); subst; auto.
      unfold ptsto in *; intuition.
      rewrite H2; eauto.

    + unfold mem_disjoint, insert, not in *; intros; repeat deex.
      rewrite H3 in *.
      destruct (AEQ a0 a); subst; try solve [ firstorder ].
      unfold ptsto in H4. intuition.
      rewrite H7 in H6; eauto.
      congruence.
Qed.
Proof.
  unfold pimpl, pred_except.
  unfold_sep_star; intros; intuition; repeat deex.
  assert (m = m1); try congruence.
  apply functional_extensionality; intros.
  destruct (AEQ x a); subst.
  - rewrite H0.
    case_eq (m1 a); intros; try auto.
    exfalso.
    apply H.
    exists a. do 2 eexists. intuition eauto.
    unfold ptsto in H4; intuition eauto.
  - apply equal_f with (x0 := x) in H1.
    rewrite insert_ne in H1 by auto.
    rewrite H1.
    unfold mem_union.
    destruct (m1 x); auto.
    unfold ptsto in H4; intuition.
Qed.
Proof.
  unfold pimpl, pred_except.
  unfold_sep_star; intros; intuition; repeat deex.
  - apply H; auto.
  - exists m.
    exists (Mem.insert empty_mem a v).
    assert (mem_disjoint m (insert empty_mem a v)).
    {
      apply mem_disjoint_comm.
      apply mem_disjoint_insert_l.
      eapply mem_disjoint_empty_mem.
      apply H; auto.
    }
    intuition eauto.
    rewrite mem_union_comm by eauto.
    rewrite <- mem_union_insert_comm; try reflexivity.
    apply H; auto.
    apply star_emp_pimpl.
    apply ptsto_insert_disjoint.
    apply emp_empty_mem.
    reflexivity.
Qed.
Proof.
  unfold_sep_star; unfold pred_except; intros.
  repeat deex.
  exists (insert m1 a' v'), m2; intuition.
  apply mem_union_insert_comm; auto.
  eapply mem_union_none_sel; eauto.
  eapply mem_disjoint_insert_l; eauto.
  eapply mem_union_none_sel; eauto.
Qed.
Proof.
  unfold_sep_star.
  unfold pimpl, diskIs, pred_except; intros.
  repeat deex.
  assert (m0 = m1); try congruence.
  apply functional_extensionality; intros.
  destruct (AEQ x off); subst.
  - rewrite H1.
    case_eq (m1 off); intros; auto.
    exfalso.
    apply H.
    exists off. do 2 eexists.
    intuition eauto.
    unfold ptsto in H4; intuition eauto.
  - eapply equal_f with (x0 := x) in H0.
    rewrite insert_ne in H0 by auto.
    rewrite H0.
    unfold mem_union.
    destruct (m1 x); auto.
    unfold ptsto in H4; intuition.
Qed.
Proof.
  intros.
  case_eq (m a); intros.
  - right.
    exists v0.
    apply ptsto_mem_except in H.
    rewrite mem_except_upd in H.
    eapply mem_except_ptsto; eauto.
  - left.
    apply ptsto_mem_except in H.
    rewrite mem_except_upd in H.
    rewrite mem_except_none in H; auto.
Qed.
Proof.
  intros.
  apply ptsto_mem_except in H0.
  rewrite mem_except_insert in H0.
  rewrite mem_except_none in H0; auto.
Qed.
Proof.
  unfold_sep_star; unfold pimpl, pred_except; intros.
  repeat deex.
  exists (mem_except m1 a').
  exists m2.
  intuition.
  apply functional_extensionality; intros.
  - apply equal_f with (x0 := x) in H2.
    destruct (AEQ x a'); subst.
    rewrite H0 in *.
    rewrite mem_union_sel_none; auto.
    apply mem_except_is_none.
    unfold ptsto in H5.
    destruct H5.
    apply H5; eauto.
    unfold mem_union in *.
    rewrite mem_except_ne by auto.
    rewrite <- H2.
    rewrite insert_ne; auto.
  - apply mem_disjoint_comm.
    apply mem_disjoint_mem_except; eauto.
    apply mem_disjoint_comm; auto.
  - apply mem_except_is_none.
  - assert (m1 = insert (mem_except m1 a') a' v').
    apply functional_extensionality; intros.
    apply equal_f with (x0 := x) in H2.
    destruct (AEQ x a'); subst.
    rewrite insert_eq in *; auto.
    rewrite H2.
    rewrite mem_union_sel_l; auto.
    eapply ptsto_ne; eauto.
    apply mem_except_is_none.
    rewrite insert_ne; auto.
    rewrite mem_except_ne; auto.
    rewrite <- H4; auto.
Qed.
Proof.
  intros.
  exists (F*y)%pred.
  apply sep_star_assoc.
  setoid_rewrite sep_star_comm.
  apply sep_star_assoc.
  eauto.
Qed.
Proof.
  intros.
  erewrite sep_star_assoc_1.
  setoid_rewrite sep_star_comm at 2.
  erewrite sep_star_assoc_2.
  erewrite H0; eauto.
Qed.
Proof.
  intros.
  erewrite sep_star_assoc_1.
  setoid_rewrite sep_star_comm at 2.
  erewrite sep_star_assoc_2.
  erewrite H0; eauto.
Qed.
Proof.
  unfold_sep_star.
  unfold notindomain, pimpl.
  intros; repeat deex.
  unfold mem_union.
  rewrite H by assumption.
  rewrite H0 by assumption.
  auto.
Qed.
Proof.
  unfold pimpl, ptsto, notindomain; intuition.
Qed.
Proof.
  unfold_sep_star. intros. repeat deex.
  unfold mem_union.
  case_eq (m1 a); eauto; intros.
  contradict H2.
  rewrite H; eauto; congruence.
Qed.
Proof.
  unfold ptsto; intuition.
Qed.