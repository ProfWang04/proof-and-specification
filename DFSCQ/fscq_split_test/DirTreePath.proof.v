  Proof.
    induction base; simpl. eauto.
    destruct pn.
    right. intro H'; destruct H'. congruence.
    destruct (string_dec s a); subst.
    - destruct (IHbase pn); repeat deex.
      left; eauto.
      right. intro H'; apply H. deex. inversion H0; eauto.
    - right. intro H. deex. inversion H. eauto.
  Qed.
  Proof.
    intros.
    unfold pathname_prefix.
    eexists suffix.
    rewrite app_nil_l; eauto.
  Qed.
  Proof.
    intros.
    unfold pathname_prefix.
    eexists suffix.
    reflexivity.
  Qed.
  Proof.
    intros. unfold pathname_prefix.
    intro.
    eapply H.
    deex.
    rewrite cons_app with (l:= suffix) in H0.
    inversion H0. subst.
    eauto.
  Qed.
  Proof.
    intros.
    deex. exfalso.
    eapply H.
    unfold pathname_prefix.
    exists suffix0; eauto.
  Qed.
  Proof.
    unfold pathname_prefix; eauto.
    intros. 
    intro.
    eapply H.
    destruct H0.
    eexists x; eauto.
  Qed.
  Proof.
    intros.
    unfold pathname_prefix in H.
    intro; subst.
    eapply H.
    exists path; eauto.
  Qed.
  Proof.
    unfold pathname_prefix; split; intros; repeat deex.
    - eexists. rewrite <- app_assoc. eauto.
    - rewrite <- app_assoc in H. eexists.
      apply app_inv_head in H. eauto.
  Qed.