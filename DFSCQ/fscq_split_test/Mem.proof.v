  Proof.
    intros; subst; unfold upd.
    destruct (AEQ a a); tauto.
  Qed.
  Proof.
    intros; subst; unfold updSome.
    rewrite H.
    destruct (AEQ a a); tauto.
  Qed.
  Proof.
    intros; subst; unfold insert.
    rewrite H.
    destruct (AEQ a a); congruence.
  Qed.
  Proof.
    intros; subst; unfold upd.
    destruct (AEQ a' a); tauto.
  Qed.
  Proof.
    intros; subst; unfold updSome.
    destruct (AEQ a' a); tauto.
  Qed.
  Proof.
    intros; subst; unfold insert.
    destruct (AEQ a' a); congruence.
  Qed.
  Proof.
    intros; apply functional_extensionality; unfold upd; intros.
    destruct (AEQ a a); try congruence.
    destruct (AEQ x a); auto.
  Qed.
  Proof.
    intros; apply functional_extensionality; unfold updSome; intros.
    destruct (AEQ a a); try congruence.
    destruct (AEQ x a); auto.
    destruct (m a); auto.
  Qed.
  Proof.
    intros; apply functional_extensionality; unfold insert at 1; intros.
    destruct (AEQ a a); try congruence.
    destruct (AEQ x a); auto.
    subst. unfold insert; simpl.
    destruct (AEQ a a); try congruence.
    destruct (m a); auto.
  Qed.
  Proof.
    intros; apply functional_extensionality; intros.
    case_eq (AEQ a x); intros; subst.
    repeat erewrite upd_eq; eauto.
    repeat rewrite upd_ne; auto.
  Qed.
  Proof.
    intros; apply functional_extensionality; intros.
    case_eq (AEQ a x); intros; subst.
    repeat erewrite updSome_eq; eauto.
    repeat rewrite updSome_ne; auto.
  Qed.
  Proof.
    unfold updSome; intros; apply functional_extensionality; intros.
    rewrite H.
    destruct (AEQ x a); subst; auto.
  Qed.
  Proof.
    intros; apply functional_extensionality; unfold upd; intros.
    destruct (AEQ a1 a0); destruct (AEQ a0 a1); try congruence.
    case_eq (AEQ x a1); case_eq (AEQ x a0); intros; subst; try congruence.
  Qed.
  Proof.
    intros; apply functional_extensionality; unfold updSome; intros.
    destruct (AEQ a1 a0); destruct (AEQ a0 a1); try congruence.
    case_eq (AEQ x a1); case_eq (AEQ x a0); intros; subst; try congruence.
  Qed.
  Proof.
    intros; apply functional_extensionality; unfold updSome, insert; intros.
    destruct (AEQ a1 a0); destruct (AEQ a0 a1); try congruence.
    case_eq (AEQ x a1); case_eq (AEQ x a0); intros; subst; try congruence.
  Qed.
  Proof.
    intros; apply functional_extensionality; unfold updSome, delete; intros.
    destruct (AEQ a1 a0); destruct (AEQ a0 a1); try congruence.
    case_eq (AEQ x a1); case_eq (AEQ x a0); intros; subst; try congruence.
  Qed.
  Proof.
    intros; apply functional_extensionality; unfold insert; intros.
    destruct (AEQ a1 a0); destruct (AEQ a0 a1); try congruence.
    case_eq (AEQ x a1); case_eq (AEQ x a0); intros; subst; try congruence.
  Qed.
  Proof.
    intros; apply functional_extensionality; unfold insert, delete; intros.
    destruct (AEQ a1 a0); destruct (AEQ a0 a1); try congruence.
    case_eq (AEQ x a1); case_eq (AEQ x a0); intros; subst; try congruence.
  Qed.
  Proof.
    intros; apply functional_extensionality; unfold delete; intros.
    destruct (AEQ a1 a0); destruct (AEQ a0 a1); try congruence.
    case_eq (AEQ x a1); case_eq (AEQ x a0); intros; subst; try congruence.
  Qed.