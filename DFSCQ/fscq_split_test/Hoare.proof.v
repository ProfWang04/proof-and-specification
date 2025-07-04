Proof.
  unfold corr2; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.
Proof.
  unfold corr3; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.
Proof.
  unfold corr2, pimpl; intros.
  edestruct H1; eauto.
  eapply sep_star_lift_l in H4; [|instantiate (1:=([x=y])%pred)].
  unfold lift in *; subst; eauto.
  firstorder.
Qed.
Proof.
  unfold corr3, pimpl; intros.
  edestruct H1; eauto.
  eapply sep_star_lift_l in H4; [|instantiate (1:=([x=y])%pred)].
  unfold lift in *; subst; eauto.
  firstorder.
Qed.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.
Proof.
  unfold corr3; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.
Proof.
  unfold corr2; intros; exfalso.
  eapply H; eauto.
Qed.
Proof.
  unfold corr3; intros; exfalso.
  eapply H; eauto.
Qed.
Proof.
  unfold corr2; intros.
  destruct H0.
  eapply H; eauto.
Qed.
Proof.
  unfold corr3; intros.
  destruct H0.
  eapply H; eauto.
Qed.
Proof.
  unfold corr2; intros.
  eapply H; eauto.
  exists a; eauto.
Qed.
Proof.
  unfold corr3; intros.
  eapply H; eauto.
  exists a; eauto.
Qed.
Proof.
  intros a b Hab x y Hxy; subst.
  split; intros; eapply pimpl_ok2; try eassumption; apply Hab.
Qed.
Proof.
  intros a b Hab x y Hxy p q Hpq; subst.
  split; intros; eapply pimpl_ok3; try eassumption; apply Hab.
Qed.