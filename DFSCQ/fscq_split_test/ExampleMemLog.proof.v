Proof.
  unfold inc_two.
  hoare.
Qed.
Proof.
  unfold log_inc_two_body.
  hoare; apply LOG.activetxn_would_recover_old.
Qed.
Proof.
  unfold log_inc_two.
  hoare.
  rewrite LOG.notxn_would_recover_old.
  cancel.
  rewrite LOG.activetxn_would_recover_old.
  cancel.
Qed.
Proof.
  intros.
  unfold forall_helper at 1 2; intros v0 v1 F.

  eapply pimpl_ok3.
  eapply corr3_from_corr2_rx; eauto with prog.
  
  eapply (LOG.recover_corr2_to_corr3 (i2 xp s0 s1)).
  unfold i2.
  intros.
  eapply pimpl_ok2.
  eapply log_inc_two_ok.
  cancel.
Qed.