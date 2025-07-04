Proof.
  unfold inc_two.
  hoare.
Qed.
Proof.
  unfold log_inc_two, LOG.log_intact.
  hoare.
Qed.
Proof.
  intros.
  unfold forall_helper; intros d v0 v1 F.
  exists (LOG.log_intact xp d \/
          exists d', LOG.log_intact xp d' *
          [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred d' ]])%pred.
  intros.

  eapply pimpl_ok3.
  eapply corr3_from_corr2.
  eauto with prog.
  eapply LOG.recover_ok.

  cancel.
  hoare_unfold LOG.unfold_intact.
  cancel.
  hoare_unfold LOG.unfold_intact.
  LOG.unfold_intact; cancel; cancel.
  hoare_unfold LOG.unfold_intact.
  LOG.unfold_intact; cancel; cancel.
Qed.