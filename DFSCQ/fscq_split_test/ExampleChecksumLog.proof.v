Proof.
  unfold put, rep, any_hash_rep, crep.
  step.
  step.
  step.
  apply goodSize_bound with (bound := 2); auto.
  step.
  step.
  step.
  step.
  step.

  solve_hash_list_rep.
  all: cancel_with solve_hash_list_rep.
  Grab Existential Variables.
  all: eauto.
Qed.
Proof.
  unfold get, rep, any_hash_rep.
  step.
  step.
  step.
  all: solve_hash_list_rep.
Qed.
Proof.
  unfold crep, after_crash_pred.
  intros.
  repeat (autorewrite with crash_xform; cancel).
Qed.
Proof.
  unfold recover, rep.
  intros.
  eapply pimpl_ok2; eauto with prog.
  intros. norm'l. unfold stars; simpl.

  (* autorewrite with crash_xform doesn't work? *)
  assert (Hafter_crash: (after_crash_pred d1_old d2_old hm)%pred d \/
    (after_crash_pred d1 d2 hm)%pred d).
    apply crash_xform_would_recover_either_pred.
    auto.

  unfold after_crash_pred in Hafter_crash.
  destruct Hafter_crash;
  destruct_lift H.

  - cancel.
    step.
    step.
    step.
    apply goodSize_bound with (bound := 2); auto.
    step.
    step.
    apply hash_to_valu_inj in H13.
    subst.
    assert (Hheq: d2_old :: d1_old :: nil = b :: a :: nil).
      eapply hash_list_injective.
      solve_hash_list_rep.
      auto.
    inversion Hheq.
    unfold any_hash_rep.
    apply pimpl_or_r. left.
    apply pimpl_exists_r. exists r_.
    cancel.

    step.
    unfold any_hash_rep.
    cancel_with eauto.
    solve_hash_list_rep.
    step.

    all: repeat cancel; try (
      unfold crep in *;
      apply pimpl_or_r; left;
      cancel;
      cancel_with solve_hash_list_rep).

  - cancel.
    step.
    step.
    step.
    apply goodSize_bound with (bound := 2); auto.
    step.
    step.
    apply hash_to_valu_inj in H13.
    subst.
    assert (Hheq: d2 :: d1 :: nil = b :: a :: nil).
      eapply hash_list_injective.
      solve_hash_list_rep.
      auto.
    inversion Hheq.
    unfold any_hash_rep.
    apply pimpl_or_r; right. apply pimpl_or_r; left.
    apply pimpl_exists_r. exists r_.
    cancel.

    step.
    unfold any_hash_rep.
    cancel_with eauto.
    solve_hash_list_rep.

    step.
    all: repeat cancel; try (
      unfold crep in *;
      apply pimpl_or_r; right;
      cancel;
      cancel_with solve_hash_list_rep).

  Grab Existential Variables.
  all: eauto.
Qed.