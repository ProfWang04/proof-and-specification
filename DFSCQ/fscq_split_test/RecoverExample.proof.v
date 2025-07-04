Proof.
  reflexivity.
Qed.
Proof.
  unfold forall_helper; intros.

  (* Idempotence theorem *)
  eapply pimpl_ok3.
  eapply corr3_from_corr2_rx; eauto with prog.

  (* Mechanical transformations *)
  intros.
  cancel.

  (* Post condition *)
  step.

  (**
   * Try to cancel out the idemcrash implication.
   * This breaks up the 3 ORs from [work]'s crash condition.
   * Note that [cancel] tries to unify the first OR branch with [idemcrash], which is wrong;
   * to avoid this, hide the fact that [idemcrash] is an evar using [set_evars].
   *)
  set_evars.
  assert (exists idemcrash', idemcrash' = H) as Hidem by eauto.
  destruct Hidem as [idemcrash' Hidem]. rewrite <- Hidem. subst H.
  rewrite <- locked_eq in Hidem.
  cancel.

  (**
   * Now we have a bunch of subgoals about idemcrash; re-combine the ORs back together..
   * Need to first unlock the idemcrash evar to make progress.
   *)
  rewrite locked_eq.
  apply pimpl_or_r. left. reflexivity.

  rewrite locked_eq.
  or_r. apply pimpl_or_r. left. reflexivity.

  rewrite locked_eq.
  or_r. or_r. reflexivity.

  (* Now we need to prove idempotence..  [xform_norm] breaks up the 3 ORs from idemcrash *)
  simpl.
  xform_norm.

  (* Prove each of the 3 idempotence subgoals *)
  all: rewrite H3.
  all: rewrite rep_xform.
  all: repeat ( cancel || step ).
Qed.