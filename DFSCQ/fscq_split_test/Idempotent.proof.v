Proof.
  inversion 1; eauto.
Qed.
Proof.
  eauto.
Qed.
Proof. eauto. Qed.

Hint Resolve finished_val_eq.

Proof.
  intros.
  generalize dependent vm'.
  generalize dependent hm'.
  generalize dependent m'.
  induction H; subst; intuition; repeat deex; try congruence;
    try match goal with
        | [ H: @eq (outcome _) _ _ |- _ ] =>
          inversion H; subst
        end;
    eauto.

  eauto 7 using hashmap_subset_some_list_trans.
  eauto 7 using hashmap_subset_some_list_trans.

Unshelve.
  all: eauto.
Qed.
Proof.
  intros.
  eapply exec_crashed_hashmap_subset'; eauto.

Unshelve.
  all: eauto.
Qed.
Proof.
  intros.
  generalize dependent m.
  induction H; intros; try congruence.
  - edestruct H5; eauto.
    apply H3. eapply crash_xform_apply; eauto.
    pred_apply; cancel.
    repeat (destruct H7; try congruence).
    repeat (destruct H7; try congruence).
  - rewrite H0. eapply IHexec_recover; eauto.
    + eapply exec_crashed_hashmap_subset with (hm':=hm') in H as H'.
      intros.
      eapply pimpl_trans; try apply H4.
      autorewrite with crash_xform; cancel.
      eauto.
    + solve_hashmap_subset'.
    + edestruct H5; eauto.
      apply H3. eapply crash_xform_apply; eauto.
      solve_hashmap_subset'.
      repeat (destruct H9; try congruence).
      repeat (destruct H9; try congruence).
Qed.
Proof.
  intros.
  induction H; try congruence.
  edestruct H5; eauto.
  - apply H3. eapply crash_xform_apply; eauto.
    pred_apply; cancel.
  - destruct H8. destruct H8. destruct H8. destruct H8.
    inversion H8. congruence.
  - repeat (destruct H8; try congruence).
Qed.
Proof.
  intros.
  generalize dependent m.
  induction H; intros; try congruence.
  - eapply corr3_from_corr2_finished; eauto.
    clear IHexec_recover H2.
    edestruct H5; eauto.
    + apply H3. eapply crash_xform_apply; eauto.
      pred_apply; cancel.
    + repeat (destruct H2; try congruence).
    + destruct H2. destruct H2. destruct H2.
      inversion H2. eauto.
    + solve_hashmap_subset'.
    + solve_hashmap_subset'.
    + congruence.
  - eapply IHexec_recover; eauto; clear IHexec_recover H2.
    + solve_hashmap_subset'.
    + solve_hashmap_subset'.
    + inversion H7. auto.
    + edestruct H5; eauto.
      * apply H3. eapply crash_xform_apply; eauto.
        solve_hashmap_subset'.
      * repeat (destruct H2; try congruence).
      * repeat (destruct H2; try congruence).
Qed.
Proof.
  unfold corr3; intros.
  destruct H1 as [crash H1].
  destruct_lift H1.
  inversion H2; subst.
  - exfalso.
    edestruct H; eauto; repeat deex; try congruence.
  - left.
    repeat eexists.
    edestruct H; eauto; repeat deex; try congruence.
  - exfalso.
    edestruct H; eauto; repeat deex; try congruence.
    inversion H8; clear H8; subst.
    eapply corr3_from_corr2_failed; eauto.
    solve_hashmap_subset'.
    solve_hashmap_subset'.
  - edestruct H; eauto; repeat deex; try congruence.
    inversion H8; clear H8; subst.
    clear H H1 H2 ppre.
    right. repeat eexists.
    eapply corr3_from_corr2_finished; eauto.
    solve_hashmap_subset'.
    solve_hashmap_subset'.
  - edestruct H; eauto; repeat deex; try congruence.
    inversion H8; clear H8; subst.
    clear H H1 H2 ppre.
    right. repeat eexists.
    eapply corr3_from_corr2_recovered; eauto.
    solve_hashmap_subset'.
    solve_hashmap_subset'.
Qed.
Proof.
  intros.
  apply corr3_from_corr2; eauto.
Qed.