Proof.
  unfold sync_invariant; eauto.
Qed.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec' H10.
    eapply H4; eauto.
    pred_apply; cancel.
    eauto.
    eapply ptsto_subset_valid' in H; deex.
    unfold possible_sync in *.
    destruct (H15 a).
    intuition congruence.
    repeat deex; simpl in *.
    congruence.
  - exfalso.
    apply sep_star_comm in H. eapply ptsto_subset_valid in H. repeat deex.
    congruence.
  - right. repeat eexists; intuition eauto.
    eapply H3.
    pred_apply; cancel.
Qed.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec' H10.
    eapply H4; eauto.
    repeat apply sep_star_lift_apply'; eauto.

    pose proof (ptsto_subset_valid' H); deex; eauto; simpl in *.
    rewrite H1 in H16; inversion H16; subst; clear H16.

    eapply pimpl_apply.
    cancel.

    eapply sync_invariant_possible_sync; eauto.
    eapply ptsto_subset_upd; eauto.
    unfold vsmerge; simpl.
    eapply incl_cons.
    constructor; auto.
    eapply incl_tl; eauto.
  - exfalso.
    apply sep_star_comm in H. eapply ptsto_subset_valid in H. repeat deex.
    congruence.
  - right. repeat eexists; intuition eauto.
    eapply H3.
    pred_apply; cancel.
Qed.
Proof.
  unfold possible_sync, sync_mem; intros.
  extensionality a.
  specialize (H a).
  destruct (m a) as [ [? ?] | ];
    intuition; repeat deex; try congruence.
  inversion H0; subst.
  apply incl_in_nil in H2; subst; eauto.
Qed.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec' H10.
    eapply H4; eauto.

    eapply pimpl_apply.
    cancel.

    apply possible_sync_from_sync in H15; subst.
    eapply pimpl_apply; [ | eapply sync_xform_pred_apply; pred_apply; reflexivity ].
    cancel.
  - right. repeat eexists; intuition eauto.
    eapply H3.
    pred_apply; cancel.
Qed.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - eapply H4; eauto.
    apply sep_star_comm in H as H'. apply ptsto_subset_valid in H'; repeat deex.
    apply sep_star_comm in H as H'. rewrite ptsto_subset_pimpl_ptsto_ex in H'. destruct_lift H'.
    apply ptsto_valid in H0.
    rewrite H0 in H1; inversion H1; subst.
    inv_exec' H10.
    destruct vs'.

    repeat apply sep_star_lift_apply'; eauto.
    eapply sync_invariant_possible_sync; eauto.

    eapply pimpl_apply.
    2: eapply ptsto_subset_upd.
    cancel.
    eauto.
    eapply incl_refl.
  - exfalso.
    apply sep_star_comm in H. eapply ptsto_subset_valid in H. repeat deex.
    congruence.
Qed.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec' H10.
    eapply H4; eauto.
    pred_apply; cancel.
    eauto.
Qed.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec' H10.
    eapply H4; eauto.
    pred_apply; cancel.
    eauto.
Qed.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec' H10.
    eapply H4; eauto.
    pred_apply; cancel.
Qed.
Proof.
  unfold corr2, corr2, exis; intros; repeat deex.
  repeat ( apply sep_star_lift2and in H; destruct H ).
  destruct b.
  - eapply H2; eauto.
    eapply pimpl_apply; [|apply H].
    cancel.
  - eapply H1; eauto.
    eapply pimpl_apply; [|apply H].
    cancel.
Qed.
Proof.
  destruct a; left + right; congruence.
Defined.
Proof.
  intros.
  apply well_founded_lt_compat with (f:=fun a => wordToNat (a.(For_args_n))).
  intros.
  apply wlt_lt; auto.
Qed.
Proof.
  intros.
  apply weq_minus1_wlt; auto.
Qed.
Proof.
  refine (Fix (@for_args_wf L) (fun _ => prog L)
          (fun args For_ => _)
          {| For_args_i := i; For_args_n := n; For_args_l := l |}).
  clear i n l.
  destruct args.
  refine (if weq For_args_n0 $0 then Ret For_args_l0 else _).
  refine (l' <- (f For_args_i0 For_args_l0); _).
  refine (For_ {| For_args_i := For_args_i0 ^+ $1;
                  For_args_n := For_args_n0 ^- $1;
                  For_args_l := l' |} _).

  simpl.
  apply word_minus_1; auto.
Defined.
Proof.
  intros.
  unfold For_.
  rewrite Fix_eq.
  simpl.

  destruct (weq n $0); f_equal.

  intros.

  match goal with
  | [ |- context[match ?x with _ => _ end] ] =>
     destruct x; f_equal
  end.

  match goal with
  | [ |- context[match ?x with _ => _ end] ] =>
     destruct x; try reflexivity
  end.

  apply f_equal.
  apply functional_extensionality; auto.
Qed.
Proof.
  intro T.
  wlt_ind.

  intros.
  apply corr2_exists; intros.
  apply corr2_exists; intros.
  apply corr2_exists; intros.
  case_eq (weq x $0); intros; subst.

  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + unfold pimpl, lift; intros.
      rewrite For_step.
      eapply pimpl_ok2.
      simpl; monad_simpl; eauto.
      intros.
      apply pimpl_refl.
    + fold (wzero addrlen). ring_simplify (wzero addrlen ^+ i). cancel.

  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + assert (wordToNat x <> 0).
      unfold not in *; intros; apply n.
      rewrite <- H6; rewrite natToWord_wordToNat; auto.

      unfold pimpl, lift; intros.
      rewrite For_step.
      rewrite H0.
      monad_simpl.
      apply H4.

      apply eq_le; auto.
      rewrite wplus_comm.
      apply lt_wlt.
      omega.

      intros.
      eapply pimpl_ok2.
      apply H.

      apply word_minus_1; auto.

      intros.
      apply pimpl_exists_r; exists a.
      apply pimpl_exists_r; exists a0.
      apply pimpl_exists_r; exists a1.
      ring_simplify (i ^+ $1 ^+ (x ^- $1)).
      ring_simplify (x ^- $1 ^+ (i ^+ $1)).
      cancel.

      subst; apply H4; eauto.
      intros; apply H9; clear H9.
      apply wlt_lt in H12.
      unfold wlt.
      repeat rewrite wordToN_nat.
      apply Nlt_in.
      repeat rewrite Nat2N.id.
      rewrite wplus_alt.
      unfold wplusN, wordBinN.
      simpl (wordToNat $1).
      rewrite wordToNat_natToWord_idempotent'.
      omega.
      eapply Nat.le_lt_trans; [| apply (wordToNat_bound (i ^+ x)) ]; omega.

      rewrite wminus_Alt.
      rewrite wminus_Alt2.
      repeat rewrite wplus_alt.
      repeat unfold wplusN, wordBinN.

      simpl (wordToNat $1).
      repeat rewrite wordToNat_natToWord_idempotent'.
      omega.
      rewrite H2; apply wordToNat_bound.

      eapply Nat.le_lt_trans; [| apply (wordToNat_bound x) ]; omega.
      eapply Nat.le_lt_trans; [| apply (wordToNat_bound (i ^+ x)) ]; omega.

      unfold not; intros; apply H6.
      assert (wordToNat x < 1); [| omega ].
      apply wlt_lt in H9; simpl in H9; auto.
    + cancel.
Qed.
Proof.
  intros.
  eapply pimpl_ok2.
  apply for_ok'.
  fold (wzero addrlen); ring_simplify (wzero addrlen ^+ n).
  simpl (wordToNat (wzero addrlen)); replace (0 + wordToNat n) with (wordToNat n) by omega.
  ring_simplify (n ^+ wzero addrlen).
  cancel.
  cancel.
Qed.
Proof.
  induction n; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros.
  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.
      eapply pimpl_ok2; monad_simpl; eauto.
      intros.
      apply pimpl_refl.
    + cancel.
  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.

      eapply pimpl_ok2; monad_simpl.
      apply H1. omega. omega.
      intros.
      eapply pimpl_ok2.
      eapply IHn.
      cancel.
      cancel.

      2: intros; apply pimpl_refl.

      eapply pimpl_ok2.
      eauto.
      intros.
      cancel.

      replace (n + S i) with (S (n + i)) by omega.
      eauto.
    + cancel.
Qed.
Proof.
  intros.
  eapply pimpl_ok2.
  apply forN_ok'.
  cancel.
  cancel.
  eapply pimpl_ok2.
  eauto.
  replace (n + 0) with n by omega; auto.
Qed.
Proof.
  intros ITEM.
  induction lst; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros;
    apply corr2_exists; intros.

  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.
      eapply pimpl_ok2; monad_simpl; eauto.
      intros.
      apply pimpl_refl.
    + cancel.
  - eapply pimpl_pre2; intros; repeat ( apply sep_star_lift_l; intros ).
    + simpl.
      unfold pimpl, lift; intros.
      eapply pimpl_ok2; monad_simpl.
      apply H1.
      intros.
      eapply pimpl_ok2.
      apply IHlst.
      cancel.
      eassign lst.
      cancel.
      eapply pimpl_ok2.
      apply H1.
      intros.
      eapply pimpl_ok2.
      apply H2.
      cancel.
      cancel.
      exists (a :: prefix); auto.

      intros.
      apply pimpl_refl.
    + cancel.
      exists nil; auto.
Qed.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec' H11.
    eapply H4; eauto.
    pred_apply; cancel.
    eauto.
    eapply ptsto_valid' in H6.
    rewrite H6 in *.
    inversion H17.
    apply inj_pair2 in H1; eauto.
  - exfalso.
    eapply ptsto_valid' in H6.
    congruence.
  - exfalso.
    eapply ptsto_valid' in H6.
    congruence.
Qed.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec' H11.
    eapply H4; eauto.
    pred_apply; cancel.
    eauto.
    eapply ptsto_upd'.
    eauto.
  - exfalso.
    eapply ptsto_valid' in H6.
    congruence.
Qed.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  inv_exec' H11.
  eapply H4; eauto.
  pred_apply; cancel.
  eauto.
  eapply ptsto_insert_disjoint; eauto.
Qed.
Proof.
  unfold corr2; intros.
  destruct_lift H.
  inv_exec.
  - inv_exec' H11.
    eapply H4; eauto.
    pred_apply; cancel.
    eauto.
    eapply ptsto_delete'.
    pred_apply; cancel.
  - exfalso.
    eapply ptsto_valid' in H6.
    congruence.
Qed.