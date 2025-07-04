Proof.
  unfold wordToZ.
  intros.
  rewrite wordToN_nat.
  unfold Z.of_N, N.of_nat, Z.of_nat.
  destruct # (w); auto.
Qed.
Proof.
  intros.
  rewrite wordToZ_nat.
  unfold Z.of_nat.
  case_eq (# w); simpl; intros.
  - rewrite <- natToWord_wordToNat.
    congruence.
  - rewrite posToWord_nat.
    rewrite SuccNat2Pos.id_succ.
    rewrite <- natToWord_wordToNat.
    congruence.
Qed.
Proof.
  intros.
  rewrite pow2_N.
  rewrite nat_N_Z.
  induction p; auto.
  rewrite Nat2Z.inj_succ.
  rewrite Z.pow_succ_r.
  rewrite IHp.
  rewrite Z.mul_comm.
  rewrite <- Zplus_diag_eq_mult_2.
  simpl.
  rewrite Nat2Z.inj_add.
  rewrite <- plus_n_O.
  reflexivity.
  replace (0%Z) with (Z.of_nat 0) by reflexivity.
  apply inj_le.
  omega.
Qed.
Proof.
  intros.
  rewrite wordToZ_nat.
  destruct z; simpl.
  - rewrite roundTrip_0. reflexivity.
  - rewrite posToWord_nat.
    rewrite wordToNat_natToWord_idempotent.
    rewrite positive_nat_Z; reflexivity.
    rewrite positive_nat_N.
    inversion H.
    apply N2Z.inj_lt.
    rewrite positive_N_Z.
    rewrite Z_pow_Npow2 in H1.
    auto.
  - inversion H.
    compute in *.
    congruence.
Qed.
Proof.
  unfold wordToZ; split.
  - apply N2Z.is_nonneg.
  - rewrite wordToN_nat.
    rewrite Z_pow_Npow2.
    rewrite <- (Nnat.N2Nat.id (Npow2 sz)).
    rewrite Npow2_nat.
    repeat rewrite nat_N_Z.
    apply Nat2Z.inj_lt.
    apply wordToNat_bound.
Qed.
Proof.
  intros.
  pose proof (ZToWordTrunc_wordToZ w).
  destruct (wordToZ_bound w).
  remember (wordToZ w).
  destruct z.
  - simpl in *; congruence.
  - unfold ZToWord.
    replace (Z.compare (Z.pos p) (2 ^ Z.of_nat sz)%Z) with (Lt).
    unfold ZToWordTrunc in H; congruence.
  - pose proof (Pos2Z.neg_is_neg p).
    apply Zle_not_lt in H0.
    congruence.
Qed.
Proof.
  unfold ZToWord; intros.
  destruct z.
  - inversion H. unfold wordToZ.
    rewrite wordToN_nat. rewrite roundTrip_0. reflexivity.
  - destruct (Z.compare (Z.pos p) (2 ^ Z.of_nat sz))%Z eqn:Heq; try congruence.
    assert (Z.pos p < 2 ^ Z.of_nat sz)%Z by (apply Z.compare_lt_iff; auto).
    inversion H.
    replace (posToWord sz p) with (ZToWordTrunc sz (Z.pos p)) by reflexivity.
    rewrite wordToZ_ZToWordTrunc_idempotent; auto.
    split; auto.
    apply Zle_0_pos.
  - congruence.
Qed.