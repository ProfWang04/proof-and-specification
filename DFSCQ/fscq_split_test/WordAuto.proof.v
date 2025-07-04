Proof.
  intros. unfold not. intro He. rewrite He in H. auto.
Qed.
Proof.
  intros. rewrite NToWord_nat. apply wordToNat_natToWord_idempotent.
  rewrite N2Nat.id. assumption.
Qed.
Proof.
  intros. rewrite N2Nat_word. trivial. unfold goodSize in H. rewrite <- Npow2_nat in H. nomega.
Qed.
Proof.
  intros. rewrite wordToN_nat. autorewrite with N. trivial.
Qed.
Proof.
  intros.
  destruct (wordToNat_natToWord sz x) as [? [Heq ?]]; rewrite Heq.
  replace (x - x0 * pow2 sz + y) with (x + y - x0 * pow2 sz) by omega.
  apply drop_sub; omega.
Qed.
Proof.
  intros.
  rewrite plus_comm.
  rewrite plus_ovf_l.
  rewrite plus_comm.
  auto.
Qed.
Proof.
  intros.
  repeat rewrite NToWord_nat.
  repeat rewrite wordToN_nat.
  rewrite <- (N2Nat.id y) at 1.
  rewrite <- Nat2N.inj_add.
  rewrite Nat2N.id.
  rewrite N2Nat.inj_add.
  apply plus_ovf_l.
Qed.
Proof.
  intros.
  rewrite N.add_comm.
  rewrite plus_ovf_lN.
  rewrite N.add_comm.
  auto.
Qed.
Proof.
  intros.
  destruct (wordToNat_natToWord sz x) as [? [Heq ?]]; rewrite Heq.
  rewrite Nat.mul_sub_distr_r.
  replace (x0 * pow2 sz * y) with (x0 * y * pow2 sz) by ring.
  apply drop_sub.
  replace (x0 * y * pow2 sz) with (x0 * pow2 sz * y) by ring.
  apply mult_le_compat_r; auto.
Qed.
Proof.
  intros.
  rewrite mult_comm.
  rewrite mul_ovf_l.
  rewrite mult_comm.
  auto.
Qed.
Proof.
  intros.
  repeat rewrite NToWord_nat.
  repeat rewrite wordToN_nat.
  rewrite <- (N2Nat.id y) at 1.
  rewrite <- Nat2N.inj_mul.
  rewrite Nat2N.id.
  rewrite N2Nat.inj_mul.
  apply mul_ovf_l.
Qed.
Proof.
  intros.
  rewrite N.mul_comm.
  rewrite mul_ovf_lN.
  rewrite N.mul_comm.
  auto.
Qed.
Proof.
  intuition. apply wordToNat_inj in H0; tauto.
Qed.
Proof.
  intros.
  (* Remember the specs of divmod and pow_div_eucl... *)
  generalize (N.pos_div_eucl_spec a (N.pos Sb)); intro HN.
  generalize (N.pos_div_eucl_remainder a (N.pos Sb)); intro HNR.
  remember (N.pos_div_eucl a (N.pos Sb)) as DN; destruct DN.
  generalize (Nat.divmod_spec (Pos.to_nat a) b 0 b); intro HNat.
  remember (Nat.divmod (Pos.to_nat a) b 0 b) as DNat; destruct DNat.
  simpl.
  destruct HNat; auto.
  (* ... and show that they are equivalent *)
  apply (f_equal nat_of_N) in HN.
  rewrite nat_of_Nplus in HN.
  rewrite nat_of_Nmult in HN.
  repeat rewrite positive_N_nat in HN.
  rewrite H in HN.
  rewrite Nat.mul_0_r in H0.
  rewrite Nat.sub_diag in H0.
  repeat rewrite Nat.add_0_r in H0.
  rewrite Nat.mul_comm in H0.
  clear HeqDN. clear HeqDNat.
  rewrite H0 in HN.
  clear H0.
  assert (N.pos Sb <> 0%N).
  apply Nneq_in. simpl.
  generalize (Pos2Nat.is_pos Sb).
  omega.
  apply Nlt_out in HNR; [|auto].
  rewrite positive_N_nat in HNR.
  simpl in HNR.
  assert (N.to_nat n = n1).
  destruct (lt_eq_lt_dec (N.to_nat n) n1); [destruct s; auto|]; [
    remember (n1 - N.to_nat n) as d;
    assert (n1 = d + N.to_nat n) as He by omega |
    remember (N.to_nat n - n1) as d;
    assert (N.to_nat n = d + n1) as He by omega
  ]; assert (d > 0) by omega;
     rewrite He in HN;
     rewrite Nat.mul_add_distr_r in HN;
     destruct (mult_O_le (S b) d); omega.
  intuition.
Qed.
Proof.
  destruct a.
  destruct a'; [|rewrite Nat.div_0_l]; auto.
  replace 0 with (N.to_nat 0) by auto.
  apply Nneq_out; discriminate.
  unfold N.div, Nat.div.
  intro a'.
  case_eq (N.to_nat a').
  + intro He.
    destruct a'.
    reflexivity.
    inversion He.
    generalize (Pos2Nat.is_pos p0).
    omega.
  + intros.
    simpl.
    destruct a'; try discriminate.
    rewrite positive_N_nat in H.
    apply divmod_Ndiv_eucl; auto.
Qed.
Proof.
  destruct a.
  destruct a'; [|rewrite Nat.mod_0_l]; auto.
  replace 0 with (N.to_nat 0) by auto.
  apply Nneq_out. discriminate.
  unfold Nmod, Nat.modulo.
  intros.
  case_eq (N.to_nat a').
  omega.
  simpl.
  destruct a'; try discriminate.
  intro n.
  apply divmod_Ndiv_eucl; auto.
Qed.
Proof.
  intros.
  replace (NToWord sz (wordToN n * wordToN m)) with (n ^* m) by auto.
  replace n with (natToWord sz (wordToNat n)) at 1 by (apply natToWord_wordToNat).
  replace m with (natToWord sz (wordToNat m)) at 1 by (apply natToWord_wordToNat).
  rewrite <- natToWord_mult. auto.
Qed.
Proof.
  intros.
  destruct (Nat.eq_dec a 0).
  rewrite e. rewrite Nat.div_0_l by assumption. omega.
  destruct (Nat.eq_dec b 1).
  rewrite e. rewrite Nat.div_1_r. omega.
  apply Nat.lt_le_incl.
  apply Nat.div_lt; omega.
Qed.
Proof.
  intros.
  rewrite N2Nat_word.
  rewrite Ninj_div.
  repeat rewrite wordToNat_N. trivial.
  apply Nlt_in.
  autorewrite with W2Nat.
  apply le_lt_trans with (m := wordToNat a).
  apply div_le; assumption.
  apply wordToNat_bound.
Qed.
Proof.
  intros.
  destruct (lt_dec y (pow2 sz)); [
    (* Either there's no overflow... *)
    rewrite wordToNat_natToWord_idempotent' in H |
    (* ... or it's true even without the hypothesis *)
    generalize (wordToNat_bound (natToWord sz y))];
  intuition; unfold goodSize in *; omega.
Qed.
Proof.
  word2nat_auto.
Qed.
Proof.
  word2nat_auto.
Qed.
Proof.
  word2nat_auto.
Qed.
Proof.
  word2nat_auto.
Qed.