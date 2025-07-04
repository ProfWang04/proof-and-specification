Proof.
  intros ? ? H; apply (f_equal N_of_nat) in H;
    autorewrite with N in *; assumption.
Qed.
Proof.
  congruence.
Qed.
Proof.
  intuition.
Qed.
Proof.
  unfold N.lt; intros.
  rewrite nat_of_Ncompare in H.
  apply nat_compare_Lt_lt; assumption.
Qed.
Proof.
  unfold N.lt; intros.
  rewrite nat_of_Ncompare.
  apply (proj1 (nat_compare_lt _ _)); assumption.
Qed.
Proof.
  unfold N.ge; intros.
  rewrite nat_of_Ncompare in H.
  apply nat_compare_ge; assumption.
Qed.
Proof.
  unfold N.ge; intros.
  rewrite nat_of_Ncompare.
  apply nat_compare_ge; assumption.
Qed.