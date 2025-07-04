  Proof.
    auto.
  Qed.
  Proof.
    auto.
  Qed.
Proof.
  rewrite valulen_is. apply Nat.eqb_neq.
  compute. reflexivity.
Qed.
Proof.
  generalize valulen_nonzero.
  generalize valulen.
  destruct n; intuition.
Qed.
Proof.
  rewrite valulen_is. apply Nat.eqb_eq.
  compute. reflexivity.
Qed.
Proof.
  eapply Nat.lt_le_trans with (m := pow2 15 + 1).
  rewrite valulen_is. apply Nat.ltb_lt. compute; reflexivity.
  apply pow2_le_S.
Qed.
Proof.
  intros.
  unfold hashmap_get.
  destruct (weq h default_hash);
  destruct (weq h h); intuition.
Qed.
Proof.
  intros.
  unfold upd_hashmap'.
  apply upd_hashmap_eq; auto.
Qed.
Proof.
  rewrite valulen_is; auto.
Qed.
Proof.
  unfold sync_addr; intros.
  destruct (AEQ a a'); try congruence.
Qed.
Proof.
  unfold sync_addr; intros; subst.
  destruct (AEQ a' a'); try congruence.
  destruct (m a'); try congruence.
  inversion H0; subst.
  destruct vs; auto.
Qed.