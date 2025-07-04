Theorem valulen_nonzero : valulen <> 0.
Proof.
  rewrite valulen_is. apply Nat.eqb_neq.
  compute. reflexivity.
Qed.

Theorem valulen_gt_0 : valulen > 0.
Proof.
  generalize valulen_nonzero.
  generalize valulen.
  destruct n; intuition.
Qed.

Theorem valulen_wordToNat_natToWord : # (natToWord addrlen valulen) = valulen.
Proof.
  rewrite valulen_is. apply Nat.eqb_eq.
  compute. reflexivity.
Qed.

(* tight bound for valulen *)
Theorem valulen_bound : valulen < pow2 16.
Proof.
  eapply Nat.lt_le_trans with (m := pow2 15 + 1).
  rewrite valulen_is. apply Nat.ltb_lt. compute; reflexivity.
  apply pow2_le_S.
Qed.
