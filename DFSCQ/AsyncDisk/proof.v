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


 Lemma upd_hashmap_eq : forall hm h k,
  h <> default_hash ->
  hashmap_get (upd_hashmap hm h k) h = Some k.
Proof.
  intros.
  unfold hashmap_get.
  destruct (weq h default_hash);
  destruct (weq h h); intuition.
Qed.

Lemma upd_hashmap'_eq : forall hm h sz k,
  h <> default_hash ->
  hashmap_get (upd_hashmap' hm h k) h = Some (existT _ sz k).
Proof.
  intros.
  unfold upd_hashmap'.
  apply upd_hashmap_eq; auto.
Qed.
