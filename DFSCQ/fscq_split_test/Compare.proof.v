Proof.
  unfold compare.
  hoare.
Qed.
Proof.
  unfold compare_hash.
  hoare.

  rewrite <- H8 in H11.
  eapply hash_safe_eq; eauto.

  Grab Existential Variables.
  all: eauto.
Qed.