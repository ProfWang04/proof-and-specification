Proof.
  unfold hash_safe.
  intuition; subst;
  rewrite H3 in H; inversion H.
  existT_wordsz_eq H4.
  intuition.
Qed.
Proof.
  unfold hashmap_get.
  destruct hm; destruct (weq default_hash default_hash);
  intuition.
Qed.
Proof.
  induction l; intros.
  constructor. inversion H. auto.
  inversion H.
  eapply HL_cons; eauto.

  unfold upd_hashmap', hashmap_get.
  destruct (weq hl default_hash) eqn:Hhl.
  - rewrite e in H7.
    rewrite hashmap_get_default in H7.
    auto.
  - destruct (weq h hl) eqn:Hhl'; auto.
    subst.
    unfold hash_safe in H0.
    inversion H0 as [ Hget | Hget ];
      rewrite Hget in H7;
      inversion H7; auto.
Qed.
Proof.
  induction hkl; intros.
  inversion H. congruence.

  inversion H. subst.
  apply hash_list_rep_upd; auto.
  eapply IHhkl; eauto.
Qed.
Proof.
  unfold upd_hashmap'. cbn; intuition.
  repeat destruct weq; try congruence.
  rewrite e in *.
  unfold hash_safe in *.
  rewrite hashmap_get_default in *.
  intuition congruence.
Qed.
Proof.
  induction l1;
    intros;
    inversion H; inversion H0;
    unfold hash2 in *; intuition;
    subst; auto.

  contradict_hashmap_get_default H6 hm.

  rewrite H8 in H7.
  contradict_hashmap_get_default H7 hm.

  rewrite H7 in H10.
  inversion H10.
  existT_wordsz_eq H2.
  intuition.
  apply IHl1 in H8; congruence.
Qed.
Proof.
  induction l; intros.
  inversion H; inversion H0; subst. auto.

  inversion H; inversion H0; subst.
  assert (Heq: hl = hl0).
    eapply IHl; eauto.
  subst. auto.
Qed.
Proof.
  unfold hash_safe, upd_hashmap'; intros. subst.
  destruct (weq h2 default_hash) eqn:Hdef.

  destruct hm;
    (unfold hashmap_get in *; rewrite Hdef in *;
    destruct H as [ H' | H' ]; inversion H';
    destruct H0 as [ H0' | H0' ]; inversion H0';
    rewrite H2 in H3; pose proof (eq_sigT_snd H3); autorewrite with core in *; auto).

  subst.
  rewrite upd_hashmap_eq in H0; auto.
  destruct H0 as [ H0' | H0' ]; inversion H0'.
  pose proof (eq_sigT_snd H1). autorewrite with core in *. auto.
Qed.
Proof.
  induction hm2; intros.
  inversion H. subst.
  inversion H0.

  inversion H; subst.
  inversion H0.

  destruct H0; subst.
  - inversion H0.
    destruct (weq h default_hash); subst.
    unfold hash_safe in *.
    intuition.
    contradict_hashmap_get_default H1 hm2.
    rewrite hashmap_get_default in *; auto.

    rewrite upd_hashmap_eq; auto.
  - eapply IHhm2 in H5; eauto.
    destruct (weq h default_hash); subst.
    rewrite hashmap_get_default in *; auto.
    unfold hashmap_get. destruct (weq h default_hash); intuition.
    destruct (weq w h); subst.
    unfold hash_safe in *. intuition;
    rewrite H1 in H5; inversion H5; auto.

    unfold hashmap_get in H5; auto.
Qed.
Proof.
  induction hm3; intros;
  inversion H0; subst; auto.

  rewrite <- app_comm_cons.
  constructor; eauto.
Qed.
Proof.
  induction hm2; intros.
  inversion H0; subst; auto.

  inversion H0; subst; auto.
  destruct (weq h default_hash).
  rewrite e in *.
  rewrite hashmap_get_default in *; auto.

  destruct (weq w h); subst.
  rewrite upd_hashmap_eq; auto.
  unfold hash_safe in *.
  eapply IHhm2 in H; eauto.
  rewrite H in *. intuition. inversion H1.

  simpl.
  destruct (weq h default_hash); intuition.
  destruct (weq w h); intuition.
  eapply IHhm2; eauto.
Qed.
Proof.
  induction i; intros.
  destruct hl. inversion H0.
  destruct vl. inversion H.

  inversion H; subst.
  simpl. inversion H7.
  rewrite <- H2 in H0. inversion H0.
  simpl.
  inversion H6; subst.
  eapply hash_list_injective2 in H1; eauto.
  subst; auto.

  destruct hl. inversion H0.
  destruct vl. inversion H.

  simpl.
  eapply IHi.
  inversion H; subst. eauto.
  simpl in *. omega.
Qed.*)


Proof.
  induction vl; intros.
  inversion H; subst. constructor.

  inversion H; subst.
  constructor.
  apply hash_list_rep_upd; auto.
  eapply IHvl; auto.
Qed.
Proof.
  induction l; intros.
  inversion H; subst; auto.

  inversion H; subst.
  apply hash_list_prefixes_upd.
  eapply IHl; eauto. auto.
Qed.
Proof.
  induction hm; intuition; inversion H; intuition.
  eapply IHhm; eauto.
Qed.