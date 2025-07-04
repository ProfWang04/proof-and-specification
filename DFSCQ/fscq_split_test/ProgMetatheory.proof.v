Proof.
  unfold buf_ne; intros.
  rewrite <- Eqdep_dec.eq_rect_eq_dec; auto.
  apply addr_eq_dec.
Qed.
Proof.
  unfold buf_ne; intros.
  congruence.
Qed.
Proof.
  unfold possible_sync; intros.
  destruct (m a).
  - right.
    destruct p.
    exists w, l, l; intuition auto.
    apply List.incl_refl.
  - left; auto.
Qed.
Proof.
  unfold hash_safe.
  case_eq (hashmap_get hm h); intros.
  destruct s.
  destruct (addr_eq_dec sz x); subst.
  destruct (weq buf w); subst.
  - (* hash is in hm with correct buffer *)
    eauto.
  - (* hash is in hm and buffers are same size, but unequal *)
    right; intro.
    intuition (try congruence).
    inversion H1.
    apply Eqdep_dec.inj_pair2_eq_dec in H2; eauto.
    apply addr_eq_dec.
  - (* hash is in hm but buffers are not same size *)
    right; intro.
    intuition (try congruence).
  - (* new hash *)
    left; eauto.
Defined.
Proof.
  induction hm; intros.
  - unfold hashmap_get in H0.
    destruct (weq (hash_fwd buf1) default_hash); subst.
    inversion H0; subst.
    apply Eqdep_dec.inj_pair2_eq_dec in H3; subst.
    eauto.
    apply addr_eq_dec.
    congruence.
  - unfold hashmap_get in H0.
    destruct (weq (hash_fwd buf1) default_hash); subst.
    inversion H0; subst.
    apply Eqdep_dec.inj_pair2_eq_dec in H3; subst.
    eauto.
    apply addr_eq_dec.
    fold (hashmap_get hm (hash_fwd buf1)) in H0.
    inversion H; subst.
    destruct (weq (hash_fwd buf) (hash_fwd buf1)); eauto.
    inversion H0; subst.
    apply Eqdep_dec.inj_pair2_eq_dec in H4; subst.
    eauto.
    apply addr_eq_dec.
Qed.
Proof.
  tauto.
Qed.
Proof.
  unfold hash_safe; intros.
  apply de_morgan in H0; intuition.
  case_eq (hashmap_get hm (hash_fwd buf)); intros;
    try solve [ exfalso; eauto ].
  destruct s.
  destruct (addr_eq_dec sz x); subst.
  destruct (weq buf w); subst.
  exfalso; eauto.
  exists _, w.
  apply hashmap_wf_get in H0; auto.
  exists _,  w.
  apply hashmap_wf_get in H0; eauto.
Qed.
Proof.
  intros.
  remember (Finished d' vm' hm' v).
  generalize dependent d'.
  generalize dependent vm'.
  generalize dependent hm'.
  generalize dependent v.
  induction H0; intros;
    repeat match goal with
        | [ H: @eq (outcome _) _ _ |- _ ] =>
          inversion H; subst; clear H
           end; eauto.
  match goal with
  | [ H: step _ _ _ _ _ _ _ _ |- _ ] =>
    inversion H; subst; eauto
  end.
  unfold upd_hashmap'; eauto.
  unfold upd_hashmap'; eauto.
Qed.
Proof.
  induction p; intros.
  - eauto.
  - case_eq (d a); intros; eauto.
    destruct p.
    eauto 10.
  - case_eq (d a); intros; eauto.
    destruct p.
    left.
    eexists.
    exists hm, tt.
    econstructor; eauto.
    eapply StepWrite; eauto.
  - left.
    eauto 10.
  - case_eq (d a); intros; eauto.
    left.
    eexists.
    exists hm, tt.
    econstructor; eauto.
    eapply StepTrim with (vs':=p); eauto.
  - destruct (hash_safe_dec hm (hash_fwd buf) buf).
    eauto 10.
    apply not_hash_safe_conflict in n; eauto.
  - specialize (IHp d hm).
    intuition eauto.
    repeat deex.
    specialize (H v' d' hm').
    assert (hashmap_wf hm') by eauto.
    intuition eauto.
    repeat deex.
    eauto 10.
Qed.