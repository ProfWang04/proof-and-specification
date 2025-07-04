  Proof.
    induction avs; simpl; intros; auto.
    destruct a; intuition.
    destruct (HighAEQ h a0); subst. intuition.
    f_equal; eauto.
  Qed.
  Proof.
    intros; simpl.
    destruct (HighAEQ a a); try congruence.
    apply avs_except_notin_eq.
    inversion H; auto.
  Qed.
  Proof.
    unfold avs2mem; simpl; intros.
    rewrite upd_ne; auto.
  Qed.
  Proof.
    induction avs; simpl; intros.
    - inversion H0.
    - destruct a.
      destruct (HighAEQ h a0); subst.
      + unfold avs2mem in H0; simpl in H0. rewrite upd_eq in H0 by auto. inversion H0; subst.
        inversion H.
        rewrite avs_except_notin_eq by auto. cancel.
      + inversion H.
        rewrite avs2mem_ne in H0 by auto.
        rewrite IHavs by eauto.
        cancel.
  Qed.
  Proof.
    induction avs; simpl; intros; eauto.
    destruct a.
    destruct (HighAEQ h a0); subst; eauto.
    simpl in *; intuition; eauto.
  Qed.
  Proof.
    unfold avs2mem, notindomain; induction l; simpl; intros.
    cbv; auto.
    destruct a; simpl in *; intuition.
    rewrite upd_ne; auto.
  Qed.
  Proof.
    induction avs; simpl; intros; eauto.
    destruct a.
    inversion H; subst.
    destruct (HighAEQ h a0); subst; eauto.
    simpl; constructor; eauto.
  Qed.
  Proof.
    induction avs; simpl; intros; eauto.
    destruct a.
    destruct (HighAEQ h a0); subst; eauto.
    rewrite avs2mem_ne by auto; auto.
  Qed.
  Proof.
    induction avs; simpl; intros; eauto.
    destruct a.
    destruct (HighAEQ h a0); subst.
    - rewrite avs2mem_ne; auto.
    - unfold avs2mem in *; simpl.
      destruct (HighAEQ h a'); subst.
      + repeat rewrite upd_eq; auto.
      + repeat rewrite upd_ne; auto.
  Qed.
  Proof.
    intros; apply functional_extensionality; intros.
    destruct (HighAEQ a x); subst.
    - rewrite mem_except_eq. rewrite avs2mem_except_eq. auto.
    - rewrite mem_except_ne by auto.
      rewrite avs2mem_except_ne by auto.
      auto.
  Qed.
  Proof.
    unfold avs2mem; induction avs; simpl; intros; auto.
    destruct a; intuition; simpl in *; subst.
    rewrite upd_eq in * by auto; congruence.
    destruct (HighAEQ h a0); subst.
    rewrite upd_eq in * by auto; congruence.
    rewrite upd_ne in * by auto; eauto.
  Qed.
  Proof.
    unfold mem_pred; intros.
    cancel.
    eapply listpred_avs_except; subst; eauto.
    eauto.
  Qed.
  Proof.
    apply mem_pred_extract'.
  Qed.
  Proof.
    unfold mem_pred; intros.
    norml.
    exists ((a, v) :: hm_avs).
    pred_apply.
    cancel.
    simpl; constructor; auto.
    apply avs2mem_none_notin.
    rewrite <- H3. apply mem_except_eq.
    unfold avs2mem in *; simpl.
    rewrite <- H3.
    rewrite upd_mem_except.
    auto.
  Qed.
  Proof.
    apply mem_pred_absorb'.
  Qed.
  Proof.
    unfold mem_pred; intros.
    norml.
    exists ( (a, v) :: hm_avs).
    pred_apply.
    cancel.
    simpl; constructor; auto.
    apply avs2mem_none_notin.
    rewrite <- H4. apply mem_except_eq.
    unfold avs2mem in *; simpl.
    rewrite <- H4.
    rewrite upd_mem_except.
    rewrite upd_nop; auto.
  Qed.
  Proof.
    apply mem_pred_absorb_nop'.
  Qed.
  Proof.
    unfold mem_pred, mem_pred_one, avs2mem; split; norm; auto.
    destruct hm_avs; try cancel.
    eapply equal_f with (x := p_1) in H2.
    rewrite upd_eq in H2 by auto.
    unfold empty_mem in H2; congruence.
    instantiate (1 := nil); cancel.
    intuition; constructor.
  Qed.
Proof.
  unfold mem_pred; intros.
  cancel; eauto.
  subst.
  induction hm_avs; simpl; intros; auto.
  unfold mem_pred_one at 1 3; simpl. rewrite H. cancel.
  eapply IHhm_avs.
  inversion H0; eauto.
Qed.
Proof.
  unfold mem_pred; intros.
  cancel; eauto.
  assert (~ In a' (map fst hm_avs)).
  eapply avs2mem_none_notin. rewrite <- H3. rewrite mem_except_eq. auto.
  clear H3 hm.
  induction hm_avs; simpl; intros; auto.
  unfold mem_pred_one at 1 3; simpl. rewrite H. cancel.
  eapply IHhm_avs; eauto.
  inversion H0; eauto.
  destruct a; firstorder.
Qed.
Proof.
  intros.
  case_eq (hm a); intros; auto.
  eapply mem_pred_extract in H1; eauto.
  rewrite H0 in H1; destruct_lift H1.
  apply ptsto_valid' in H1; congruence.
Qed.
Proof.
  intros.
  unfold mem_pred, mem_pred_one in H1. destruct_lift H1.
  apply avs2mem_none_notin in H.
  generalize dependent m.
  induction dummy; simpl in *; intros.
  - apply emp_empty_mem_only in H1; subst.
    firstorder.
  - destruct a0; simpl in *.
    rewrite H0 in H1.
    destruct (AEQ a0 a); try solve [ exfalso; eauto ].
    destruct_lift H1.
    generalize dependent H1.
    unfold_sep_star; intros; repeat safedeex.
    inversion H3.
    unfold ptsto, mem_union in H1.
    intuition; subst.
    match goal with
    | [ H : forall _, _ -> m1 _ = None |- _ ] => rewrite H
    end; eauto.
Qed.
Proof.
  unfold mem_pred; intros; split.
  xform_norm; subst.
  rewrite xform_listpred.
  cancel.

  cancel; subst.
  xform_normr; cancel.
  rewrite xform_listpred.
  cancel.
  eauto.
Qed.
Proof.
  unfold mem_pred; intros; split.
  rewrite sync_xform_exists_comm; apply pimpl_exists_l; intros.
  repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty).
  rewrite sync_xform_listpred; cancel.

  rewrite sync_xform_exists_comm; apply pimpl_exists_l; intros.
  apply pimpl_exists_r; eexists.
  repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty).
  rewrite sync_xform_listpred; cancel.
Qed.
Proof.
  unfold mem_pred; eauto.
Qed.
  Proof.
    firstorder.
  Qed.
  Proof.
    firstorder.
  Qed.
  Proof.
    firstorder.
  Qed.
  Proof.
    unfold mem_match; intros.
    unfold mem_except.
    destruct (AEQ a0 a); firstorder.
  Qed.
  Proof.
    unfold mem_match; intros.
    destruct (AEQ a0 a); subst.
    repeat rewrite upd_eq by auto.
    split; congruence.
    repeat rewrite upd_ne by auto.
    firstorder.
  Qed.
  Proof.
    unfold mem_match; intros.
    destruct (AEQ a0 a); subst.
    repeat rewrite upd_eq by auto.
    split; congruence.
    repeat rewrite upd_ne by auto.
    firstorder.
  Qed.
  Proof.
    unfold mem_match; intros.
    destruct (AEQ a0 a); subst.
    repeat rewrite upd_eq by auto.
    split; congruence.
    repeat rewrite upd_ne by auto.
    firstorder.
  Qed.
  Proof.
    intros.
    specialize (H a); destruct H.
    destruct (ma a); destruct (mb a).
    right. eexists; eauto.
    contradict H0; intuition; congruence.
    contradict H; intuition; congruence.
    intuition.
  Qed.
  Proof.
    intros.
    specialize (H a H0 H1).
    destruct (m a); try congruence.
    eexists; eauto.
  Qed.
  Proof.
    unfold region_filled; destruct l; simpl; intros.
    omega.
    destruct (addr_eq_dec a a0); subst.
    rewrite listupd_sel_oob by omega.
    rewrite upd_eq; congruence.
    erewrite listupd_sel_inb with (def := v) by omega.
    congruence.
  Qed.
  Proof.
    unfold region_filled; induction l; simpl; intros.
    omega.
    destruct (addr_eq_dec a1 a0); subst.
    apply sep_star_comm in H; apply sep_star_assoc in H.
    apply ptsto_valid in H; congruence.
    apply sep_star_assoc in H.
    eapply IHl; eauto; omega.
  Qed.
  Proof.
    induction l; simpl; auto; intros.
    apply IHl.
    eapply region_filled_sel in H0; eauto.
    destruct H0.
    eapply mem_match_upd_l; eauto.
    omega.
    unfold region_filled in *; intuition.
    eapply H0 with (a := a1); try omega; auto.
  Qed.
  Proof.
    unfold mem_incl; intros.
    destruct (m a) eqn: Heq; intuition.
    right; do 2 eexists; intuition.
  Qed.
  Proof.
    unfold mem_incl; intuition.
    specialize (H a); specialize (H0 a).
    intuition; repeat deex; try congruence.
    right.
    rewrite H1 in H0; inversion H0; subst.
    do 2 eexists; intuition eauto.
    eapply incl_tran; eauto.
  Qed.
  Proof.
    unfold possible_crash, mem_incl; intros.
    specialize (H a); specialize (H0 a).
    intuition; repeat deex; try congruence.
    right.
    rewrite H2 in H0; inversion H0; subst.
    do 2 eexists; intuition eauto.
  Qed.
  Proof.
    unfold mem_incl; intros.
    specialize (H a0).
    destruct (addr_eq_dec a a0); subst.
    repeat rewrite upd_eq by auto.
    intuition; repeat deex; intuition.
    right; do 2 eexists; eauto.
    right; do 2 eexists; eauto.
    repeat rewrite upd_ne by auto.
    intuition.
  Qed.
  Proof.
    induction 1; simpl; intros; auto.
    apply IHForall2.
    apply mem_incl_upd; auto.
  Qed.
  Proof.
    intros.
    apply mem_incl_listupd; auto.
    apply mem_incl_refl.
  Qed.