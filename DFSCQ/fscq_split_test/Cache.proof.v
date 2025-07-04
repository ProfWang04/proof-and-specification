  Proof.
    unfold cachepred; intros.
    destruct (Map.find a cache); eauto.
    destruct p; destruct b; eauto.
  Qed.
  Proof.
    unfold synpred; intros.
    destruct (Map.find a cache); eauto.
    destruct p; destruct b; eauto.
  Qed.
  Proof.
    unfold rep; eauto.
  Qed.
  Proof.
    unfold synrep'; eauto.
  Qed.
  Proof.
    unfold synrep; eauto.
  Qed.
  Proof.
    unfold cachepred; intros.
    rewrite MapFacts.remove_neq_o; auto.
  Qed.
  Proof.
    unfold cachepred; intros.
    rewrite MapFacts.add_neq_o; auto.
  Qed.
  Proof.
    unfold synpred; intros.
    rewrite MapFacts.remove_neq_o; auto.
  Qed.
  Proof.
    unfold synpred; intros.
    rewrite MapFacts.add_neq_o; auto.
  Qed.
  Proof.
    intros.
    eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
    unfold cachepred at 3.
    rewrite MapFacts.remove_eq_o by auto.
    unfold ptsto_subset; cancel; eauto.
    rewrite mem_pred_pimpl_except; eauto.
    intros; apply cachepred_remove_invariant; eauto.
  Qed.
  Proof.
    unfold size_valid in *; intuition simpl.
    rewrite map_remove_cardinal by eauto; congruence.
    eapply le_trans.
    apply map_cardinal_remove_le; auto.
    auto.
  Qed.
  Proof.
    unfold size_valid in *; intuition simpl.
    rewrite Map.cardinal_1 in *.
    rewrite map_remove_not_in_elements_eq by auto. auto.
    eapply le_trans.
    apply map_cardinal_remove_le; auto.
    auto.
  Qed.
  Proof.
    unfold size_valid; intros.
    rewrite map_remove_cardinal.
    omega.
    apply In_MapsTo; auto.
  Qed.
  Proof.
    unfold size_valid, cache0; simpl; intros.
    rewrite Map.cardinal_1.
    rewrite MapProperties.elements_empty.
    intuition.
  Qed.
  Proof.
    unfold addr_valid; intros.
    apply H.
    eapply MapFacts.remove_in_iff; eauto.
  Qed.
  Proof.
    unfold addr_valid; intros.
    apply MapFacts.empty_in_iff in H.
    exfalso; auto.
  Qed.
  Proof.
    intros.
    assert (Map.In a cm).
    apply MapFacts.in_find_iff.
    destruct (Map.find a cm); try congruence.
    specialize (H0 _ H1).
    destruct (d a); try congruence; eauto.
  Qed.
  Proof.
    intros.
    edestruct addr_valid_mem_valid; eauto.
    exists (diskIs (mem_except d a)), x.
    eapply diskIs_extract' in H1.
    specialize (H1 d eq_refl).
    pred_apply; unfold ptsto_subset; cancel.
  Qed.
  Proof.
    intros.
    eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
    unfold cachepred at 3.
    rewrite MapFacts.add_eq_o by auto.
    unfold ptsto_subset; cancel; eauto.
    rewrite mem_pred_pimpl_except; eauto.
    intros; apply cachepred_add_invariant; eauto.
  Qed.
  Proof.
    unfold addr_clean; intros.
    apply ptsto_subset_valid' in H0; repeat deex.
    - rewrite mem_pred_extract with (a := a) by eauto.
      unfold cachepred at 2; rewrite H0.
      unfold ptsto_subset; cancel.
      rewrite sep_star_comm.
      eapply mem_pred_cachepred_remove_absorb; eauto.
    - rewrite mem_pred_extract with (a := a) by eauto.
      unfold cachepred at 2; rewrite H.
      unfold ptsto_subset; cancel.
      rewrite sep_star_comm.
      eapply mem_pred_cachepred_remove_absorb; eauto.
  Qed.
  Proof.
    unfold size_valid; intuition; simpl.
    rewrite map_add_dup_cardinal; auto.
    eexists; eapply MapFacts.find_mapsto_iff; eauto.
    rewrite map_add_dup_cardinal; auto.
    eexists; eapply MapFacts.find_mapsto_iff; eauto.
  Qed.
  Proof.
    unfold size_valid; intuition; simpl.

    destruct (Map.find a0 (CSMap cs)) eqn:?; try congruence.
    rewrite map_add_cardinal. omega.
    intuition repeat deex.
    apply MapFacts.find_mapsto_iff in H3; congruence.

    destruct (Map.find a0 (CSMap cs)) eqn:?.
    rewrite map_add_dup_cardinal; auto.
    eexists; eapply MapFacts.find_mapsto_iff; eauto.
    rewrite map_add_cardinal. omega.
    intuition repeat deex.
    apply MapFacts.find_mapsto_iff in H3; congruence.
  Qed.
  Proof.
    unfold addr_valid; intros.
    destruct (addr_eq_dec a a0); subst; try congruence.
    apply H0.
    eapply MapFacts.add_in_iff in H1; intuition.
  Qed.
  Proof.
    unfold addr_valid; intros.
    destruct (addr_eq_dec a a0); subst.
    rewrite upd_eq; congruence.
    rewrite upd_ne; auto.
  Qed.
  Proof.
    intros.
    eapply addr_valid_add; eauto.
    apply upd_eq; auto.
    apply addr_valid_upd; auto.
  Qed.
  Proof.
    unfold vsmerge, incl; simpl; intuition subst.
    specialize (H _ H0); intuition.
    specialize (H _ H0); intuition subst; auto.
  Qed.
  Proof.
    unfold vsmerge, incl; simpl; intuition subst.
    specialize (H _ H1); intuition subst.
    right; auto.
  Qed.
  Proof.
    unfold vsmerge, incl; intuition simpl in *.
    specialize (H0 _ H1); intuition subst; auto.
  Qed.
  Proof.
    unfold vsmerge; intuition.
  Qed.
  Proof.
    unfold incl; intros.
    specialize (H _ H0); auto.
  Qed.
  Proof.
    unfold incl, vsmerge; simpl; intros.
    specialize (H _ H1); intuition.
  Qed.
  Proof.
    intros.
    eapply incl_vsmerge_in''; eauto.
    eapply incl_vsmerge_trans; eauto.
  Qed.
  Proof.
    unfold writeback; intros.
    hoare.
    Unshelve. all: eauto.
  Qed.
  Proof.
    unfold writeback, rep; intros.

    prestep; norml; unfold stars; simpl;
    denote ptsto_subset as Hx; apply ptsto_subset_valid' in Hx; repeat deex.

    (* cached, dirty *)
    - rewrite mem_pred_extract with (a := a) by eauto.
      unfold cachepred at 2.
      destruct (Map.find a (CSMap cs)) eqn:Hm; try congruence.
      destruct p; destruct b; try congruence.
      cancel.
      step.
      erewrite <- upd_nop with (m := d) at 2 by eauto.
      rewrite <- mem_pred_absorb with (hm := d) (a := a).
      unfold cachepred at 3.
      rewrite MapFacts.add_eq_o by reflexivity.
      unfold ptsto_subset; cancel; eauto.
      rewrite mem_pred_pimpl_except.
      2: intros; apply cachepred_add_invariant; eassumption.
      cancel.
      eapply size_valid_add_in; eauto.
      eapply addr_valid_add; eauto.
      unfold addr_clean; right; eexists; simpl.
      apply MapFacts.add_eq_o; auto.
      eapply MapFacts.add_in_iff; eauto.

      (* crash *)
      unfold ptsto_subset; cancel; eauto.
      eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
      unfold cachepred at 3; rewrite Hm.
      unfold ptsto_subset; cancel; eauto.

    (* cached, non-dirty *)
    - cancel.
      step.
      unfold addr_clean; right; eexists; eauto.
      cancel.

    (* not cached *)
    - cancel.
      step.
      unfold addr_clean; left; auto.
      cancel.

    Unshelve. all: try exact addr_eq_dec.
  Qed.
  Proof.
    unfold evict; intros.
    step.
    prestep; unfold rep; cancel.

    eapply addr_clean_cachepred_remove; eauto.
    apply size_valid_remove; auto. eapply MapFacts.in_find_iff. congruence.
    apply addr_valid_remove; auto.
    eapply Map.remove_1; eauto.
    reflexivity.
    eapply size_valid_remove_cardinal_ok; eauto.

    eapply addr_clean_cachepred_remove; eauto.
    apply size_valid_remove_notin; auto. eapply MapFacts.not_find_in_iff. congruence.
    apply addr_valid_remove; auto.
    eapply Map.remove_1; eauto.
    reflexivity.
    eapply size_valid_remove_cardinal_ok; eauto.
  Qed.
  Proof.
    unfold maybe_evict; intros.
    step.
    unfold rep, size_valid in *; step.

    prestep; unfold rep; norml; unfold stars; simpl.

    (* found the victim  *)
    - edestruct addr_valid_ptsto_subset; eauto.
      norm. 2: intuition eauto. cancel.
      step.
      unfold rep; cancel.
      denote ( _ -> _ < _) as Hx; apply Hx.
      apply MapFacts.in_find_iff; congruence.

    (* victim not found, cache is empty *)
    - unfold size_valid in *; cancel.
      rewrite Map.cardinal_1, Heql; simpl; omega.

    (* victim not found, cache is non-empty *)
    - clear Heqo.
      assert (Map.find k (CSMap cs) = Some (p0_1, p0_2)).
      rewrite MapFacts.elements_o, Heql; simpl.
      destruct (MapFacts.eqb k k) eqn:?; auto.
      contradict Heqb.
      unfold MapFacts.eqb, MapOrdProperties.P.F.eq_dec.
      destruct (Nat.eq_dec k k); congruence.

      edestruct addr_valid_ptsto_subset; eauto; repeat deex.
      norm. 2: intuition eauto. cancel.
      step.
      unfold rep; cancel.
      denote ( _ -> _ < _) as Hx; apply Hx.
      apply MapFacts.in_find_iff; congruence.

    Unshelve. all: eauto; exact 0.
  Qed.
  Proof.
    unfold read, rep; intros.
    safestep; eauto.
    unfold rep; cancel.

    prestep; unfold rep; norml; unfold stars; simpl;
    edestruct ptsto_subset_valid'; eauto; intuition simpl in *;
    erewrite mem_pred_extract with (a := a) at 1 by eauto;
    unfold cachepred at 2; rewrite Heqo.

    (* found in cache *)
    - destruct b; simpl.
      unfold ptsto_subset; cancel.
      rewrite sep_star_comm.
      eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
      unfold cachepred at 3; rewrite Heqo.
      unfold ptsto_subset; cancel; eauto.

      cancel.
      eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
      unfold cachepred at 3.
      rewrite Heqo.
      unfold ptsto_subset; cancel; eauto.

    (* not found *)
    - cancel.
      step.
      eapply mem_pred_cachepred_add_absorb_clean; eauto.
      apply size_valid_add; auto.
      eapply addr_valid_add; eauto.

      cancel; eauto.
      eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
      unfold cachepred at 3.
      rewrite Heqo.
      unfold ptsto_subset; cancel; eauto.
  Qed.
  Proof.
    unfold write, rep; intros.
    safestep; eauto.
    unfold rep; cancel.

    prestep; unfold rep; norml; unfold stars; simpl.

    edestruct ptsto_subset_valid'; eauto; intuition simpl in *.
    erewrite mem_pred_extract with (a := a) at 1 by eauto.
    unfold cachepred at 2.
    destruct (Map.find a (CSMap r_)) eqn:Hm; try congruence.
    destruct p; destruct b.

    (* found in cache, was dirty *)
    - cancel.
      2: eapply size_valid_add_in; eauto.
      rewrite mem_pred_pimpl_except.
      2: intros; apply cachepred_add_invariant; eassumption.
      rewrite <- mem_pred_absorb with (hm := d) (a := a) (v := (v, p_1 :: x)).
      unfold cachepred at 3.
      rewrite MapFacts.add_eq_o by reflexivity; safecancel.
      eassign v0; rewrite ptsto_subset_pimpl.
      cancel.
      apply incl_tl; apply incl_refl.
      apply in_cons; auto.

      apply addr_valid_upd_add; auto.
      eapply ptsto_subset_upd; eauto.
      apply incl_cons2; auto.

    (* found in cache, was clean *)
    - cancel.
      2: eapply size_valid_add_in; eauto.
      rewrite mem_pred_pimpl_except.
      2: intros; apply cachepred_add_invariant; eassumption.
      rewrite <- mem_pred_absorb with (hm := d) (a := a) (v := (v, p_1 :: x)).
      unfold cachepred at 3.
      rewrite MapFacts.add_eq_o by reflexivity; safecancel.
      rewrite ptsto_subset_pimpl.
      cancel.
      apply incl_tl; apply incl_refl.
      left; auto.
      apply addr_valid_upd_add; auto.
      eapply ptsto_subset_upd; eauto.
      apply incl_cons; simpl; auto.
      eapply incl_tran; eauto; apply incl_tl; apply incl_refl.

    (* not found in cache *)
    - edestruct ptsto_subset_valid'; eauto; intuition simpl in *.
      erewrite mem_pred_extract with (a := a) at 1 by eauto.
      unfold cachepred at 2.
      destruct (Map.find a (CSMap r_)) eqn:Hm; try congruence.

      cancel.
      2: apply size_valid_add; eauto.
      rewrite mem_pred_pimpl_except.
      2: intros; apply cachepred_add_invariant; eassumption.
      rewrite <- mem_pred_absorb with (hm := d) (a := a) (v := (v, v0_cur :: x)).
      unfold cachepred at 3.
      rewrite MapFacts.add_eq_o by reflexivity; safecancel.
      rewrite ptsto_subset_pimpl.
      cancel.
      apply incl_tl; apply incl_refl.
      left; auto.
      apply addr_valid_upd_add; auto.
      eapply ptsto_subset_upd; eauto.
      apply incl_cons; simpl; auto.
      eapply incl_tran; eauto; apply incl_tl; apply incl_refl.
  Qed.
  Proof.
    unfold cachepred, synpred, addr_clean; intros.
    destruct (Map.find a cm) eqn:?.
    destruct p, b; cancel.
    apply incl_cons; auto; apply incl_nil.
    deex; congruence.
    apply incl_nil.
    cancel.
    apply incl_nil.
  Qed.
  Proof.
    induction l; simpl; intros.
    cancel; simpl; auto.
    rewrite cachepred_synpred, IHl.
    safecancel.
    eassign ((a_1, (a_2_cur, vs'_old)) :: l'); simpl.
    cancel.
    constructor; auto.
    unfold avs_match; simpl; intuition.
    auto.
  Qed.
  Proof.
    unfold avs_match; induction 1; simpl; auto.
    f_equal; auto.
    destruct x, y; intuition.
  Qed.
  Proof.
    induction l; destruct l'; simpl; try congruence; intros; cbn.
    cbv; intuition.
    destruct a, p; simpl in *.
    inversion H; subst.
    apply mem_match_upd.
    apply IHl; auto.
  Qed.
  Proof.
    unfold addr_valid; intros.
    specialize (H0 _ H1).
    edestruct mem_match_cases with (a := a); eauto; intuition.
    repeat deex; congruence.
  Qed.
  Proof.
    intros.
    eapply addr_valid_mem_match; eauto.
    apply avs2mem_mem_match.
    apply avs_match_map_fst_eq; auto.
  Qed.
  Proof.
    intros.
    eapply addr_valid_mem_match; eauto.
    apply avs2mem_mem_match.
    apply eq_sym.
    apply avs_match_map_fst_eq; auto.
  Qed.
  Proof.
    unfold possible_sync; induction 1; intuition.
    unfold avs_match in H.
    specialize (IHForall2 a); destruct x, y; cbn.
    destruct p, p0; intuition; simpl in *; subst; repeat deex.
    - destruct (addr_eq_dec a n); subst.
      repeat rewrite upd_eq; auto.
      right; do 3 eexists; intuition.
      repeat rewrite upd_ne; auto.
    - destruct (addr_eq_dec a n); subst.
      repeat rewrite upd_eq; auto.
      right; do 3 eexists; intuition.
      repeat rewrite upd_ne; auto.
      right; do 3 eexists; intuition eauto.
  Qed.
  Proof.
    unfold sync_invariant; intros.
    eapply H0; eauto.
    apply avs_match_possible_sync; auto.
  Qed.
  Proof.
    unfold cachepred, synpred; intros.
    rewrite sync_xform_exists_comm.
    apply pimpl_exists_l; intro vs0.
    rewrite sync_xform_sep_star_dist.
    destruct vs0 as [v0 l0].
    destruct (Map.find a cm) eqn:?; try destruct p, b;
    rewrite sync_xform_lift_empty, sync_xform_ptsto_subset_precise;
    unfold ptsto_subset; cancel; apply incl_nil.
  Qed.
  Proof.
    intros; rewrite sync_xform_listpred'; eauto.
    intros; eapply synpred_cachepred_sync.
  Qed.
  Proof.
    intros.
    rewrite pimpl_and_r_exists.
    unfold pimpl; intros. destruct H. destruct H. destruct_lift H0.
    exists x.
    eapply sep_star_lift_apply'; eauto.
    split; eauto.
  Qed.
  Proof.
    unfold synrep; intros.
    apply pimpl_l_and; eauto.
  Qed.
  Proof.
    induction l; simpl; intros.
    cbv in H1; congruence.
    inversion H; inversion H2; subst.
    destruct a; cbn in H1; simpl in *.
    destruct (addr_eq_dec n a0); subst.
    rewrite upd_eq in H1 by auto; inversion H1; subst; eauto.
    rewrite upd_ne in H1 by auto.
    eapply IHl; eauto; simpl in *.
  Qed.
  Proof.
    unfold synrep; intros.
    rewrite <- rep_synrep_split.
    apply pimpl_and_split; auto.
    unfold rep, synrep', mem_pred, mem_pred_one.
    norml; unfold stars; simpl.
    rewrite listpred_cachepred_synpred.
    cancel.
    eapply addr_valid_mem_match; eauto.
    apply avs2mem_mem_match.
    erewrite avs_match_map_fst_eq; eauto.
    erewrite avs_match_map_fst_eq; eauto.
    eapply avs_match_sync_invariant; eauto.
    eapply nil_if_clean_synced; eauto.
    erewrite avs_match_map_fst_eq; eauto.
  Qed.
  Proof.
    unfold begin_sync, synrep.
    step.
    prestep.
    norml; unfold stars; simpl.
    rewrite rep_synrep by eauto.
    cancel; eauto.
  Qed.
  Proof.
    unfold end_sync, synrep, synrep'.
    step.
    prestep; unfold mem_pred.
    norml; unfold stars, mem_pred_one; simpl.
    rewrite sync_xform_sep_star_dist. rewrite sync_xform_and_dist.
    rewrite sep_star_and_distr'. rewrite pimpl_r_and.
    unfold rep, mem_pred, mem_pred_one. 
    repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty || rewrite sync_xform_exists_comm).
    norml; unfold stars; simpl.
    repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty || rewrite sync_xform_exists_comm).
    cancel.
    rewrite sync_xform_listpred_synpred_cachepred.
    rewrite sync_xform_sync_invariant by auto.
    cancel.
    all: auto.
    rewrite pimpl_l_and.
    cancel.
  Qed.
  Proof.
    unfold sync; intros.
    eapply pimpl_ok2; monad_simpl. apply writeback_ok'.
    intros.
    norml; unfold stars; simpl.
    denote (_ d) as Hx; apply ptsto_subset_valid' in Hx as Hy; repeat deex.
    denote (_ d0) as Hz; apply ptsto_subset_valid' in Hz as Hy; repeat deex.
    unfold synrep, rep, synrep'.
    rewrite lift_empty_and_distr_l; norml; unfold stars; simpl.
    rewrite mem_pred_extract with (a := a) (hm := d) by eauto.
    rewrite mem_pred_extract with (a := a) (hm := d0) by eauto.
    unfold cachepred at 2; unfold synpred at 2; simpl in *.
    destruct (Map.find a (CSMap cs)) eqn:?; try destruct p, b.
    - unfold ptsto_subset.
      repeat (rewrite pimpl_exists_l_star_r ||
              rewrite pimpl_exists_r_star_r ||
              rewrite pimpl_and_l_exists ||
              rewrite pimpl_and_r_exists ||
              apply pimpl_exists_l; intros ).
      setoid_rewrite sep_star_assoc at 2.
      rewrite sep_star_lift_empty.
      setoid_rewrite sep_star_assoc at 2.
      rewrite sep_star_lift_empty.
      setoid_rewrite <- sep_star_assoc at 1 2.
      rewrite lift_empty_and_distr_r.
      norml; unfold stars; simpl; subst.
      rewrite sep_star_ptsto_and_eq.
      cancel; subst; eauto.

      prestep; norml; unfold stars; simpl.
      2: intuition; repeat deex; congruence.
      inv_option_eq.
      cancel.
      2: eapply ptsto_subset_upd with (vs' := nil); eauto; apply incl_refl.
      rewrite sep_star_and_distr; unfold synrep.
      apply pimpl_and_split.
      + rewrite pimpl_l_and; unfold rep; cancel.
        erewrite <- upd_nop with (m := d0) at 2 by eauto.
        rewrite <- mem_pred_absorb with (hm := d0) (a := a).
        unfold cachepred at 3.
        rewrite MapFacts.add_eq_o by reflexivity.
        unfold ptsto_subset; cancel; eauto.
        rewrite mem_pred_pimpl_except.
        2: intros; apply cachepred_add_invariant; eassumption.
        cancel.
        eapply size_valid_add_in; eauto.
        eapply addr_valid_add; eauto.
      + rewrite pimpl_r_and; unfold synrep'; cancel.
        rewrite <- mem_pred_absorb with (hm := d) (a := a).
        unfold synpred at 3.
        rewrite MapFacts.add_eq_o by reflexivity.
        unfold ptsto_subset; cancel; eauto.
        rewrite mem_pred_pimpl_except.
        2: intros; apply synpred_add_invariant; eassumption.
        cancel.
        eapply size_valid_add_in; eauto.
        eapply addr_valid_add; eauto.
        rewrite upd_eq; auto.
        apply addr_valid_upd; auto.
      + (* crash *)
        cancel.
        rewrite sep_star_and_distr, pimpl_l_and.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        eapply incl_tran; eauto.

    - unfold ptsto_subset.
      repeat (rewrite pimpl_exists_l_star_r ||
              rewrite pimpl_exists_r_star_r ||
              rewrite pimpl_and_l_exists ||
              rewrite pimpl_and_r_exists ||
              apply pimpl_exists_l; intros ).
      setoid_rewrite sep_star_assoc at 2.
      rewrite sep_star_lift_empty.
      setoid_rewrite sep_star_assoc at 2.
      rewrite sep_star_lift_empty.
      setoid_rewrite <- sep_star_assoc at 1 2.
      rewrite lift_empty_and_distr_r.
      norml; unfold stars; simpl; subst.
      rewrite sep_star_ptsto_and_eq.
      cancel; subst; eauto.

      prestep; norml; unfold stars; simpl;
      intuition; repeat deex; try congruence; inv_option_eq.
      cancel.
      2: eapply ptsto_subset_upd with (vs' := nil); eauto; apply incl_refl.
      rewrite sep_star_and_distr; unfold synrep.
      apply pimpl_and_split.
      + rewrite pimpl_l_and; unfold rep; cancel.
        erewrite <- upd_nop with (m := d0) at 2 by eauto.
        rewrite <- mem_pred_absorb with (hm := d0) (a := a).
        unfold cachepred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel.
        eapply incl_tran; eauto.
      + rewrite pimpl_r_and; unfold synrep'; cancel.
        rewrite <- mem_pred_absorb with (hm := d) (a := a).
        unfold synpred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        apply addr_valid_upd; auto.
      + (* crash *)
        cancel.
        rewrite sep_star_and_distr, pimpl_l_and.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        eapply incl_tran; eauto.

    - unfold ptsto_subset.
      repeat (rewrite pimpl_exists_l_star_r ||
              rewrite pimpl_exists_r_star_r ||
              rewrite pimpl_and_l_exists ||
              rewrite pimpl_and_r_exists ||
              apply pimpl_exists_l; intros ).
      setoid_rewrite sep_star_assoc at 2.
      rewrite sep_star_lift_empty.
      setoid_rewrite <- sep_star_assoc at 1 2.
      rewrite lift_empty_and_distr_r.
      norml; unfold stars; simpl; subst.
      rewrite sep_star_ptsto_and_eq.
      cancel; subst; eauto.

      prestep; norml; unfold stars; simpl;
      intuition; repeat deex; try congruence; inv_option_eq.
      cancel.
      2: eapply ptsto_subset_upd with (vs' := nil); eauto; apply incl_refl.
      rewrite sep_star_and_distr; unfold synrep.
      apply pimpl_and_split.
      + rewrite pimpl_l_and; unfold rep; cancel.
        erewrite <- upd_nop with (m := d0) at 2 by eauto.
        rewrite <- mem_pred_absorb with (hm := d0) (a := a).
        unfold cachepred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel.
        eapply incl_tran; eauto.
      + rewrite pimpl_r_and; unfold synrep'; cancel.
        rewrite <- mem_pred_absorb with (hm := d) (a := a).
        unfold synpred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        apply addr_valid_upd; auto.
      + (* crash *)
        cancel.
        rewrite sep_star_and_distr, pimpl_l_and.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        eapply incl_tran; eauto.

    Unshelve. all: eauto.
  Qed.
  Proof.
    unfold synrep, rep, synrep', ptsto_subset; intros.
    case_eq (d0 a); intros.
    - destruct p.
      eapply any_sep_star_ptsto in H1.
      pred_apply.
      safecancel.
      eassign (w, l).
      eassign l.
      cancel.
      firstorder.
    - destruct H.
      destruct_lift H.
      destruct_lift H2.
      destruct_lift H0.
      apply ptsto_valid' in H0.
      eapply mem_pred_absent_lm in H; eauto.
      eapply mem_pred_absent_hm in H2; eauto.
      congruence.

      unfold synpred, ptsto_subset; intros.
      destruct (Map.find a0 (CSMap cs)); try destruct p; try destruct b; cancel.

      unfold cachepred, ptsto_subset; intros.
      destruct (Map.find a0 (CSMap cs)); try destruct p; try destruct b; cancel.
  Qed.
  Proof.
    unfold pimpl; intros.
    eapply sync_synrep_helper_1 in H; eauto; repeat deex.
    pred_apply; cancel.
  Qed.
  Proof.
    intros.
    eapply pimpl_ok2; monad_simpl.
    apply sync_ok'.
    intros; norml; unfold stars; simpl.
    rewrite sync_synrep_helper_2 by eauto.
    safecancel.
    eauto.
    step.
  Qed.
  Proof.
    unfold sync_one.
    hoare.
  Qed.
  Proof.
    unfold sync_two.
    hoare.
  Qed.
  Proof.
    unfold cachepred; intros.
    case_eq (Map.find a m); intros; try destruct p, b.
    - xform_norm; subst.
      rewrite crash_xform_ptsto_subset.
      cancel; subst.
      apply in_inv in H1; simpl in *; intuition subst;
      apply in_cons; auto.
    - xform_norm; subst.
      rewrite crash_xform_ptsto_subset.
      cancel.
    - xform_norm; subst.
      rewrite crash_xform_ptsto_subset.
      cancel.
  Qed.
  Proof.
    intros.
    rewrite xform_mem_pred.
    unfold mem_pred at 1.
    xform_norm; subst.

    rename hm_avs into l.
    revert H; revert l.
    induction l; simpl; intros.
    cancel.
    apply mem_pred_empty_mem.
    unfold possible_crash; intuition.

    inversion H; destruct a; subst; simpl in *.
    unfold mem_pred_one; simpl.

    rewrite IHl by auto.
    xform_norm.
    rewrite xform_cachepred_ptsto.
    norml; unfold stars; simpl.
    apply pimpl_exists_r.
    exists (upd m' n (v, nil)).
    rewrite <- mem_pred_absorb.
    unfold cachepred at 3; unfold ptsto_subset.
    rewrite MapFacts.empty_o; cancel.
    erewrite <- notindomain_mem_eq; auto.
    eapply possible_crash_notindomain; eauto.
    apply avs2mem_notindomain; auto.
    apply possible_crash_upd; eauto.
  Qed.
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite xform_mem_pred_cachepred.
    cancel.
    eassign (cache0 (CSMaxCount cs)); cancel.
    all: unfold cache0; simpl; eauto.
    unfold size_valid in *; intuition.
    unfold addr_valid in *; intuition.
    eapply MapFacts.empty_in_iff; eauto.
  Qed.
  Proof.
    intros.
    rewrite crash_xform_rep.
    norm. cancel. split; auto.
    exists m; eauto.
  Qed.
  Proof.
    unfold mem_pred_one; simpl; intros.
    unfold cachepred at 1 in H.
    destruct (Map.find a buf) eqn: Heq; try destruct p, b;
    unfold ptsto_subset in H; destruct_lift H;
    eapply ptsto_mem_except; pred_apply; eauto.
  Qed.
  Proof.
    unfold mem_pred; intros.
    destruct H; destruct_lift H.
    generalize dependent m''.
    generalize dependent m.
    generalize dependent x.
    induction x; intros.
    - exists nil.
      rewrite listpred_nil in *.
      apply sep_star_assoc.
      apply lift_impl; intros.
      simpl; auto.
      cbn in *; subst.
      assert (@emp _ addr_eq_dec _ m) by firstorder.
      apply lift_impl; intros; auto.
      apply emp_empty_mem_only; auto.

    - destruct a.
      inversion H2; subst.
      edestruct IHx; eauto.
      + rewrite notindomain_mem_eq with (a := n).
        erewrite mem_except_upd.
        apply mem_match_except; eauto.
        apply avs2mem_notindomain; eauto.
      + eapply listpred_cachepred_mem_except; eauto.
      + destruct (mem_match_cases n H0).
        exists x0.
        destruct H3.
        rewrite mem_except_none in H1; eauto.

        do 3 destruct H3.
        exists ((n, x1) :: x0).
        destruct_lift H1.
        apply sep_star_assoc.
        apply lift_impl; intros.
        apply NoDup_cons; eauto.
        eapply avs2mem_none_notin; eauto.
        denote mem_except as Hx; rewrite <- Hx.
        apply mem_except_eq.

        apply lift_impl; intros.
        cbn; denote mem_except as Hx; setoid_rewrite <- Hx.
        rewrite upd_mem_except.
        rewrite upd_nop; auto.

        unfold mem_pred_one, cachepred at 1; simpl.
        unfold ptsto_subset; simpl.
        apply pimpl_exists_r_star.
        exists x1_old.
        apply sep_star_assoc.
        apply mem_except_ptsto; eauto.
        eapply sep_star_lift_r'; eauto.
        split; unfold lift; eauto.
        apply incl_refl.
  Qed.
  Proof.
    induction l; simpl; intros.
    - apply emp_empty_mem_only in H; subst.
      unfold mem_pred. exists nil; simpl.
      eapply pimpl_apply; [ | apply emp_empty_mem ].
      cancel.
      constructor.
    - unfold mem_pred in *.
      apply ptsto_mem_except in H as H'.
      specialize (IHl _ _ H').
      destruct IHl.
      destruct_lift H0.
      exists ((start, (a_cur, a_old)) :: x).
      simpl.
      unfold mem_pred_one at 1. unfold cachepred at 1.
      rewrite MapFacts.empty_o; simpl.

      eapply pimpl_apply.
      2: eapply mem_except_ptsto.
      3: eassumption.
      2: apply ptsto_valid in H; eauto.
      rewrite ptsto_pimpl_ptsto_subset.
      cancel.

      constructor; auto.
      eapply avs2mem_none_notin; eauto.
      denote avs2mem as Heq; rewrite <- Heq.
      apply mem_except_eq.
      cbn.
      denote avs2mem as Heq; setoid_rewrite <- Heq.
      rewrite upd_mem_except.
      rewrite upd_nop; eauto.
      eapply ptsto_valid; eauto.
  Qed.
  Proof.
    induction l; simpl; intros.
    exists nil; simpl; eauto.
    rewrite IHl.
    unfold ptsto_subset.
    norml; unfold stars; simpl.
    exists ((a_cur, old) :: l'); simpl.
    pred_apply; cancel.
  Qed.
  Proof.
    intros.
    apply arrayS_arrayN in H.
    destruct_lift H.
    eapply mem_pred_cachepred_refl_arrayN; eauto.
  Qed.
  Proof.
    unfold possible_crash, mem_match; intuition.
    specialize (H a); intuition.
    repeat deex; congruence.
    specialize (H a); intuition.
    repeat deex; congruence.
  Qed.
  Proof.
    induction l; intros; eauto.
    destruct a; subst; simpl in *; intuition.
    unfold mem_pred_one at 1, cachepred at 1 in H0; simpl in *.
    destruct (Map.find n cs) eqn: Heq; try destruct p0, b;
    unfold ptsto_subset in *; destruct_lifts;
    eapply notindomain_mem_except with (a' := n); eauto;
    apply IHl; eauto;
    eapply ptsto_mem_except; eauto.
  Qed.
  Proof.
    unfold mem_pred; intros.
    destruct_lift H; subst.
    rename dummy into l.
    apply avs2mem_none_notin in H0 as Hx.
    erewrite listpred_cachepred_notin with (m := m2); eauto.
  Qed.
  Proof.
    intros.
    specialize (H0 a); intuition try congruence; repeat deex.
    rewrite H0 in H1; inversion_clear H1; subst.
    eapply mem_pred_extract in H; eauto.
    unfold cachepred in H at 2.
    destruct (Map.find a cs) eqn:?; try destruct p, b;
    unfold ptsto_subset in H; destruct_lift H;
    denote incl as Hx; apply incl_in_nil in Hx; subst.
    intuition.
    eapply ptsto_valid'; eauto.
    eapply ptsto_valid'; eauto.
  Qed.
  Proof.
    intros.
    apply functional_extensionality; intros.
    destruct (m1 x) eqn: Heq.
    erewrite mem_pred_cachepred_some; eauto.
    eapply mem_pred_cachepred_none in H; eauto.
  Qed.
  Proof.
    intros.
    replace m2 with m1.
    apply possible_crash_refl.
    eapply possible_crash_synced; eauto.
    eapply mem_pred_cachepred_eq; eauto.
    eapply possible_crash_synced; eauto.
  Qed.
  Proof.
    unfold rep; intros.
    cancel.
    xform_normr.
    cancel.
    unfold pimpl, crash_xform; intros.
    eexists; split.
    eapply mem_pred_cachepred_refl; eauto.
    apply possible_crash_mem_match; auto.
    eapply possible_crash_trans.
    eauto.
    eapply mem_pred_possible_crash_trans; eauto.
    unfold size_valid in *; intuition.
    unfold addr_valid in *; intuition.
    eapply MapFacts.empty_in_iff; eauto.
  Qed.
  Proof.
    intros.
    unfold crash_xform in H; deex.
    rewrite crash_xform_rep_r by eauto.
    cancel.
  Qed.
  Proof.
    unfold cachepred; intros.
    case_eq (Map.find a m); intros; try destruct p, b.
    - rewrite sync_xform_exists_comm.
      apply pimpl_exists_l; intro.
      rewrite sync_xform_sep_star_dist, sync_xform_lift_empty.
      rewrite sync_xform_ptsto_subset_precise; simpl.
      cancel.
      apply in_cons; auto.
    - rewrite sync_xform_sep_star_dist, sync_xform_lift_empty.
      rewrite sync_xform_ptsto_subset_precise; simpl.
      cancel.
    - rewrite sync_xform_ptsto_subset_precise; cancel.
  Qed.
  Proof.
    intros.
    rewrite sync_xform_mem_pred.
    unfold mem_pred at 1.
    xform_norm; subst.

    rename hm_avs into l.
    revert H; revert l.
    induction l; simpl; intros.
    cancel.
    apply mem_pred_empty_mem.
    unfold possible_crash; intuition.

    inversion H; destruct a; subst; simpl in *.
    unfold mem_pred_one; simpl.

    rewrite IHl by auto.
    xform_norm.
    rewrite sync_xform_cachepred.
    norml; unfold stars; simpl.
    apply pimpl_exists_r.
    exists (upd m' n (v, nil)).
    rewrite <- mem_pred_absorb.
    unfold cachepred at 3; unfold ptsto_subset.
    rewrite MapFacts.empty_o; cancel.
    erewrite <- notindomain_mem_eq; auto.
    eapply possible_crash_notindomain; eauto.
    apply avs2mem_notindomain; auto.
    apply possible_crash_upd; eauto.
  Qed.
  Proof.
    unfold init_recover, init, rep.
    step.
    prestep; norml; unfold stars; simpl.
    rewrite sync_xform_sep_star_dist.
    rewrite sync_xform_mem_pred_cachepred; norm.
    cancel.
    rewrite sync_xform_sync_invariant; auto.
    intuition eauto.
    unfold size_valid in *; intuition.
    unfold addr_valid in *; intuition.
    eapply MapFacts.empty_in_iff; eauto.
    unfold crash_xform; eexists; eauto.
  Qed.
  Proof.
    induction l; simpl; intros.
    rewrite sync_xform_emp; cancel.
    rewrite sync_xform_sep_star_dist.
    rewrite sync_xform_ptsto_subset_preserve.
    rewrite IHl.
    cancel.
  Qed.
  Proof.
    unfold init_load, init, rep.
    step.

    eapply pimpl_ok2; monad_simpl; eauto.
    simpl; intros.

    (**
     * Special-case for initialization, because we are moving a predicate [F]
     * from the base memory to a virtual memory.
     *)
    unfold pimpl; intros.
    destruct_lift H; subst.

    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    exists m.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sync_xform_arrayS in H.

    eapply mem_pred_cachepred_refl_arrayS; eauto.
    intuition.
    apply size_valid_cache0; eauto.
    apply addr_valid_empty.
    apply sync_xform_arrayS in H; eauto.
  Qed.
  Proof.
    intros.
    eapply pimpl_ok2; monad_simpl.
    apply write_ok'.
    cancel.
    cancel.
    xcrash_rewrite.

    rewrite crash_xform_rep.
    unfold rep at 1; xform_norm.
    edestruct ptsto_subset_valid' with (a := a); eauto; intuition.
    edestruct possible_crash_sel_exis; eauto; intuition.
    rewrite mem_pred_extract with (a := a) by eauto.

    cancel; xform_normr.
    rewrite <- crash_xform_rep_r.
    unfold rep; cancel.
    eapply pimpl_trans2.
    eapply mem_pred_absorb_nop with (a := a).
    2: apply pimpl_refl.
    eauto.
    eauto.
    eauto.
    eapply ptsto_subset_upd; eauto.
    2: eapply possible_crash_ptsto_upd_incl' with (m := d); eauto.
    2: apply incl_tl; apply incl_refl.
    apply incl_cons2; auto.
  Qed.
  Proof.
    unfold read_array.
    hoare.
    rewrite isolateN_fwd with (i:=i) by auto.
    rewrite <- surjective_pairing.
    cancel.
  Qed.
  Proof.
    intros.
    rewrite crash_xform_rep.
    unfold rep at 1; xform_norm.
    edestruct arrayN_selN_subset with (a := a + i); eauto; try omega; intuition.
    replace (a + i - a) with i in * by omega.
    edestruct possible_crash_sel_exis; eauto; intuition.
    rewrite mem_pred_extract with (a := a + i) by eauto.

    cancel; xform_normr.
    rewrite <- crash_xform_rep_r.
    unfold rep; cancel.
    eapply pimpl_trans2.
    eapply mem_pred_absorb_nop with (a := a + i).
    2: apply pimpl_refl.
    eauto.
    eauto.
    eauto.
    apply arrayN_subset_memupd; eauto.
    2: eapply possible_crash_ptsto_upd_incl' with (m := d); eauto.
    2: apply incl_tl; apply incl_refl.
    apply incl_cons2; auto.
  Qed.
  Proof.
    unfold write_array, vsupd.
    intros.
    eapply pimpl_ok2; monad_simpl.
    apply write_ok'.
    cancel.

    rewrite isolateN_fwd with (i:=i) by auto.
    rewrite surjective_pairing with (p := selN vs i ($0, nil)).
    cancel.

    step.
    rewrite <- isolateN_bwd_upd by auto.
    cancel.

    cancel.
    xcrash_rewrite.
    apply write_array_xcrash_ok; auto.
  Qed.
  Proof.
    unfold sync_array, vssync.
    safestep.
    rewrite isolateN_fwd with (i:=i) by auto; cancel.
    eauto.
    step.
    rewrite <- isolateN_bwd_upd by auto.
    cancel.
  Qed.
  Proof.
    unfold read_range; intros.
    safestep. auto. auto.
    safestep.
    step; subst.

    rewrite firstn_S_selN_expand with (def := $0).
    rewrite fold_left_app; simpl.
    erewrite selN_map by omega; auto.
    rewrite map_length; omega.
    all: step.

    Unshelve. exact tt. eauto.
  Qed.
  Proof.
    induction l using rev_ind; simpl; intros.
    rewrite firstn_nil in H; cbn in *.
    apply crash_xform_pimpl; cancel.
    destruct (le_dec n (S (length l))).
    destruct (le_dec n (length l)).
    - rewrite app_length in *; simpl in *.
      rewrite firstn_app_l in H by auto.
      rewrite IHl; eauto; try omega.
      rewrite vsupd_range_app_tl; eauto.
      xform_norm.
      rewrite write_array_xcrash_ok with (i := length l); eauto.
      2: rewrite vsupd_range_length; try omega; rewrite firstn_length, app_length, Nat.min_l; simpl; omega.
      xform_norm; cancel.
      apply crash_xform_pimpl.
      cancel.
    - assert (n = length l + 1) by omega; subst.
      rewrite app_length in *; simpl in *.
      rewrite firstn_oob in H by (rewrite app_length; simpl; omega).
      apply crash_xform_pimpl.
      cancel.
    - rewrite firstn_oob in H.
      apply crash_xform_pimpl; cancel.
      rewrite app_length; simpl; omega.
  Qed.
  Proof.
    intros.
    xform_norm.
    erewrite vsupd_range_xcrash_firstn'; eauto.
    xform_norm.
    do 2 (xform_normr; cancel).
  Qed.
  Proof.
    unfold write_range; intros.
    safestep. auto. auto.
    prestep; unfold rep; cancel.

    rewrite vsupd_range_length; try omega.
    rewrite firstn_length_l; omega.
    prestep; unfold rep; cancel.
    erewrite firstn_S_selN_expand by omega.
    setoid_rewrite <- vsupd_range_progress; auto.

    cancel.
    repeat xcrash_rewrite.
    setoid_rewrite vsupd_range_progress; auto.
    rewrite <- firstn_plusone_selN by auto.

    apply vsupd_range_xcrash_firstn; auto.
    step.
    rewrite firstn_oob; auto.
    xcrash.
    Unshelve. exact tt.
  Qed.
  Proof.
    unfold sync_range; intros.
    step.
    step.
    rewrite vssync_range_length; omega.

    step.
    apply arrayN_unify.
    apply vssync_range_progress; omega.

    step.

    Unshelve. all: try exact tt.
  Qed.
  Proof.
    induction l using rev_ind; simpl; intros.
    exists d; split; auto.
    apply mem_incl_refl.
    rewrite vsupd_vecs_app; simpl.
    destruct x as [k v].
    apply forall_app_l in H0 as Hx; apply forall_app_r in H0 as Hy.
    apply Forall_inv in Hx; simpl in Hx.
    edestruct IHl; eauto; intuition.
    eexists; split; simpl in *.
    apply arrayN_subset_memupd; eauto.
    apply incl_refl.
    rewrite vsupd_vecs_length; auto.
    edestruct arrayN_selN_subset with (m := d) (a := a + k); eauto; try omega.
    intuition; replace (a + k - a) with k in * by omega.
    erewrite <- upd_nop with (m := d); eauto.
    apply mem_incl_upd; auto.

    destruct x0; simpl in *; subst.
    apply incl_cons; simpl.
    - apply in_cons.
      apply vsupd_vecs_selN_vsmerge_in.
      constructor; auto.
    - eapply incl_tran; eauto.
      apply vsupd_vecs_incl in H0.
      eapply forall2_selN in H0; eauto.
      rewrite vsupd_vecs_app in H0; simpl in H0; unfold vsupd in H0.
      rewrite selN_updN_eq in H0 by (rewrite vsupd_vecs_length; auto).
      eapply incl_tran; try eassumption.
      apply incl_tl; apply incl_refl.
    Unshelve. eauto.
  Qed.
  Proof.
    induction l; simpl; intros.
    rewrite firstn_nil in H; cbn in *.
    apply crash_xform_pimpl; cancel.

    destruct n; simpl in *.
    - inversion H0; subst; simpl in *.
      rewrite crash_xform_rep.
      unfold rep at 1; xform_norm.
      edestruct arrayN_selN_subset with (a := a + a0_1); eauto; try omega; intuition.

      edestruct possible_crash_sel_exis; eauto; intuition.
      rewrite mem_pred_extract with (a := a + a0_1) by eauto.
      rewrite <- vsupd_vecs_cons.
      edestruct vsupd_vecs_mem_exis with (l := (a0_1, a0_2) :: l); eauto; intuition.
      cancel; xform_normr.
      rewrite <- crash_xform_rep_r.
      unfold rep; cancel.
      eapply pimpl_trans2.
      eapply mem_pred_absorb_nop with (a := a + a0_1).
      2: apply pimpl_refl.
      eauto.
      eauto.
      eauto.
      eauto.
      eapply possible_crash_incl_trans; eauto.
    - rewrite IHl; eauto.
      inversion H0; subst.
      rewrite vsupd_length; auto.
    Unshelve. exact ($0, nil).
  Qed.
  Proof.
    intros.
    xform_norm.
    erewrite vsupd_vecs_xcrash_firstn'; eauto.
    xform_norm.
    do 2 (xform_normr; cancel).
  Qed.
  Proof.
    unfold write_vecs.
    safestep. auto. auto.
    step.
    prestep; unfold rep; cancel.

    erewrite firstn_S_selN_expand by auto.
    setoid_rewrite vsupd_vecs_app; simpl.
    cancel.

    repeat xcrash_rewrite.
    setoid_rewrite vsupd_vecs_progress; auto.
    apply vsupd_vecs_xcrash_firstn; auto.

    step.
    rewrite firstn_oob; auto.
    xcrash.
    Unshelve. exact tt.
  Qed.
  Proof.
    unfold sync_vecs; intros.
    step.
    apply app_nil_l.
    cancel.
    step.
    rewrite vssync_vecs_length.
    eapply Forall_inv with (P := fun x => x < length vs).
    eauto using forall_app_l.
    step.
    apply cons_nil_app.
    rewrite vssync_vecs_app; cancel.
    step.
    rewrite app_nil_r. cancel.
    Unshelve. all: eauto; constructor.
  Qed.
  Proof.
    unfold sync_vecs_now; intros.
    step.
    eapply pimpl_ok2; monad_simpl. apply sync_vecs_ok.
    cancel.
    step.
    step.
    cancel.
  Qed.