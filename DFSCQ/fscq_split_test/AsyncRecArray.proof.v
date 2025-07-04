  Proof.
    unfold items_valid; intros; split; intros;
    pose proof (well_formed_app_iff itemtype a b);
    rewrite app_length in *; intuition.
  Qed.
  Proof.
    intros; omega.
  Qed.
  Proof.
    intros. omega.
  Qed.
  Proof.
    unfold items_valid, roundup; intuition.
    pose proof (well_formed_app_iff itemtype a b); intuition.
    rewrite app_length.
    eapply le_add_helper. apply H.
    rewrite le_plus_minus_r.
    apply mult_le_compat_r.
    apply divup_le; lia.
    apply roundup_ge.
    apply items_per_val_gt_0.
  Qed.
  Proof.
    unfold items_valid; intros; split; intros;
    pose proof (well_formed_app_iff itemtype a b);
    rewrite app_length in *; intuition.

    apply le_add_le_sub; auto.
    eapply Nat.mul_le_mono_pos_r.
    apply items_per_val_gt_0.
    rewrite <- H; omega.

    rewrite Nat.sub_add_distr.
    rewrite Nat.mul_sub_distr_r.
    apply Nat.le_add_le_sub_l.
    setoid_rewrite <- H; auto.
  Qed.
  Proof.
    unfold items_valid, roundup; intuition.
    apply well_formed_app_iff; intuition.
    rewrite app_length.
    rewrite Nat.sub_add_distr in H8.
    rewrite Nat.mul_sub_distr_r in H8.
    rewrite <- H in H8.
    omega.
  Qed.
  Proof.
    unfold synced_array, rep_common; cancel; subst; auto.
  Qed.
  Proof.
    unfold array_rep, synced_array, rep_common; intros.
    split; cancel; subst; simpl; unfold items_valid, eqlen;
      try setoid_rewrite ipack_nil; simpl; intuition; auto.
  Qed.
  Proof.
    unfold array_rep, synced_array, rep_common; intros.
    cancel; subst; simpl; unfold items_valid, eqlen;
      try setoid_rewrite ipack_nil; simpl; intuition; auto.
  Qed.
  Proof.
    intros.
    unfold array_rep, synced_array, rep_common, eqlen; intros.
    norm.
    eassign (@nil valu).
    cancel.
    subst; repeat setoid_rewrite ipack_nil; simpl; auto;
    unfold items_valid in *; intuition.
    rewrite nils_length; auto.
  Qed.
  Proof.
    unfold array_rep, synced_array, unsync_array; destruct st; eauto.
  Qed.
  Proof.
    unfold avail_rep; eauto.
  Qed.
  Proof.
    unfold synced_array; intros.
    xform; cancel; subst.
    rewrite crash_xform_arrayN_subset_combine_nils.
    cancel.
    auto.
  Qed.
  Proof.
    intros; simpl.
    apply xform_synced_array.
  Qed.
  Proof.
    unfold avail_rep; intros; intros.
    xform.
    rewrite crash_xform_arrayN_subset; cancel.
    unfold possible_crash_list in *; subst; intuition.
    rewrite H0.
    replace (combine l' (repeat [] (length l'))) with (synced_list l') by auto.
    rewrite synced_list_length; auto.
  Qed.
  Proof.
    unfold avail_rep; intros.
    xform.
    rewrite crash_xform_arrayN_subset; cancel;
    apply possible_crash_list_length in H3 as Hlength; subst.
    unfold possible_crash_list in *; subst; intuition.
    instantiate (l := fold_left iunpack l' []).
    unfold synced_array.
    cancel.
    unfold rep_common; intuition.
    unfold items_valid; intuition.
    rewrite fold_left_iunpack_length.
    congruence.

    apply ipack_iunpack; auto.

    unfold eqlen.
    rewrite repeat_length; auto.

    rewrite fold_left_iunpack_length.
    congruence.
  Qed.
  Proof.
    unfold unsync_array, avail_rep, rep_common; intros.
    xform.
    rewrite crash_xform_arrayN_subset.
    unfold possible_crash_list.
    cancel.
    rewrite combine_length_eq in *; simplen.
    rewrite <- ipack_length; auto.
    rewrite synced_list_length; auto.
  Qed.
  Proof.
    unfold array_rep, synced_array, unsync_array, rep_common, items_valid.
    destruct st; intros; destruct_lift H; subst;
    apply divup_le; rewrite Nat.mul_comm; eauto.
  Qed.
  Proof.
    intros; unfold pimpl; intros.
    apply array_rep_size_ok in H as H1.
    pred_apply; cancel.
  Qed.
  Proof.
    unfold array_rep, avail_rep, synced_array, unsync_array, rep_common, eqlen, nr_blocks.
    intros; destruct st; cancel; subst; autorewrite with lists.
    rewrite ipack_length; auto.
    rewrite <- ipack_length.
    rewrite Nat.min_l; simplen.
  Qed.
  Proof.
    intros; apply array_rep_avail.
  Qed.
  Proof.
    unfold avail_rep; intros; norm.
    instantiate (2 := (firstn n1 vsl)).
    instantiate (1 := (skipn n1 vsl)).
    cancel.
    rewrite Nat.add_assoc.
    rewrite arrayN_split by auto.
    cancel.
    intuition.
    rewrite firstn_length.
    rewrite Nat.min_l; omega.
    rewrite skipn_length.
    omega.
  Qed.
  Proof.
    unfold avail_rep; intros; norm.
    instantiate (1 := vsl ++ vsl0).
    setoid_rewrite arrayN_app.
    rewrite Nat.add_assoc.
    cancel.
    intuition.
    rewrite app_length; omega.
  Qed.
  Proof.
    intros; omega.
  Qed.
  Proof.
    intros; omega.
  Qed.
  Proof.
    simpl; intros;
    unfold synced_array, rep_common, nils; norm; subst; intuition.
    cancel.
    erewrite ipack_app by eauto.
    rewrite app_length, Nat.add_assoc.
    rewrite <- repeat_app.
    rewrite combine_app, arrayN_app, combine_length_eq by auto.
    repeat rewrite ipack_length.
    cancel.

    unfold items_valid, roundup in *; intuition.
    apply well_formed_app_iff; auto.
    rewrite app_length.
    eapply helper_add_le; eauto.
    rewrite Nat.sub_add_distr.
    setoid_rewrite Nat.mul_sub_distr_r at 2.
    apply helper_add_sub.
    apply roundup_ge; auto.
    apply Nat.mul_le_mono_r; omega.

    erewrite ipack_app; eauto.
    simplen.
  Qed.
  Proof.
    simpl; intros;
    unfold synced_array, rep_common, nils, eqlen; norm; subst; intuition;
    try rewrite repeat_length; auto.
    cancel.
    erewrite ipack_app by eauto.
    rewrite app_length, Nat.add_assoc.
    rewrite <- repeat_app.
    rewrite combine_app, arrayN_app, combine_length_eq by (rewrite repeat_length; auto).
    repeat rewrite ipack_length.
    cancel.
    apply (@items_valid_app xp start a b H1).
    rewrite H, divup_mul by auto.
    eapply items_valid_app3; eauto.
  Qed.
  Proof.
    unfold read_all.
    step.
    rewrite synced_array_is, Nat.add_0_r; cancel.
    simplen.

    step; subst.
    rewrite map_fst_combine by simplen.
    rewrite firstn_oob by simplen.
    eapply iunpack_ipack; eauto.
  Qed.
  Proof.
    intros.
    unfold vsupd_range, unsync_array, rep_common, ipack.
    cancel.
    apply arrayN_unify.
    rewrite skipn_oob.
    rewrite app_nil_r.
    f_equal.
    simplen.
    simplen.
  Qed.
  Proof.
    unfold vsupd_range, unsync_array, rep_common, eqlen.
    intros.
    rewrite nopad_ipack_length in *.
    rewrite firstn_oob by omega.
    rewrite skipn_oob by omega.
    cancel.
    apply arrayN_unify.
    rewrite app_nil_r.
    f_equal.
    auto using ipack_nopad_ipack_eq.
    autorewrite with core list. auto.
  Qed.
  Proof.
    intros; autorewrite with lists in *.
    erewrite <- list_chunk_length; eauto.
  Qed.
  Proof.
    unfold write_aligned, avail_rep.
    step.
    cbn. simplen.
    step.
    apply vsupd_range_nopad_unsync_array; auto.
    xcrash.
    rewrite vsupd_range_length; auto.
    simplen.
    setoid_rewrite nopad_list_chunk_length; auto.
  Qed.
  Proof.
    unfold synced_array, rep_common; cancel; simplen.
    unfold vssync_range.
    rewrite skipn_oob by simplen.
    rewrite app_nil_r.
    apply arrayN_unify.
    rewrite firstn_oob by simplen.
    rewrite map_fst_combine by simplen.
    auto.
  Qed.
  Proof.
    intros.
    replace (length vsl) with (length (ipack items)) by simplen.
    rewrite ipack_length; simplen.
  Qed.
  Proof.
    intros; apply eq_sym; eapply helper_ipack_length_eq; eauto.
  Qed.
  Proof.
    intros.
    unfold vssync_range, ipack.
    apply arrayN_unify.
    rewrite skipn_combine by simplen.
    rewrite <- combine_app.
    f_equal.
    rewrite <- firstn_map_comm.
    rewrite map_fst_combine by simplen.
    rewrite firstn_skipn; auto.
    simplen.
    lia.
  Qed.
  Proof.
    unfold sync_aligned.
    prestep. norml.
    unfold unsync_array, rep_common in *; destruct_lifts.

    cancel.
    rewrite combine_length_eq by simplen.
    rewrite ipack_length; simplen.

    step.
    apply vssync_range_sync_array; eauto.
  Qed.