    Proof.
      unfold items_per_val; simpl.
      rewrite valulen_is.
      cbv; auto.
    Qed.
    Proof.
      unfold items_per_val; simpl.
      rewrite valulen_is.
      cbv; auto.
    Qed.
    Proof.
      rewrite valulen_is. apply leb_complete. compute. trivial.
    Qed.
    Proof.
      apply le_plus_minus_r; auto.
    Qed.
    Proof.
      unfold val2hdr, hdr2val.
      unfold eq_rec_r, eq_rec.
      intros.
      rewrite <- plus_minus_header.
      unfold zext.
      autorewrite with core; auto.
      simpl; destruct h; tauto.
    Qed.
    Proof.
      unfold rep; intros; simpl.
      xform; auto.
    Qed.
    Proof.
      unfold rep; intros; simpl.
      xform; cancel.
      or_l; cancel.
      or_r; cancel.
    Qed.
    Proof.
      unfold write.
      hoare.
      xcrash.
    Qed.
    Proof.
      unfold read.
      hoare.
      subst; rewrite val2hdr2val; simpl.
      unfold mk_header, Rec.recget'; simpl.
      repeat rewrite wordToNat_natToWord_idempotent'; auto.
      destruct n; auto.
    Qed.
    Proof.
      unfold sync.
      hoare.
      xcrash.
   Qed.
  Proof.
    intros; rewrite Forall_forall; auto.
  Qed.
  Proof.
    unfold vals_nonzero.
    induction l; intros; simpl; auto.
    destruct a, n; simpl.
    case_eq (map ent_valu (log_nonzero l)); intros; simpl.
    apply map_eq_nil in H; auto.
    rewrite <- H; auto.
    rewrite IHl; auto.
  Qed.
  Proof.
    induction a; intros; simpl; auto.
    destruct a; simpl; auto.
  Qed.
  Proof.
    induction a; intros; simpl; auto.
    destruct b; auto.
    destruct a, b; simpl; auto.
    rewrite IHa; auto.
  Qed.
  Proof.
    induction n; intros; simpl.
    rewrite app_nil_r; auto.
    rewrite <- cons_nil_app.
    rewrite IHn.
    apply combine_nonzero_app_zero.
  Qed.
  Proof.
    unfold padded_addr, vals_nonzero.
    induction a; intros; simpl; auto.
    unfold setlen, roundup; simpl.
    rewrite divup_0; simpl; auto.

    unfold setlen, roundup; simpl.
    destruct a, b; simpl; auto;
    rewrite firstn_oob; simpl; auto;
    rewrite combine_nonzero_app_zeros; auto.
  Qed.
  Proof.
    induction n; intros; simpl; auto.
    rewrite IHn; auto.
  Qed.
  Proof.
    induction n; intros; simpl; auto.
    rewrite IHn; auto.
  Qed.
  Proof.
    unfold padded_log, setlen, roundup; intros.
    induction l; simpl.
    rewrite divup_0; simpl; auto.
    
    rewrite <- IHl.
    destruct a, b, n; simpl; auto;
    repeat rewrite firstn_oob; simpl; auto;
    repeat rewrite map_app;
    setoid_rewrite map_fst_repeat;
    repeat rewrite combine_nonzero_app_zeros; auto.
  Qed.
  Proof.
    unfold padded_log, setlen, roundup; intros.
    rewrite firstn_oob; simpl; auto.
    apply Forall_append; auto.
    rewrite Forall_forall; intros.
    apply repeat_spec in H0; subst.
    unfold addr_valid; simpl.
    apply zero_lt_pow2.
  Qed.
  Proof.
    unfold padded_log, setlen; intros.
    rewrite firstn_oob in H; auto.
    eapply forall_app_r; eauto.
  Qed.
  Proof.
    unfold ent_addr, addr2w.
    induction l; intros; simpl; auto.
    rewrite IHl; f_equal.
    rewrite wordToNat_natToWord_idempotent'; auto.
    apply Forall_inv in H; unfold addr_valid in H; auto.
    eapply Forall_cons2; eauto.
  Qed.
  Proof.
    intros; unfold ent_addr, addr2w.
    rewrite <- combine_nonzero_ok.
    rewrite <- combine_nonzero_padded_log.
    f_equal.
    rewrite map_wordToNat_ent_addr; auto.
  Qed.
  Proof.
    induction l; intros; simpl; auto.
    destruct a, n; simpl; auto.
  Qed.
  Proof.
    induction l; intros; simpl; auto.
    destruct a, n; simpl; auto.
  Qed.
  Proof.
    unfold padded_log, setlen; intros.
    rewrite firstn_oob, map_app, map_entaddr_repeat_0 by auto.
    rewrite DescDefs.ipack_app_item0; auto.
    rewrite map_length; auto.
  Qed.
  Proof.
     unfold Desc.array_rep, Desc.synced_array, Desc.rep_common; intros.
     split; cancel; subst.
     unfold padded_log, setlen, roundup in H0.
     rewrite firstn_oob, map_app in H0 by auto.
     apply Desc.items_valid_app in H0; intuition.
     apply eq_sym; apply desc_ipack_padded.
     unfold padded_log, setlen, roundup.
     rewrite firstn_oob, map_app by auto.
     apply Desc.items_valid_app2; auto.
     autorewrite with lists; auto.
     apply desc_ipack_padded.
  Qed.
  Proof.
     unfold Desc.array_rep, Desc.unsync_array, Desc.rep_common; intros.
     split; cancel; subst.
     unfold padded_log, setlen, roundup in H.
     rewrite firstn_oob, map_app in H by auto.
     apply Desc.items_valid_app in H; intuition.
     apply eq_sym; apply desc_ipack_padded.
     unfold padded_log, setlen, roundup.
     rewrite firstn_oob, map_app by auto.
     apply Desc.items_valid_app2; auto.
     autorewrite with lists; auto.
     apply desc_ipack_padded.
  Qed.
  Proof.
    intros; unfold ndesc_log.
    eapply goodSize_trans; [ apply divup_le | eauto ].
    destruct (mult_O_le (length l) DescSig.items_per_val); auto.
    contradict H0; apply DescDefs.items_per_val_not_0.
  Qed.
  Proof.
    unfold padded_log, roundup; intros.
    rewrite setlen_length; auto.
  Qed.
  Proof.
    induction a; intros; simpl; auto.
    destruct a; simpl; auto.
  Qed.
  Proof.
    induction n; intros; simpl.
    rewrite app_nil_r; auto.
    rewrite <- cons_nil_app.
    rewrite IHn.
    apply nonzero_addrs_app_zero.
  Qed.
  Proof.
    unfold padded_log; induction l; simpl; auto.
    rewrite setlen_nil, repeat_is_nil; simpl; auto.
    unfold roundup; rewrite divup_0; omega.
    
    destruct a, n; simpl;
    rewrite <- IHl;
    unfold setlen, roundup;
    repeat rewrite firstn_oob, map_app by auto;
    setoid_rewrite map_fst_repeat;
    repeat rewrite nonzero_addrs_app_zeros; simpl; auto.
  Qed.
  Proof.
    unfold vals_nonzero; induction l; intros; simpl; auto.
    destruct a, n; simpl; auto.
    autorewrite with lists in *; omega.
  Qed.
  Proof.
    unfold ndata_log; intros.
    rewrite <- vals_nonzero_addrs.
    eapply goodSize_trans.
    apply vals_nonzero_length; auto.
    auto.
  Qed.
  Proof.
    unfold avail.
    safestep.
    safestep.
    cancel.
  Qed.
  Proof.
    unfold read.
    safestep.
    prestep. norm. cancel. intuition simpl.
    eassign (map ent_addr (padded_log l)).
    rewrite map_length, padded_log_length.
    auto. auto.
    pred_apply.
    rewrite desc_padding_synced_piff; cancel.

    safestep.
    setoid_rewrite vals_nonzero_addrs; unfold ndata_log.
    replace DataSig.items_per_val with 1 by (cbv; auto); omega.

    safestep.
    rewrite desc_padding_synced_piff; cancel.
    replace (map ent_valu (log_nonzero l)) with (vals_nonzero l); auto.

    all: cancel.
    rewrite desc_padding_synced_piff; cancel.
  Qed.
  Proof.
    unfold goodSize; intros.
    apply zero_lt_pow2.
  Qed.
  Proof.
    unfold ndesc_log; simpl.
    rewrite divup_0; auto.
  Qed.
  Proof.
    unfold ndata_log; simpl; auto.
  Qed.
  Proof.
    intros; cancel.
  Qed.
  Proof.
    intros; omega.
  Qed.
  Proof.
    intros.
    unfold ndesc_log, vals_nonzero; simpl; rewrite divup_0.
    rewrite Desc.array_rep_sync_nil_sep_star, Data.array_rep_sync_nil_sep_star; auto.
    cancel.
    unfold ndata_log; simpl; repeat rewrite Nat.sub_0_r.
    rewrite <- log_nonzero_addrs.
    rewrite Data.array_rep_size_ok_pimpl, Desc.array_rep_size_ok_pimpl.
    rewrite Data.array_rep_avail, Desc.array_rep_avail.
    simpl; rewrite divup_1; autorewrite with lists.
    cancel.
    rewrite helper_sep_star_reorder.
    rewrite Desc.avail_rep_merge by auto.
    rewrite Data.avail_rep_merge by auto.
    repeat rewrite helper_add_sub_0 by auto.
    cancel.
  Qed.
  Proof.
    unfold trunc.
    step.
    step.
    step.
    cancel_by helper_trunc_ok.

    (* crash conditions *)
    xcrash.
    xcrash.
  Qed.
  Proof.
    unfold loglen_valid, loglen_invalid.
    destruct (lt_dec (LogDescLen xp) ndesc);
    destruct (lt_dec (LogLen xp) ndata); simpl; auto.
    left; intuition.
  Defined.
  Proof.
    unfold ndata_log; induction l; rewrite Forall_forall; intuition.
    destruct a, n; simpl.
    exfalso; intuition.
    apply (H (0, w)); simpl; auto.
    rewrite IHl; auto.
    rewrite Forall_forall; intros.
    apply H; simpl; intuition.
  Qed.
  Proof.
    unfold Desc.items_valid, loglen_valid.
    intuition.
    unfold DescSig.RALen; omega.
    autorewrite with lists; unfold DescSig.RALen.
    apply divup_ge; auto.
    unfold ndesc_log in *; omega.
  Qed.
  Proof.
    unfold Data.items_valid, loglen_valid.
    intuition.
    unfold DataSig.RALen; omega.
    autorewrite with lists; unfold DataSig.RALen.
    apply divup_ge; auto.
    rewrite divup_1; rewrite <- entry_valid_ndata by auto.
    unfold ndata_log in *; omega.
  Qed.
  Proof.
    unfold loglen_valid, ndesc_log; intros.
    omega.
  Qed.
  Proof.
    unfold loglen_valid, ndata_log; intros.
    omega.
  Qed.
  Proof.
    intros.
    rewrite <- entry_valid_ndata by auto.
    apply helper_loglen_data_valid_extend; auto.
  Qed.
  Proof.
    unfold Desc.items_valid; intuition.
    autorewrite with lists in *.
    rewrite padded_log_length; unfold roundup.
    apply Nat.mul_le_mono_pos_r.
    apply DescDefs.items_per_val_gt_0.
    apply divup_le; lia.
  Qed.
  Proof.
    intros; rewrite Nat.mul_comm.
    destruct (mult_O_le a b); auto; omega.
  Qed.
  Proof.
    unfold loglen_valid, DescSig.xparams_ok, DataSig.xparams_ok; intuition.
    eapply goodSize_trans.
    eapply le_trans. eauto.
    apply le_plus_r. eauto.
  Qed.
  Proof.
    unfold loglen_valid, DescSig.xparams_ok, DataSig.xparams_ok; intuition.
    eapply goodSize_trans.
    eapply le_trans. eauto.
    apply le_plus_r. eauto.
  Qed.
  Proof.
    intros; rewrite Forall_forall in *; intros.
    apply H; auto.
  Qed.
  Proof.
    intros; omega.
  Qed.
  Proof.
    induction a; intros; simpl; auto.
    destruct a; auto.
    rewrite IHa; omega.
  Qed.
  Proof.
    unfold ndata_log;  intros.
    repeat rewrite map_app.
    rewrite nonzero_addrs_app; auto.
  Qed.
  Proof.
    unfold ndesc_log; intros.
    rewrite padded_log_length.
    unfold roundup; rewrite divup_divup; auto.
  Qed.
  Proof.
    unfold ndesc_log; intros.
    rewrite app_length, H at 1.
    unfold roundup.
    rewrite Nat.add_comm, Nat.mul_comm.
    rewrite divup_add by auto.
    omega.
  Qed.
  Proof.
    intros.
    rewrite ndesc_log_app.
    rewrite ndesc_log_padded_log; auto.
    rewrite padded_log_length.
    rewrite roundup_roundup; auto.
  Qed.
  Proof.
    unfold ndata_log, padded_log, setlen, roundup; intros.
    rewrite firstn_oob by auto.
    repeat rewrite map_app.
    rewrite repeat_map; simpl.
    rewrite nonzero_addrs_app.
    setoid_rewrite <- app_nil_l at 3.
    rewrite nonzero_addrs_app_zeros; auto.
  Qed.
  Proof.
    intros.
    rewrite ndata_log_app.
    rewrite ndata_log_padded_log; auto.
  Qed.
  Proof.
    unfold vals_nonzero; induction a; intros; simpl; auto.
    destruct a, n; simpl; auto.
    rewrite IHa; auto.
  Qed.
  Proof.
    induction n; simpl; auto.
  Qed.
  Proof.
    induction a; simpl; intros; auto.
    destruct a, n; simpl; auto.
    rewrite IHa; auto.
  Qed.
  Proof.
    unfold vals_nonzero, padded_log, setlen, roundup; simpl.
    induction l; intros; simpl; auto.
    rewrite firstn_oob; simpl; auto.
    rewrite log_nonzero_repeat_0; auto.

    destruct a, n.
    rewrite <- IHl.
    repeat rewrite firstn_oob; simpl; auto.
    repeat rewrite log_nonzero_app, map_app.
    repeat rewrite log_nonzero_repeat_0; auto.

    repeat rewrite firstn_oob; simpl; auto.
    f_equal.
    repeat rewrite log_nonzero_app, map_app.
    repeat rewrite log_nonzero_repeat_0; auto.
    simpl; rewrite app_nil_r; auto.
  Qed.
  Proof.
    unfold entry_valid; induction l; simpl; auto.
    destruct a, n; simpl; auto; intros.
    exfalso.
    rewrite Forall_forall in H; intuition.
    apply (H (0, w)); simpl; auto.
    rewrite IHl; auto.
    eapply Forall_cons2; eauto.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    destruct a, n; simpl.
    exfalso.
    rewrite Forall_forall in H.
    apply (H (0, w)); simpl; auto.
    rewrite IHl; auto.
    eapply Forall_cons2; eauto.
  Qed.
  Proof.
    intros.
    repeat rewrite ndesc_log_padded_app, ndata_log_padded_app.
    setoid_rewrite Nat.sub_add_distr.
    unfold ndesc_log.
    rewrite divup_1.
    rewrite entry_valid_ndata with (l := new); auto.
    repeat rewrite map_length.
    rewrite map_app, vals_nonzero_app.
    rewrite <- Desc.array_rep_synced_app.
    rewrite <- Data.array_rep_synced_app.
    repeat rewrite Nat.add_0_l.
    repeat rewrite desc_padding_synced_piff.
    repeat rewrite map_length.
    repeat rewrite vals_nonzero_padded_log.
    rewrite divup_1, padded_log_length.
    unfold roundup; rewrite divup_mul; auto.
    unfold ndata_log; rewrite vals_nonzero_addrs.
    unfold vals_nonzero; rewrite entry_valid_vals_nonzero with (l := new); auto.
    cancel.

    rewrite Nat.mul_1_r; auto.
    rewrite map_length, padded_log_length.
    unfold roundup; auto.
  Qed.
  Proof.
    induction l; simpl; auto.
    destruct a; omega.
  Qed.
  Proof.
    intros.
    rewrite ndesc_log_padded_app, ndata_log_padded_app; auto.
  Qed.
  Proof.
    intros.
    eapply le_trans.
    apply nonzero_addrs_bound.
    rewrite map_length.
    apply roundup_ge; auto.
  Qed.
  Proof.
    unfold loglen_invalid, ndesc_log, ndata_log; intros.
    rewrite app_length; repeat rewrite padded_log_length.
    unfold roundup; intuition.
    rewrite H.
    setoid_rewrite <- Nat.mul_comm at 2.
    apply divup_add_gt; auto.

    eapply lt_le_trans; eauto.
    apply Nat.add_le_mono.
    apply nonzero_addrs_roundup; auto.
    erewrite <- map_length.
    apply nonzero_addrs_bound.
  Qed.
  Proof.
    unfold extend.
    step.
    step.

    (* true case *)
    - (* write content *)
      safestep.
      rewrite Desc.avail_rep_split. cancel.
      autorewrite with lists; apply helper_loglen_desc_valid_extend; auto.

      safestep.
      unfold loglen_valid in *; unfold Data.items_valid; intuition.
      unfold DataSig.RALen; omega.
      autorewrite with lists.
      rewrite <- entry_valid_ndata by auto.
      replace DataSig.items_per_val with 1 by (cbv; auto).
      unfold DataSig.RALen; omega.
      rewrite Data.avail_rep_split. cancel.
      autorewrite with lists.
      rewrite divup_1; rewrite <- entry_valid_ndata by auto.
      apply helper_loglen_data_valid_extend; auto.

      (* sync content *)
      prestep. norm. cancel. intuition simpl.
      instantiate ( 1 := map ent_addr (padded_log new) ).
      rewrite map_length, padded_log_length; auto.
      apply padded_desc_valid.
      apply loglen_valid_desc_valid; auto.
      rewrite desc_padding_unsync_piff.
      pred_apply; cancel.

      safestep.
      autorewrite with lists.
      rewrite entry_valid_ndata, Nat.mul_1_r; auto.
      unfold loglen_valid in *; unfold Data.items_valid; intuition.
      unfold DataSig.RALen; omega.
      autorewrite with lists.
      rewrite <- entry_valid_ndata by auto.
      replace DataSig.items_per_val with 1 by (cbv; auto).
      unfold DataSig.RALen; omega.

      (* write header *)
      safestep.
      eapply loglen_valid_goodSize_l; eauto.
      eapply loglen_valid_goodSize_r; eauto.

      (* sync header *)
      safestep.

      (* post condition *)
      safestep.
      or_l; cancel.
      cancel_by extend_ok_helper; auto.

      (* crashes *)
      (* after header write : Extended *)
      rewrite ndesc_log_app, ndata_log_app.
      rewrite ndesc_log_padded_log, ndata_log_padded_log.
      eauto.
      rewrite padded_log_length, roundup_roundup; auto.
      xcrash.
      or_r; cancel.
      cancel_by extend_ok_helper; auto.

      (* after header sync : Synced new *)
      xcrash.
      or_r; cancel.
      cancel_by extend_ok_helper; auto.

      (* before header write : ExtendedUnsync *)
      xcrash.
      or_l; cancel.
      extend_crash.

      xcrash.
      or_l; cancel.
      extend_crash.

      xcrash.
      or_l; cancel.
      extend_crash.

      (* before write desc : Synced old *)
      xcrash.
      or_l; cancel.
      rewrite Desc.avail_rep_merge. cancel.
      rewrite map_length.
      apply helper_loglen_desc_valid_extend; auto.

    (* false case *)
    - step.
      or_r; cancel.
      apply loglen_invalid_overflow; auto.

    (* crash for the false case *)
    - cancel.
      xcrash.
      or_l; cancel.
  Qed.
  Proof.
    unfold padded_log, setlen, roundup; intros.
    rewrite firstn_oob by auto.
    rewrite log_nonzero_app.
    rewrite log_nonzero_repeat_0, app_nil_r; auto.
  Qed.
  Proof.
    intros.
    rewrite log_nonzero_app.
    repeat rewrite log_nonzero_padded_log.
    f_equal.
    rewrite entry_valid_vals_nonzero; auto.
  Qed.
  Proof.
    intros.
    rewrite log_nonzero_app, log_nonzero_padded_log.
    f_equal.
    rewrite entry_valid_vals_nonzero; auto.
  Qed.
  Proof.
    unfold rep, rep_inner, rep_contents, xparams_ok.
    unfold Desc.array_rep, Desc.synced_array, Desc.rep_common, Desc.items_valid.
    intros; destruct_lifts.
    rewrite map_length, Nat.sub_0_r in *.
    rewrite H5, Nat.mul_comm; auto.
  Qed.
  Proof.
    unfold rep; simpl; unfold rep_contents; intros.
    xform; cancel.
    rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
    rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
    rewrite Hdr.xform_rep_synced.
    cancel.
  Qed.
  Proof.
    unfold rep; simpl; unfold rep_contents; intros.
    xform; cancel.
    rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
    rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
    rewrite Hdr.xform_rep_unsync.
    norm; auto.

    or_r; cancel.
    cancel_by helper_trunc_ok.
    or_l; cancel.
  Qed.
  Proof.
    unfold rep; simpl; unfold rep_contents; intros.
    xform; cancel.

    rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
    rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
    rewrite Hdr.xform_rep_synced.
    cancel.
  Qed.
  Proof.
    unfold rep, rep_inner, rep_contents, xparams_ok.
    unfold Desc.array_rep, Desc.synced_array, Desc.rep_common, Desc.items_valid.
    intros; destruct_lifts.
    rewrite map_length, Nat.sub_0_r in *.
    unfold ndata_log, ndesc_log; split; auto; split.

    rewrite H4, Nat.mul_comm.
    eapply le_trans; [ | eauto ].
    rewrite app_length, nonzero_addrs_entry_valid with (l := new) by auto.
    apply plus_le_compat_r.
    eapply le_trans.
    apply nonzero_addrs_bound.
    rewrite padded_log_length, map_length.
    apply roundup_ge; auto.

    eapply Nat.mul_le_mono_pos_r with (p := DescSig.items_per_val).
    apply DescDefs.items_per_val_gt_0.
    rewrite app_length, padded_log_length in H16.
    apply roundup_le in H16.
    rewrite roundup_roundup_add in H16 by auto.
    rewrite Nat.mul_add_distr_r.
    eapply le_trans; eauto.
  Qed.
  Proof.
    unfold pimpl; intros.
    pose proof rep_extended_facts' H.
    pred_apply; cancel.
  Qed.
  Proof.
    intros; cancel.
  Qed.
  Proof.
    intros; omega.
  Qed.
  Proof.
    intros.
    rewrite map_app, vals_nonzero_app.
    rewrite ndesc_log_padded_app, ndata_log_padded_app.
    rewrite Desc.array_rep_synced_app_rev, Data.array_rep_synced_app_rev.
    repeat rewrite Nat.add_0_l.
    rewrite map_length, vals_nonzero_padded_log, padded_log_length.
    setoid_rewrite desc_padding_synced_piff.
    cancel.

    rewrite Data.array_rep_avail, Desc.array_rep_avail; simpl.
    unfold roundup; rewrite divup_divup by auto.
    setoid_rewrite vals_nonzero_addrs.
    setoid_rewrite divup_1.
    setoid_rewrite map_length.
    unfold ndata_log, ndesc_log.
    rewrite helper_sep_star_distr.
    rewrite Desc.avail_rep_merge, Data.avail_rep_merge.
    cancel.
    apply helper_add_sub_add; auto.
    apply helper_add_sub_add; auto.

    rewrite Nat.mul_1_r; auto.
    rewrite map_length, padded_log_length.
    unfold roundup; auto.
  Qed.
  Proof.
    intros; rewrite rep_extended_facts.
    unfold rep; simpl; unfold rep_contents; intros.
    xform; cancel.

    rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
    rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
    rewrite Hdr.xform_rep_unsync.
    norm; auto.

    or_r; cancel.
    rewrite extend_ok_synced_hdr_helper; auto.

    or_l; cancel.
    apply xform_rep_extended_helper; auto.

    apply padded_addr_valid.
    eapply forall_app_r; eauto.
  Qed.
  Proof.
    unfold rep; simpl; intros; unfold rep_contents; cancel.
    setoid_rewrite ndesc_log_padded_app.
    setoid_rewrite ndata_log_padded_app.
    rewrite ndesc_log_padded_log, ndata_log_padded_log.
    setoid_rewrite map_app.
    setoid_rewrite vals_nonzero_app.
    setoid_rewrite vals_nonzero_padded_log.
    cancel.

    rewrite Desc.array_rep_synced_app_rev.
    setoid_rewrite <- desc_padding_synced_piff at 2.
    eapply pimpl_trans2.
    eapply Desc.array_rep_synced_app.
    rewrite map_length, padded_log_length; unfold roundup; eauto.
    cancel.
    rewrite map_length, padded_log_length; unfold roundup; eauto.
    apply Forall_append.
    eapply forall_app_r; eauto.
    eapply forall_app_l in H2.
    apply addr_valid_padded; auto.
  Qed.
  Proof.
    unfold read.
    hoare.
  Qed.
  Proof.
    unfold trunc.
    hoare.
    unfold roundup; rewrite divup_0; omega.

    (* crashes *)
    xcrash.
  Qed.
  Proof.
    unfold avail.
    step.
    step.
  Qed.
  Proof.
    intros.
    repeat rewrite app_length.
    repeat rewrite PaddedLog.padded_log_length.
    rewrite H.
    rewrite roundup_roundup_add, roundup_roundup; auto.
  Qed.
  Proof.
    intros.
    apply extend_length_ok'.
    rewrite PaddedLog.padded_log_length.
    rewrite roundup_roundup; auto.
  Qed.
  Proof.
    intros.
    rewrite app_length in H0.
    pose proof (PaddedLog.rep_synced_length_ok H1).
    generalize H2.
    rewrite H.
    rewrite <- PaddedLog.padded_log_length.
    intro; omega.
  Qed.
  Proof.
    unfold rounded; intros.
    rewrite extend_length_ok by auto.
    rewrite app_length.
    rewrite H.
    repeat rewrite PaddedLog.padded_log_length.
    rewrite roundup_roundup_add by auto.
    rewrite roundup_roundup by auto.
    omega.
  Qed.
  Proof.
    unfold extend.

    safestep.
    eassign dummy; cancel.
    safestep.

    or_l; norm; [ cancel | intuition; pred_apply; norm ].
    eassign (PaddedLog.padded_log dummy ++ PaddedLog.padded_log new).
    cancel; auto.
    intuition.
    or_r; cancel; eauto.

    xcrash.
    or_l; cancel.
    or_r; cancel.
  Qed.
  Proof.
    unfold rep, rep_common; cancel; eauto.
  Qed.
  Proof.
    unfold rep, rep_common; cancel; eauto.
  Qed.
  Proof.
    unfold rep, rep_common; intros.
    xform; cancel.
    apply PaddedLog.xform_rep_synced.
    all: auto.
  Qed.
  Proof.
    unfold rep, rep_common; intros.
    xform; cancel.
    rewrite PaddedLog.xform_rep_truncated.
    cancel.
    or_r; cancel.
    rewrite roundup_0; auto.
  Qed.
  Proof.
    unfold rep, rep_common; intros.
    xform; cancel.
    apply PaddedLog.xform_rep_extended_unsync.
    all: auto.
  Qed.
  Proof.
    unfold rep, rep_common; intros.
    xform.
    rewrite PaddedLog.rep_extended_facts.
    xform; cancel.
    rewrite PaddedLog.xform_rep_extended.
    cancel.
    or_r; norm.
    instantiate (1 := (PaddedLog.padded_log x ++ PaddedLog.padded_log new)).
    cancel; auto.
    intuition.
  Qed.