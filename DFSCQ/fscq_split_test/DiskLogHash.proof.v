    Proof.
      unfold items_per_val; simpl.
      rewrite valulen_is. apply Nat.eqb_eq. compute. reflexivity.
    Qed.
    Proof.
      unfold items_per_val; simpl.
      rewrite valulen_is. apply Nat.eqb_eq. compute; reflexivity.
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
      rewrite crash_xform_ptsto_subset'.
      cancel.
      rewrite H1; auto.
    Qed.
    Proof.
      unfold rep; intros; simpl.
      xform.
      rewrite crash_xform_ptsto_subset; unfold ptsto_subset.
      cancel.
      or_l; cancel.
      cancel.
    Qed.
    Proof.
      unfold write.
      step.
      step.
      xcrash.
      step.
      xcrash.
    Qed.
    Proof.
      unfold read.
      hoare.
      subst; rewrite val2hdr2val; simpl.
      unfold hdr_goodSize in *; intuition.
      repeat rewrite wordToNat_natToWord_idempotent'; auto.
      destruct n; auto.
      destruct p as (p1 , p2); destruct p1, p2, p0; auto.
    Qed.
    Proof.
      unfold sync.
      step.
      step.
    Qed.
    Proof.
      unfold sync_now; intros.
      hoare.
    Qed.
    Proof.
      unfold init, rep; intros.
      step.
      step.
      step.
      step.
      step.
      prestep; unfold rep; safecancel.
      unfold hdr_goodSize; cbn.
      repeat split; apply zero_lt_pow2.
      all: apply pimpl_any.
      Unshelve. exact tt.
    Qed.
    Proof.
      unfold rep; destruct st; eauto.
    Qed.
  Proof.
    unfold rep, rep_inner, rep_contents, rep_contents_unmatched.
    destruct st; intros; eauto 50.
  Qed.
  Proof.
    unfold would_recover'; intros; eauto.
  Qed.
  Proof.
    unfold would_recover; intros; eauto.
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
    unfold ndata_log; intros.
    rewrite <- vals_nonzero_addrs.
    eapply goodSize_trans.
    apply vals_nonzero_length; auto.
    auto.
  Qed.
  Proof.
    intros.
    unfold padded_log.
    rewrite setlen_length.
    rewrite roundup_roundup; auto.
    rewrite setlen_exact; auto.
    rewrite setlen_length; auto.
  Qed.
  Proof.
    intros.
    unfold padded_log.
    rewrite setlen_app_r.
    f_equal.
    rewrite app_length, setlen_length.
    rewrite roundup_roundup_add; auto.
    f_equal; omega.
    rewrite app_length, setlen_length.
    rewrite roundup_roundup_add; auto.
    omega.
  Qed.
  Proof.
    unfold avail.
    safestep.
    safestep.
    solve_checksums.
    cancel.
    solve_checksums.
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

    safestep; subst.
    setoid_rewrite vals_nonzero_addrs; unfold ndata_log.
    replace DataSig.items_per_val with 1 by (cbv; auto); try omega.
    replace (map ent_valu (log_nonzero l)) with (vals_nonzero l); auto.
    safestep.
    rewrite desc_padding_synced_piff; cancel.
    solve_checksums.

    pimpl_crash; cancel.
    rewrite desc_padding_synced_piff; cancel.
    solve_checksums.

    cancel.
    solve_checksums.
    cancel.
    solve_checksums.
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
    unfold init, initrep.
    prestep; unfold rep, Hdr.LAHdr; safecancel.
    auto.
    step.
    unfold ndesc_log, ndata_log; rewrite divup_0; simpl; cancel.
    repeat rewrite Nat.sub_0_r; cbn; cancel.
    rewrite Desc.array_rep_sync_nil, Data.array_rep_sync_nil by (auto; omega); cancel.
    solve_checksums; simpl; auto.
    setoid_rewrite DescDefs.ipack_nil; simpl.
    solve_hash_list_rep; auto.
  Qed.
  Proof.
    intros.
    eapply pimpl_ok2. apply init_ok'.
    intros; unfold initrep; safecancel.
    unfold Desc.avail_rep, Data.avail_rep.
    rewrite arrayN_isolate_hd by omega.
    repeat rewrite Nat.add_0_r.
    rewrite arrayN_split with (i := LogDescLen xp).
    rewrite surjective_pairing with (p := selN l 0 ($0, nil)).
    substl (LogData xp); substl (LogDescriptor xp).
    cancel.
    rewrite firstn_length_l; auto.
    setoid_rewrite skipn_length with (n := 1); omega.
    setoid_rewrite skipn_skipn with (m := 1).
    rewrite skipn_length; omega.
    auto.
    step.
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
    rewrite !le_plus_minus_r by auto.
    cancel.
  Qed.
  Proof.
    unfold trunc.
    step.
    step.
    step.

    unfold Hdr.rep in H0.
    destruct_lift H0.
    unfold Hdr.hdr_goodSize in *; intuition.

    step.
    step.

    (* post condition *)
    cancel_by helper_trunc_ok.
    solve_checksums.
    replace (DescDefs.ipack (map ent_addr [])) with (@nil valu).
    solve_hash_list_rep; auto.
    symmetry. apply DescDefs.ipack_nil.
    auto.

    (* crash conditions *)
    repeat xcrash_rewrite.
    xform_norm. cancel. xform_normr; cancel.
    or_r; cancel.
    solve_checksums.
    solve_checksums; auto.
    setoid_rewrite DescDefs.ipack_nil; simpl.
    solve_hash_list_rep; auto.

    repeat xcrash_rewrite.
    xform_norm; cancel. xform_normr; cancel.
    or_r; cancel.
    solve_checksums.
    solve_checksums; auto.
    setoid_rewrite DescDefs.ipack_nil; simpl.
    solve_hash_list_rep; auto.

    xcrash_rewrite.
    xform_normr; cancel.
    or_l; cancel.
    solve_checksums.

    xcrash_rewrite.
    xform_normr; cancel.
    or_l; cancel.
    solve_checksums.

    Unshelve.
    constructor.
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
    induction l; simpl; intros; auto.
    destruct a, n; simpl; auto;
    rewrite log_nonzero_app; simpl.
    rewrite app_nil_r. congruence.
    congruence.
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
    erewrite <- DescDefs.iunpack_ipack; eauto.
    erewrite <- DescDefs.iunpack_ipack at 1; eauto.
    congruence.
  Qed.
  Proof.
    unfold ndesc_log, ndesc_list.
    intros.
    autorewrite with lists.
    rewrite padded_log_length.
    unfold roundup.
    rewrite divup_divup; auto.
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
    intros.
    destruct st; unfold rep, rep_inner; cancel; solve_checksums.
    auto.
  Qed.
  Proof.
    unfold would_recover'.
    intros.
    cancel;
    rewrite rep_hashmap_subset; auto; cancel.
  Qed.
  Proof.
    unfold extend.
    step.
    step.

    (* true case *)
    - (* write content *)
      rewrite <- DescDefs.ipack_nopad_ipack_eq.
      step.
      unfold checksums_match in *; intuition.
      solve_hash_list_rep.
      step.
      unfold checksums_match in *; intuition.
      solve_hash_list_rep.

      safestep.
      rewrite Desc.avail_rep_split. cancel.
      autorewrite with lists; apply helper_loglen_desc_valid_extend; auto.

      safestep.
      rewrite Data.avail_rep_split. cancel.
      autorewrite with lists.
      rewrite divup_1; rewrite <- entry_valid_ndata by auto.
      apply helper_loglen_data_valid_extend; auto.

      (* write header *)
      safestep.
      denote Hdr.rep as Hx; unfold Hdr.rep in Hx.
      destruct_lift Hx.
      unfold Hdr.hdr_goodSize in *; intuition.
      eapply loglen_valid_goodSize_l; eauto.
      eapply loglen_valid_goodSize_r; eauto.

      (* sync content *)
      step.
      eauto 10.
      prestep. norm. cancel. intuition simpl.
      instantiate ( 1 := map ent_addr (padded_log new) ).
      rewrite desc_padding_unsync_piff.
      pred_apply; cancel.
      rewrite map_length, padded_log_length; auto.
      apply padded_desc_valid.
      apply loglen_valid_desc_valid; auto.
      eauto 10.

      safestep.
      autorewrite with lists.
      rewrite entry_valid_ndata, Nat.mul_1_r; auto.
      eauto 10.

      (* sync header *)
      safestep.
      eauto 10.
      step.

      (* post condition *)
      safestep.
      or_l; cancel.
      cancel_by extend_ok_helper; auto.
      solve_checksums.

      (* crash conditons *)
      (* after sync data : Extended *)
      cancel.
      repeat xcrash_rewrite.
      xform_norm. cancel. xform_normr. cancel.
      or_r. cancel.
      extend_crash.
      solve_checksums.
      solve_checksums.

      cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_r. cancel. extend_crash.
      solve_checksums.
      solve_checksums.

      cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_r. cancel. extend_crash.
      solve_checksums.
      solve_checksums.

      cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_r. cancel. extend_crash.
      solve_checksums.
      solve_checksums.

      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_r. cancel. extend_crash.
      solve_checksums.
      solve_checksums.

      cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_r. cancel. extend_crash.
      solve_checksums.
      solve_checksums.


      (* before writes *)
      cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_l; cancel. extend_crash.
      solve_checksums.

      cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel. xform_normr; cancel.
      or_l; cancel.
      rewrite Desc.avail_rep_merge. cancel.
      rewrite map_length.
      apply helper_loglen_desc_valid_extend; auto.
      solve_checksums.

      xcrash.
      or_l; cancel.
      solve_checksums.

      xcrash.
      or_l; cancel.
      solve_checksums.

    (* false case *)
    - safestep.
      or_r; cancel.
      apply loglen_invalid_overflow; auto.
      solve_checksums.

    (* crash for the false case *)
    - xcrash.
      or_l; cancel.
      solve_checksums.
  Qed.
  Proof.
    unfold entry_valid, addr_valid, goodSize; intuition.
    destruct (addr_eq_dec (fst ent) 0); destruct (lt_dec (fst ent) (pow2 addrlen)).
    right; tauto.
    right; tauto.
    left; tauto.
    right; tauto.
  Defined.
  Proof.
    unfold rep, rep_inner, rep_contents, xparams_ok.
    unfold Desc.array_rep, Desc.synced_array, Desc.rep_common, Desc.items_valid.
    intros; destruct_lifts.
    rewrite map_length, Nat.sub_0_r in H17.
    rewrite H5, Nat.mul_comm; auto.
  Qed.
  Proof.
    unfold rep; simpl; unfold rep_contents; intros.
    xform.
    norm'l. unfold stars; cbn.
    xform.
    norm'l. unfold stars; cbn.
    xform.
    rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
    rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
    rewrite Hdr.xform_rep_synced.
    cancel.
  Qed.
  Proof.
    unfold rep; simpl; unfold rep_contents; intros.
    xform; cancel.
    xform; cancel.
    rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
    rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
    rewrite Hdr.xform_rep_unsync.
    norm; auto.

    or_r; cancel.
    cancel_by helper_trunc_ok.
    auto.
    or_l; cancel.
  Qed.
  Proof.
    unfold rep; simpl; unfold rep_contents_unmatched; intros.
    do 4 (xform;
      norm'l; unfold stars; cbn).
    xform.
    rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
    rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
    rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
    rewrite Hdr.xform_rep_synced.
    cancel.
    congruence.
  Qed.
  Proof.
    unfold rep, rep_inner, rep_contents, xparams_ok.
    unfold Desc.array_rep, Desc.synced_array, Desc.rep_common, Desc.items_valid.
    intros; destruct_lifts.
    intuition.
    unfold loglen_valid in *; intuition.
    unfold loglen_valid in *; intuition.
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
    rewrite Data.avail_rep_split with (n1:=ndata_log new).
    rewrite Desc.avail_rep_split with (n1:=ndesc_log new).
    xform.
    erewrite Data.xform_avail_rep_array_rep, Desc.xform_avail_rep_array_rep.
    norml. unfold stars; simpl.
    norm.
    unfold stars; simpl.
    cancel.
    rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
    rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
    unfold rep_contents_unmatched.
    rewrite vals_nonzero_padded_log, desc_padding_synced_piff.
    cancel.
    replace (ndesc_list _) with (ndesc_log new).
    replace (length l) with (ndata_log new).
    cancel.

    replace DataSig.items_per_val with 1 in * by (cbv; auto); try omega.
    unfold ndesc_list.
    substl (length l0).
    unfold ndesc_log.
    rewrite divup_divup; auto.

    replace DataSig.items_per_val with 1 in * by (cbv; auto); try omega.
    intuition; auto.
    all: unfold DescSig.RALen, DataSig.RALen, xparams_ok in *;
          try omega; auto; intuition.

    apply mult_le_compat_r; omega.

    replace DataSig.items_per_val with 1 in * by (cbv; auto); try omega.
  Qed.
  Proof.
    intros.
    cancel; auto.
  Qed.
  Proof.
    intros; rewrite rep_extended_facts.
    unfold rep; simpl; unfold rep_contents; intros.
    xform; cancel.
    xform; cancel.
    rewrite Hdr.xform_rep_unsync; cancel.

    - or_r.
      repeat rewrite sep_star_assoc.
      eapply sep_star_pimpl_trans.
      eapply pimpl_trans.
      2: apply xform_rep_extended_helper; try eassumption.
      cancel.
      cancel.
      subst; auto.

    - or_l.
      cancel.
      rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
      rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
      cancel.
  Qed.
  Proof.
    unfold rep; simpl; intros; unfold rep_contents; cancel.
    repeat rewrite ndesc_log_padded_app.
    repeat rewrite ndata_log_padded_app.
    repeat rewrite ndesc_log_padded_log.
    repeat rewrite ndata_log_padded_log.
    repeat rewrite map_app.
    repeat rewrite vals_nonzero_app.
    repeat rewrite vals_nonzero_padded_log.
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
    apply addr_valid_padded; auto.
    eapply forall_app_l; eauto.
    solve_checksums.
    rewrite <- rev_app_distr.
    erewrite <- DescDefs.ipack_app.
    rewrite <- map_app.
    solve_hash_list_rep.
    rewrite map_length, padded_log_length; unfold roundup; eauto.
    rewrite <- rev_app_distr.
    rewrite vals_nonzero_padded_log.
    rewrite <- vals_nonzero_padded_log.
    rewrite <- vals_nonzero_app.
    solve_hash_list_rep.
  Qed.
  Proof.
    intros.
    unfold rep at 1, rep_inner; simpl.
    norm'l. unfold stars; simpl.
    destruct (list_eq_dec (@weq valulen) (DescDefs.ipack (map ent_addr (padded_log new))) (DescDefs.ipack synced_addr)).
    destruct (list_eq_dec (@weq valulen) (vals_nonzero new) synced_valu).

    - eapply desc_ipack_injective in e.
      unfold rep, rep_inner, rep_contents_unmatched, rep_contents.
      or_l; cancel.
      rewrite map_app.
      rewrite vals_nonzero_app.
      rewrite vals_nonzero_padded_log.
      rewrite <- Data.array_rep_synced_app.
      replace DataSig.items_per_val with 1 by (cbv; auto); try omega.
      rewrite divup_1; simpl.
      repeat rewrite vals_nonzero_addrs.
      rewrite ndata_log_app, ndata_log_padded_log.
      rewrite Nat.sub_add_distr.
      cancel.

      rewrite <- Desc.array_rep_synced_app.
      simpl.
      replace (divup _ _) with (ndesc_log old).
      rewrite ndesc_log_app, ndesc_log_padded_log.
      rewrite Nat.sub_add_distr.
      replace (ndesc_list _) with (ndesc_log new).
      cancel.
      rewrite desc_padding_synced_piff.
      cancel.

      rewrite ndesc_log_ndesc_list; auto.
      rewrite padded_log_length.
      unfold roundup.
      rewrite divup_divup; auto.
      autorewrite with lists.
      rewrite padded_log_length.
      unfold roundup.
      rewrite divup_divup; auto.
      autorewrite with lists.
      rewrite padded_log_length.
      unfold roundup; eauto.
      replace DataSig.items_per_val with 1 by (cbv; auto); try omega.
      rewrite Nat.mul_1_r; eauto.
      auto.
      autorewrite with lists.
      rewrite padded_log_length.
      unfold roundup; eauto.
      eauto.

    - unfold rep, rep_inner.
      or_r; cancel.
      eauto.
      right; auto.

    - unfold rep, rep_inner.
      or_r; cancel.
      eauto.
      left; eauto.
  Qed.
  Proof.
    intros.
    rewrite xform_rep_extended'.
    rewrite rep_extendedcrashed_pimpl.
    auto.
  Qed.
  Proof.
    unfold rep; simpl; unfold rep_contents_unmatched; intros.
    do 6 (xform; norm'l; unfold stars; simpl).
    xform.
    rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
    repeat rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
    rewrite Hdr.xform_rep_synced.
    cancel.
    all: eauto.
  Qed.
  Proof.
    intros.
    rewrite Desc.avail_rep_merge;
    eauto.
    rewrite le_plus_minus_r;
    auto.
    unfold loglen_valid in *;
    omega.
  Qed.
  Proof.
    intros.
    replace DataSig.items_per_val with 1 by (cbv; auto); try omega.
    rewrite divup_1, Data.avail_rep_merge;
    eauto.
    rewrite le_plus_minus_r;
    auto.
    unfold loglen_valid in *;
    omega.
  Qed.
  Proof.
    unfold rep; simpl; unfold rep_contents_unmatched; intros.
    do 7 (xform; norm'l; unfold stars; simpl).
    rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
    repeat rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
    rewrite Hdr.xform_rep_unsync.
    cancel.

    unfold rep_contents.
    or_r.
    rewrite desc_padding_synced_piff, vals_nonzero_padded_log.
    cancel.
    rewrite Desc.array_rep_avail_synced, Data.array_rep_avail_synced.
    rewrite <- recover_desc_avail_helper.
    setoid_rewrite <- recover_data_avail_helper.
    cancel.
    denote (length _ = ndata_log _) as Hndata.
    rewrite Hndata; eauto.
    denote (length _ = _ * _) as Hndesc.
    unfold ndesc_list.
    rewrite Hndesc, divup_mul; eauto.

    Unshelve.
    all: eauto.
  Qed.
  Proof.
    unfold would_recover'.
    intros.
    xform.
    cancel; (rewrite xform_rep_synced ||
              rewrite xform_rep_rollback ||
              rewrite xform_rep_rollbackunsync); cancel.
  Qed.
  Proof.
    intros.
    destruct (weq x y); destruct (weq a b); intuition.
  Defined.
  Proof.
    intros.
    repeat rewrite map_app.
    rewrite Desc.array_rep_synced_app_rev.
    rewrite <- Desc.array_rep_synced_app.
    cancel.
    rewrite desc_padding_synced_piff.
    cancel.
    rewrite map_length, padded_log_length. unfold roundup; eauto.
    rewrite map_length, padded_log_length. unfold roundup; eauto.
  Qed.
  Proof.
    intros.
    rewrite map_app.
    eapply pimpl_trans; [ | eapply Desc.array_rep_synced_app ].
    rewrite Desc.array_rep_synced_app_rev.
    cancel.
    apply desc_padding_synced_piff.
    rewrite map_length, padded_log_length; unfold roundup; eauto.
    rewrite map_length, padded_log_length; unfold roundup; eauto.
  Qed.
  Proof.
    unfold recover.
    step.
    prestep. norm. cancel. intuition simpl.
    eassign (map ent_addr (padded_log l)).
    rewrite map_length, padded_log_length.
    all: auto.
    rewrite desc_padding_synced_piff.
    pred_apply; cancel.

    safestep.
    rewrite vals_nonzero_addrs.
    replace DataSig.items_per_val with 1 by (cbv; auto).
    unfold ndata_log; omega.
    step.

    intros.
    eapply pimpl_ok2; monad_simpl.
    eapply hash_list_ok. cancel.
    solve_hash_list_rep; auto.
    step.
    solve_hash_list_rep; auto.

    step.

    {
      step.
      apply desc_padding_synced_piff.
      solve_checksums.
    }
    {
      eapply pimpl_ok2; monad_simpl; eauto with prog.
      intros.
      unfold pimpl; intros.
      unfold checksums_match in *; intuition.
      rewrite app_nil_r, <- desc_ipack_padded in *.
      denote (_ m) as Hx; destruct_lift Hx; intuition.
      all: denote (_ -> False) as Hx; contradict Hx;
          eapply hash_list_injective2; solve_hash_list_rep.
    }

    all: try cancel;
          solve [ apply desc_padding_synced_piff | solve_checksums ].

    Unshelve. all: eauto; easy.
  Qed.
  Proof.
    unfold recover.
    prestep. norm. cancel.
    denote (length _ = ndata_log _) as Hndata.
    denote (length _ = _ * _) as Hndesc.
    intuition simpl.
    pred_apply; cancel.

    safestep. subst.
    instantiate (1:=(map ent_addr (padded_log old) ++ dummy)).
    autorewrite with lists.
    rewrite Nat.mul_add_distr_r.
    rewrite padded_log_length.
    all: auto.

    unfold rep_contents_unmatched.
    rewrite <- Desc.array_rep_synced_app.
    repeat rewrite desc_padding_synced_piff.
    autorewrite with lists.
    rewrite <- ndesc_log_padded_log.
    unfold ndesc_log; cancel.
    autorewrite with lists.
    rewrite padded_log_length; unfold roundup; eauto.

    prestep. norm. cancel. intuition simpl.
    eassign (vals_nonzero (padded_log old) ++ dummy0).
    autorewrite with lists.
    rewrite vals_nonzero_addrs, nonzero_addrs_padded_log, Nat.mul_add_distr_r.
    unfold ndata_log.
    replace DataSig.items_per_val with 1 by (cbv; auto); try omega.
    repeat rewrite Nat.mul_1_r.
    all: auto.

    rewrite <- Data.array_rep_synced_app.
    pred_apply.
    replace DataSig.items_per_val with 1 by (cbv; auto); try omega.
    rewrite vals_nonzero_addrs, nonzero_addrs_padded_log, divup_1.
    cancel.
    replace DataSig.items_per_val with 1 by (cbv; auto); try omega.
    rewrite Nat.mul_1_r; eauto.

    step.
    intros.
    eapply pimpl_ok2; monad_simpl.
    eapply hash_list_ok.
    cancel.
    solve_hash_list_rep; auto.
    intros.
    eapply pimpl_ok2; monad_simpl.
    eapply hash_list_ok.
    cancel.
    solve_hash_list_rep; auto.
    step.

    (* Impossible case case: the hash could not have matched what was on disk. *)
    {
      prestep. norm'l.
      Transparent hide_or.
      unfold hide_or in *.
      intuition; exfalso;
      denote (False) as Hcontra; apply Hcontra.

      rewrite <- desc_ipack_padded.
      eapply app_inv_head.
      repeat erewrite <- DescDefs.ipack_app.
      erewrite <- map_app.
      eapply rev_injective.
      rewrite app_nil_r in *.
      unfold checksums_match in *; intuition.
      eapply hash_list_injective; [ | solve_hash_list_rep ].
      solve_hash_list_rep.
      (* Not sure why hashmap_subset automation isn't kicking in here. *)
      eapply hashmap_subset_trans; eauto.
      eapply hashmap_subset_trans; eauto.
      eapply hashmap_subset_trans; eauto.
      eapply hashmap_subset_trans; eauto.

      autorewrite with lists.
      rewrite padded_log_length.
      unfold roundup; eauto.
      autorewrite with lists.
      rewrite padded_log_length.
      unfold roundup; eauto.

      eapply app_inv_head.
      erewrite <- vals_nonzero_app.
      eapply rev_injective.
      rewrite app_nil_r in *.
      unfold checksums_match in *; intuition.
      eapply hash_list_injective; [ | solve_hash_list_rep ].
      solve_hash_list_rep.

      Opaque hide_or.
    }

    (* False case: the hash did not match what was on disk and we need to recover. *)
    {
      denote (Data.avail_rep) as Hx; clear Hx.
      denote (Data.avail_rep) as Hx; clear Hx.
      prestep. norm.
      cancel.
      match goal with
      | [ Hor: (_ \/ _ \/ _) |- _ ] => clear Hor
      end.
      intuition simpl.
      instantiate (1:= map ent_addr (padded_log old)).
      rewrite map_length, padded_log_length.
      all: auto.
      pred_apply.
      unfold rep_contents_unmatched.
      cancel.

      safestep.
      rewrite vals_nonzero_padded_log, vals_nonzero_addrs.
      unfold ndata_log.
      replace DataSig.items_per_val with 1 by (cbv; auto); omega.

      step.
      solve_hash_list_rep; eauto.
      eapply pimpl_ok2; monad_simpl; try apply hash_list_ok.
      cancel.
      solve_hash_list_rep; eauto.

      step.
      match goal with
      | [ H: ( _ )%pred d |- _ ]
        => unfold Hdr.rep in H; destruct_lift H
      end.
      unfold Hdr.hdr_goodSize in *; intuition.

      denote (Data.avail_rep) as Hx; clear Hx.
      denote (Data.avail_rep) as Hx; clear Hx.
      step.
      eauto 10.
      step.

      (* post condition: Synced old *)
      rewrite desc_padding_synced_piff, vals_nonzero_padded_log.
      cancel.
      rewrite Desc.array_rep_avail_synced, Data.array_rep_avail_synced.
      rewrite <- recover_desc_avail_helper.
      setoid_rewrite <- recover_data_avail_helper.
      cancel.
      rewrite Hndata; eauto.
      unfold ndesc_list.
      rewrite Hndesc, divup_mul; eauto.
      match goal with
      | [ H: context[rep_contents_unmatched] |- _ ]
        => unfold rep_contents_unmatched in H; destruct_lift H
      end;
      auto.
      rewrite vals_nonzero_padded_log in *.
      solve_checksums.

      (* Crash conditions. *)
      (* After header write, before header sync: RollbackUnsync *)
      xcrash.
      or_r.
      safecancel.
      unfold rep_contents_unmatched.
      rewrite desc_padding_synced_piff, vals_nonzero_padded_log.
      cancel.
      match goal with
      | [ H: context[rep_contents_unmatched] |- _ ]
        => unfold rep_contents_unmatched in H; destruct_lift H
      end;
      auto.
      all: auto.
      rewrite vals_nonzero_padded_log in *.
      solve_checksums.
      solve_checksums.

      xcrash.
      or_r.
      safecancel.
      unfold rep_contents_unmatched.
      rewrite desc_padding_synced_piff, vals_nonzero_padded_log.
      cancel.
      match goal with
      | [ H: context[rep_contents_unmatched] |- _ ]
        => unfold rep_contents_unmatched in H; destruct_lift H
      end;
      auto.
      all: auto.
      rewrite vals_nonzero_padded_log in *.
      solve_checksums.
      solve_checksums.

      (* Before header write: Rollback *)
      norm'l.
      denote (Data.avail_rep) as Hx; clear Hx.
      denote (Data.avail_rep) as Hx; clear Hx.
      xcrash.
      or_l.
      cancel.
      solve_checksums.

      denote (Data.avail_rep) as Hx; clear Hx.
      denote (Data.avail_rep) as Hx; clear Hx.
      xcrash.
      or_l.
      cancel.
      solve_checksums.

      norm'l.
      denote (Data.avail_rep) as Hx; clear Hx.
      xcrash.
      or_l.
      cancel.
      solve_checksums.

      norm'l.
      xcrash.
      or_l.
      cancel.
      solve_checksums.
    }

    (* Rest of the crash conditions. All before header write: Rollback. *)
    all: norm'l.

    denote (Data.avail_rep) as Hx; clear Hx.
    denote (Data.avail_rep) as Hx; clear Hx.
    xcrash.
    or_l.
    cancel.
    solve_checksums.

    denote (Data.avail_rep) as Hx; clear Hx.
    denote (Data.avail_rep) as Hx; clear Hx.
    xcrash.
    or_l.
    cancel.
    solve_checksums.

    denote (Data.avail_rep) as Hx; clear Hx.
    denote (Data.avail_rep) as Hx; clear Hx.
    xcrash.
    or_l.
    cancel.
    solve_checksums.

    denote (Data.avail_rep) as Hx; clear Hx.
    xcrash.
    or_l.
    cancel.
    solve_checksums.

    xcrash.
    or_l.
    cancel.
    solve_checksums.

    xcrash.
    or_l.
    cancel.
    solve_checksums.

    Grab Existential Variables.
    all: eauto; try econstructor.
  Qed.
  Proof.
    unfold would_recover, would_recover'; intros.
    eapply pimpl_ok2; monad_simpl; try eapply nop_ok.
    intros. norm'l. unfold stars; cbn.
    intuition; subst.

    (* Synced *)
    - cancel.
      eapply pimpl_ok2; monad_simpl; try apply recover_ok_Synced.
      cancel.
      eassign l.
      cancel.
      hoare.
      norm'l. xcrash.
      xcrash.
      xcrash.
      or_l; cancel.

    (* Rollback *)
    - cancel.
      eapply pimpl_ok2; monad_simpl; try apply recover_ok_Rollback.
      intros; norm. cancel. intuition simpl. eauto. auto.
      step.
      cancel.
      xcrash.
      or_r; or_l; cancel.
      or_r; or_r; cancel.
      xcrash.
      or_r; or_l; cancel.
  Qed.
  Proof.
    unfold recover, would_recover_either.
    intros.
    eapply pimpl_ok2; eauto with prog.
    intros. norm'l. unfold stars; cbn.

    rewrite crash_xform_exists_comm.
    norm'l. unfold stars; cbn.
    rewrite crash_xform_exists_comm.
    norm'l. unfold stars; cbn.
    rewrite crash_xform_sep_star_dist.
    rewrite crash_xform_lift_empty.
    norm'l. unfold stars; cbn.
    cancel. cancel. eauto.
    eauto.

    step.
    autorewrite with crash_xform. cancel.

    eapply pimpl_ok2; eauto with prog.
    intros. norm'l. unfold stars; cbn.
    cancel.
    rewrite would_recover_either'_hashmap_subset; eauto.

    step.
    or_l. cancel.
    autorewrite with crash_xform. eauto.

    or_r. cancel.
    autorewrite with crash_xform. eauto.

    unfold would_recover_either.
    norm'l; unfold stars; cbn.
    cancel.
    autorewrite with crash_xform; eauto.

    autorewrite with crash_xform; eauto.
    cancel.
    rewrite xform_would_recover_either'.
    rewrite would_recover_either'_hashmap_subset; eauto.

    norm'l; unfold stars; cbn.
    autorewrite with crash_xform.
    rewrite <- H1.
    norm'l. unfold stars; cbn.
    norm'r.
    cancel.
    intuition.


    assert (Hxform: crash_xform (sb_rep fsxp * would_recover_either' (FSXPLog fsxp) old new hm)%pred m').
    unfold crash_xform.
    exists x0; intuition.

    pred_apply.
    autorewrite with crash_xform.
    rewrite xform_would_recover_either'.
    rewrite would_recover_either'_hashmap_subset; eauto.
  Qed.
  Proof.
    unfold forall_helper; intros.
    eexists.

    Require Import Idempotent.
    intros.
    eapply pimpl_ok3.
    eapply corr3_from_corr2; eauto with prog.
    apply extend_ok.
    apply recover_ok.

    cancel.
    cancel. eauto.

    step.
    cancel.
    xform.
    norm'l; unfold stars; cbn.
    cancel.
    cancel. eauto.

    step.
    all: rewrite H3; cancel.

    or_l; cancel.
    or_r; cancel.
  Qed.
  Proof.
    unfold rep, rep_common; destruct st; intros; eauto.
  Qed.
  Proof.
    unfold read.
    hoare.
  Qed.
  Proof.
    unfold trunc.
    safestep.
    eassign F; cancel.
    eauto.
    step.
    unfold roundup; rewrite divup_0; omega.

    (* crashes *)
    xcrash.
    or_l; cancel.
    or_r; cancel.
  Qed.
  Proof.
    unfold avail.
    step.
    step.
    cancel.
  Qed.
  Proof.
    unfold init, rep.
    step.
    unfold PaddedLog.xparams_ok, PaddedLog.DescSig.xparams_ok, PaddedLog.DataSig.xparams_ok; intuition.
    substl (LogDescriptor xp); unfold PaddedLog.DescSig.RALen.
    eapply goodSize_trans; [ | eauto ]; omega.
    substl (LogData xp); substl (LogDescriptor xp); unfold PaddedLog.DataSig.RALen.
    eapply goodSize_trans; [ | eauto ]; omega.
    step.
    rewrite roundup_0; auto.
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

    prestep.
    safecancel.
    eassign F; cancel. auto.
    step.

    or_l. norm; [ cancel | intuition; pred_apply; norm ].
    eassign (PaddedLog.padded_log dummy ++ PaddedLog.padded_log new).
    cancel; auto.
    intuition.

    xcrash.
    or_l; cancel.
    or_r; cancel.
  Qed.
  Proof.
    unfold recover.
    prestep. norm. cancel.
    intuition simpl.
    pred_apply.
    eassign F; cancel.
    eauto.

    step.
    norm'l.
    unfold PaddedLog.would_recover in *.
    xcrash.
    xform.
    cancel.

    eassign (PaddedLog.Rollback dummy).
    intuition simpl.
    pred_apply; cancel.
    auto.

    step.
    norm'l.
    unfold PaddedLog.would_recover in *.
    xcrash.
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
    apply PaddedLog.xform_rep_synced.
    all: auto.
  Qed.
  Proof.
    unfold rep, rep_common; intros.
    xform.
    rewrite PaddedLog.rep_extended_facts.
    xform; cancel.
    rewrite PaddedLog.xform_rep_extended.
    cancel.
    rewrite PaddedLog.rep_synced_app_pimpl.
    or_r; or_l; cancel.
  Qed.
  Proof.
    unfold rep, rep_common; intros.
    xform.
    rewrite PaddedLog.xform_rep_rollback.
    cancel.
  Qed.
  Proof.
    unfold rep, rep_common; intros.
    xform.
    rewrite PaddedLog.xform_would_recover'.
    cancel.
  Qed.
  Proof.
    unfold rep, PaddedLog.would_recover'; intros.
    cancel.
    eassign padded; cancel.
    or_l; cancel.
  Qed.
  Proof.
    unfold rep, PaddedLog.would_recover'; intros.
    cancel.
    eassign padded; cancel.
    or_r; or_l; cancel.
  Qed.
  Proof.
    unfold rep; intros.
    destruct st; cancel;
    try erewrite PaddedLog.rep_hashmap_subset; eauto.
    all: cancel; eauto.
    rewrite PaddedLog.would_recover'_hashmap_subset; eauto.
  Qed.