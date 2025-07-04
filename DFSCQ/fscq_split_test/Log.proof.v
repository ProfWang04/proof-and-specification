  Proof.
    unfold rep; destruct st; intros; eauto.
  Qed.
  Proof.
    unfold intact; auto.
  Qed.
  Proof.
    unfold recover_any; auto.
  Qed.
  Proof.
    unfold intact; cancel.
  Qed.
  Proof.
    unfold intact; cancel.
  Qed.
  Proof.
    unfold recover_any; cancel.
  Qed.
  Proof.
    unfold intact, recover_any, rep, rep_inner; cancel.
    apply GLog.cached_recover_any.
    eauto.
    apply GLog.cached_recover_any.
    eapply sm_ds_valid_pushd_r; eauto.
    Unshelve. all: eauto.
  Qed.
  Proof.
    unfold intact, recover_any, rep, rep_inner; cancel.
    apply GLog.cached_recover_any.
    Unshelve. all: eauto.
  Qed.
  Proof.
    unfold rep, rep_inner; cancel.
    eapply sm_ds_valid_pushd_r; eauto.
  Qed.
  Proof.
    unfold rep, rep_inner, GLog.rep; intros; split; cancel.
    eexists; eauto.
  Qed.
  Proof.
    unfold rep, rep_inner, GLog.rep; intros; split; cancel.
    eexists; eauto.
  Qed.
  Proof.
    intros.
    destruct st; unfold rep_inner, GLog.would_recover_any.
    all: try erewrite GLog.rep_hashmap_subset; eauto.
    cancel.
    erewrite GLog.rep_hashmap_subset; eauto.
    auto.
  Qed.
  Proof.
    unfold rep; intros; cancel.
    erewrite rep_inner_hashmap_subset; eauto.
  Qed.
  Proof.
    unfold intact; intros; cancel;
    erewrite rep_hashmap_subset; eauto.
    all: cancel.
  Qed.
  Proof.
    unfold rep_inner; intros.
    rewrite GLog.cached_recovering.
    norm'l. cancel.
    eassign (mk_mstate vmap0 ms'); auto.
    apply map_empty_vmap0.
  Qed.
  Proof.
    unfold rep_inner; intros.
    rewrite GLog.rollback_recovering.
    cancel.
  Qed.
  Proof.
    unfold readOnly; intros; deex; intuition.
  Qed.
  Proof.
    firstorder.
  Qed.
  Proof.
    intros; substl; eauto.
  Qed.
  Proof.
    intuition.
  Qed.
  Proof.
    unfold readOnly.
    intuition congruence.
  Qed.
  Proof.
    induction d' using rev_ind; intros.
    constructor.
    apply Forall_app.
    eapply IHd'.
    eapply possible_crash_mem_except in H.
    rewrite list2nmem_except_last in *.
    eauto.
    specialize (H (length d')); cbn in *.
    erewrite list2nmem_sel_inb in *.
    intuition.
    congruence.
    rewrite selN_app2 in * by auto.
    rewrite Nat.sub_diag in *; cbn in *.
    repeat deex.
    inversion H; subst; auto.
    inversion H; subst; auto.
    rewrite app_length; cbn; omega.
  Unshelve.
    all: auto.
  Qed.
  Proof.
    intros.
    unfold crash_xform, diskIs in *.
    deex.
    eapply sm_vs_valid_all_synced.
    eapply sm_ds_valid_nthd; eauto.
    eauto using possible_crash_list2nmem_length.
    eauto using possible_crash_list2nmem_synced.
  Qed.
  Proof.
    intros.
    apply crash_xform_diskIs in H.
    destruct_lift H.
    unfold diskIs in *; subst.
    eapply possible_crash_list2nmem_synced in H0.
    unfold sm_synced, sm_vs_valid.
    rewrite Forall_forall in *.
    intuition.
    congruence.
    unfold vs_synced.
    rewrite H0; auto.
    eapply in_selN; auto.
  Qed.
  Proof.
    induction a; cbn; intros;
      destruct b; cbn in *; try congruence.
    rewrite IHa by omega.
    cancel.
  Qed.
  Proof.
    intros.
    setoid_rewrite filter_In in H0.
    generalize dependent b.
    generalize dependent a.
    induction a; cbn; intros;
      destruct b; cbn in *; try congruence.
    denote In as Hi.
    destruct f eqn:Hf; cbn in *; eauto.
    rewrite IHa; auto.
    cancel.
    erewrite Hi with (y := v); eauto.
    intuition.
    eapply Hi; split; eauto.
    rewrite IHa; eauto.
    intuition.
    eapply Hi; split; eauto.
  Qed.
  Proof.
    induction a; cbn; intros;
      destruct b; cbn in *; try congruence.
    rewrite IHa, H0 by (auto; omega). cancel.
  Qed.
  Proof.
    unfold init, rep.
    step.
    step.
    apply sm_ds_valid_synced.
    apply sm_vs_valid_disk_exact.
    apply list2nmem_array.
    apply list2nmem_array.
    autorewrite with lists. auto.
  Qed.
  Proof.
    unfold begin.
    hoare using dems.
    rewrite replay_disk_empty; auto.
  Qed.
  Proof.
    unfold abort.
    safestep.
    step using dems; subst; simpl.
    pred_apply; cancel.
    eapply sm_ds_valid_pushd_r; eauto.
    eapply readOnlyLL; eauto; try reflexivity; simpl; dems.
    pimpl_crash; norm. cancel.
    eassign (mk_mstate vmap0 (MSGLog ms_1)).
    intuition; pred_apply; cancel.
    eapply sm_ds_valid_pushd_r; eauto.
  Qed.
  Proof.
    unfold read.
    prestep.
    cancel.
    step.

    eapply replay_disk_eq; eauto.
    eassign ds!!; pred_apply; cancel.
    pimpl_crash; cancel.

    cancel.
    2: step.
    eexists; subst.
    eapply ptsto_replay_disk_not_in; eauto.
    apply MapFacts.not_find_in_iff; eauto.

    pimpl_crash; norm. cancel.
    eassign (mk_mstate (MSTxn ms_1) ms'_1).
    intuition; pred_apply; cancel.
  Qed.
  Proof.
    unfold write.
    hoare using dems.
    pred_apply; cancel.

    apply map_valid_add; eauto.
    erewrite <- replay_disk_length.
    eapply list2nmem_ptsto_bound; eauto.

    rewrite replay_disk_add; eauto.

    eapply sm_ds_valid_pushd.
    eapply sm_vs_valid_same_upd_synced.
    eapply sm_ds_valid_pushd_l; eauto.
    eapply sm_ds_valid_pushd_r; eauto.

    rewrite replay_disk_add.
    eapply list2nmem_updN. eauto.
  Qed.
  Proof.
    unfold dwrite, recover_any.
    step.
    step; subst.

    eapply map_valid_remove; autorewrite with lists; eauto.
    rewrite dsupd_latest_length; auto.
    rewrite dsupd_latest.
    apply updN_replay_disk_remove_eq; eauto.
    rewrite dsupd_latest.
    eapply list2nmem_updN; eauto.

    (* crash conditions *)
    xcrash.
    or_l; cancel; xform_normr; cancel.
    eauto.

    or_r; cancel.
    xform_normr; cancel.
    eauto.

    Unshelve. all: eauto.
  Qed.
  Proof.
    unfold dsync, recover_any.
    step.
    step; subst.
    rewrite dssync_latest; unfold vssync; apply map_valid_updN; auto.
    rewrite dssync_latest; substl (ds!!) at 1.
    apply replay_disk_vssync_comm.
    Unshelve. eauto.
  Qed.
  Proof.
    unfold flushall, recover_any.
    hoare.
    xcrash.
    eauto.
    Unshelve. eauto.
  Qed.
  Proof.
    unfold flushsync, recover_any.
    hoare.
    xcrash.
    eauto.
    Unshelve. eauto.
  Qed.
  Proof.
    unfold flushall_noop, recover_any.
    hoare.
    xcrash.
    eauto.
    Unshelve. eauto.
  Qed.
  Proof.
    unfold flushsync_noop, recover_any.
    hoare.
    xcrash.
    eauto.
    Unshelve. eauto.
  Qed.
  Proof.
    unfold commit, recover_any.
    step.
    step.
    step.
    step.

    xcrash.
    unfold GLog.would_recover_any.
    cancel.
    constructor; auto.
    eauto.

    step.
    step.
    step.
    xcrash.
    eauto.
    step.
    xcrash.
    rewrite GLog.cached_recover_any.
    unfold GLog.would_recover_any.
    cancel.
    constructor; auto.
    eauto.
    Unshelve. all: eauto.
  Qed.
  Proof.
    intros.
    eapply pimpl_ok2.
    apply abort_ok.
    safecancel.
    apply sep_star_comm.
    auto.
    step.
    cancel.
  Qed.
  Proof.
    unfold after_crash; eauto.
  Qed.
  Proof.
    unfold before_crash; eauto.
  Qed.
  Proof.
    unfold recover, after_crash, before_crash, rep, rep_inner.
    safestep.
    unfold GLog.recover_any_pred. norm.
    eassign F; cancel.
    or_l; cancel.
    intuition simpl; eauto.
    unfold GLog.recover_any_pred. norm.
    cancel.
    or_r; cancel.
    intuition simpl; eauto.
    eauto.

    step.
    eapply sm_ds_valid_synced.
    eapply sm_vs_valid_sm_synced; eauto.
    rewrite Nat.min_l by eauto.
    cancel.

    norm'l.
    repeat xcrash_rewrite.
    xform_norm; cancel.
    xform_norm; cancel.
    xform_norm.
    norm.
    cancel.
    intuition simpl; eauto.
    pred_apply.
    norm.
    cancel.
    eassign (mk_mstate vmap0 x1); eauto.
    intuition simpl; eauto.
    eapply sm_ds_valid_synced.
    eapply sm_vs_valid_sm_synced; eauto.
  Qed.
  Proof.
    unfold before_crash, after_crash, rep_inner; intros.
    xform_norm.
    rewrite BUFCACHE.crash_xform_rep_pred by eauto.
    norm.
    cancel.
    intuition.
    pred_apply.
    xform_norm.
    rewrite GLog.crash_xform_recovering.
    unfold GLog.recover_any_pred.
    norm. unfold stars; simpl.
    cancel.
    unfold GLog.recover_any_pred; cancel.
    or_l; cancel.
    eassign (mk_mstate vmap0 ms); eauto.
    auto.
    eauto using sm_ds_valid_synced, sm_vs_valid_sm_synced.
    intuition simpl; eauto.
    eapply crash_xform_diskIs_trans; eauto.

    unfold stars; simpl.
    cancel.
    or_r; cancel.
    eassign (mk_mstate vmap0 ms); eauto.
    auto.
    eauto using sm_ds_valid_synced, sm_vs_valid_sm_synced.
    intuition simpl; eauto.
    eapply crash_xform_diskIs_trans; eauto.
  Qed.
  Proof.
    unfold recover_any, after_crash, rep, rep_inner; intros.
    xform_norm.
    rewrite BUFCACHE.crash_xform_rep_pred by eauto.
    xform_norm.
    norm. cancel.
    intuition simpl; pred_apply; xform_norm.
    rewrite GLog.crash_xform_any.
    unfold GLog.recover_any_pred.
    norm. cancel.
    eassign (mk_mstate vmap0 ms); eauto.
    intuition simpl; eauto.

    or_l; cancel.
    eauto using sm_ds_valid_synced, sm_vs_valid_sm_synced.
    intuition simpl; eauto.
    cancel.
    or_r; cancel.
    eassign (mk_mstate vmap0 ms); eauto.
    eauto.
    eauto using sm_ds_valid_synced, sm_vs_valid_sm_synced.
    intuition simpl; eauto.
  Qed.
  Proof.
    unfold after_crash, rep, rep_inner.
    intros. norm. cancel.
    denote or as Hor; apply sep_star_or_distr in Hor.
    destruct Hor; destruct_lift H.
    or_l; cancel.
    eauto.
    or_r; cancel.
    intuition simpl. eassumption.
    auto.
  Qed.
  Proof.
    intros; rewrite after_crash_notxn; cancel.
  Qed.
  Proof.
    unfold after_crash, rep_inner; intros.
    xform_norm.
    rewrite BUFCACHE.crash_xform_rep_pred by eauto.
    xform_norm.
    denote crash_xform as Hx.
    apply crash_xform_sep_star_dist in Hx.
    rewrite crash_xform_or_dist in Hx.
    apply sep_star_or_distr in Hx.
    norm. unfold stars; simpl. cancel.
    intuition simpl; eauto.

    destruct Hx as [Hx | Hx];
    autorewrite with crash_xform in Hx;
    destruct_lift Hx; pred_apply.

    rewrite GLog.crash_xform_cached.
    norm. cancel.
    or_l; cancel.
    eassign (mk_mstate vmap0 ms'); cancel.
    auto.
    eauto using sm_ds_valid_synced, sm_vs_valid_sm_synced.
    intuition simpl; eauto.
    eapply crash_xform_diskIs_trans; eauto.

    rewrite GLog.crash_xform_rollback.
    norm. cancel.
    or_r; cancel.
    eassign (mk_mstate vmap0 ms'); cancel.
    auto.
    eauto using sm_ds_valid_synced, sm_vs_valid_sm_synced.
    intuition simpl; eauto.
    eapply crash_xform_diskIs_trans; eauto.
  Qed.
  Proof.
    unfold rep_inner; intros.
    xform_norml.
    rewrite GLog.crash_xform_cached; cancel.
    eassign (mk_mstate vmap0 ms').
    or_l; cancel.
    eauto using sm_ds_valid_synced, sm_vs_valid_sm_synced.
    eapply crash_xform_diskIs_pred; eauto.

    rewrite GLog.crash_xform_rollback; cancel.
    eassign (mk_mstate vmap0 ms').
    or_r; cancel.
    eauto using sm_ds_valid_synced, sm_vs_valid_sm_synced.
    eapply crash_xform_diskIs_pred; eauto.
  Qed.
  Proof.
    unfold Proper, respectful; intros.
    unfold rep; cancel.
    apply H0.
  Qed.
  Proof.
    unfold Proper, respectful; intros.
    unfold intact; cancel; or_l.
    rewrite H0; eauto.
    rewrite active_notxn.
    rewrite H0; eauto.
  Qed.
  Proof.
    unfold Proper, respectful; intros.
    unfold after_crash.
    subst. norm. cancel. intuition simpl.
    pred_apply. norm.

    cancel.
    rewrite sep_star_or_distr.
    or_l; cancel.
    rewrite H0; eauto.
    intuition simpl; eauto.

    cancel.
    rewrite sep_star_or_distr.
    or_r; cancel.
    rewrite H0; eauto.
    intuition simpl; eauto.
  Qed.
  Proof.
    unfold rep, after_crash, rep_inner; intros.
    safecancel.
    or_l; cancel.
    eauto using sm_ds_valid_synced, sm_vs_valid_sm_synced.
    eauto.
    auto.
  Qed.
  Proof.
    unfold rep, after_crash, rep_inner; intros.
    safecancel.
    or_r; cancel.
    eauto using sm_ds_valid_synced, sm_vs_valid_sm_synced.
    eauto.
    auto.
  Qed.
  Proof.
    unfold idempred; auto.
  Qed.
  Proof.
    unfold idempred; intros.
    xform_norm.
    rewrite crash_xform_any; cancel.
    rewrite crash_xform_before_crash; cancel.
    rewrite after_crash_idem; cancel.
  Qed.
  Proof.
    unfold idempred; cancel.
  Qed.
  Proof.
    intros.
    rewrite intact_any.
    apply recover_any_idempred.
  Qed.
  Proof.
    intros.
    rewrite notxn_intact.
    apply intact_idempred.
  Qed.
  Proof.
    intros.
    rewrite active_intact.
    apply intact_idempred.
  Qed.
  Proof.
    unfold idempred; intros.
    or_r; cancel.
  Qed.
  Proof.
    unfold idempred; intros.
    or_r; or_l; cancel.
  Qed.
  Proof.
    unfold Proper, respectful; intros.
    unfold idempred; cancel.
    unfold recover_any, rep. or_l; cancel.
    rewrite H0; cancel.

    unfold before_crash, rep.
    or_r; or_l.
    norm. cancel.
    intuition. pred_apply.
    norm. cancel.
    rewrite H0; cancel.
    intuition simpl; eauto.

    unfold after_crash, rep.
    or_r; or_r.
    norm. cancel.
    intuition. pred_apply.
    norm. cancel.
    rewrite sep_star_or_distr.
    or_l; cancel.
    rewrite H0; cancel.
    intuition simpl; eauto.

    norm; auto. cancel.
    rewrite sep_star_or_distr.
    or_r; cancel.
    rewrite H0; cancel.
    intuition simpl; eauto.
  Qed.
  Proof.
    unfold intact, rep, rep_inner; intros.
    xform_norm;
    rewrite BUFCACHE.crash_xform_rep_pred by eauto;
    xform_norm;
    denote crash_xform as Hx;
    apply crash_xform_sep_star_dist in Hx;
    rewrite GLog.crash_xform_cached in Hx;
    destruct_lift Hx.

    safecancel.
    eassign (mk_mstate (MSTxn x_1) dummy1).
    cancel. auto.
    eauto using sm_ds_valid_synced, sm_vs_valid_sm_synced.
    eauto.
    eauto.

    safecancel.
    eassign (mk_mstate vmap0 dummy1).
    cancel. auto.
    eauto using sm_ds_valid_synced, sm_vs_valid_sm_synced.
    eauto. auto.
  Qed.
  Proof.
    unfold idempred, recover_any, after_crash, before_crash, rep, rep_inner; intros.
    xform_norm;
    rewrite BUFCACHE.crash_xform_rep_pred by eauto;
    xform_norm;
    denote crash_xform as Hx.

    - apply crash_xform_sep_star_dist in Hx;
      rewrite GLog.crash_xform_any in Hx;
      unfold GLog.recover_any_pred in Hx;
      destruct_lift Hx.

      denote or as Hor.
      apply sep_star_or_distr in Hor.
      destruct Hor.

      safecancel.
      or_l; cancel.
      eassign (mk_mstate (Map.empty valu) dummy1).
      cancel. auto.
      eauto using sm_ds_valid_synced, sm_vs_valid_sm_synced.
      eassumption. auto.

      safecancel.
      or_r; cancel.
      eassign (mk_mstate (Map.empty valu) dummy1).
      cancel. auto.
      eauto using sm_ds_valid_synced, sm_vs_valid_sm_synced.
      eassumption. auto.

    - apply crash_xform_sep_star_dist in Hx;
      rewrite GLog.crash_xform_recovering in Hx;
      unfold GLog.recover_any_pred in Hx;
      destruct_lift Hx.

      denote or as Hor.
      apply sep_star_or_distr in Hor.
      destruct Hor.

      safecancel.
      or_l; cancel.
      match goal with |- context [?x] => eassign (mk_mstate (Map.empty valu) x) end.
      cancel. auto.
      eauto using sm_ds_valid_synced, sm_vs_valid_sm_synced.
      eassumption.
      eapply crash_xform_diskIs_trans; eauto.


      safecancel.
      or_r; cancel.
      match goal with |- context [?x] => eassign (mk_mstate (Map.empty valu) x) end.
      cancel. auto.
      eauto using sm_ds_valid_synced, sm_vs_valid_sm_synced.
      eassumption.
      eapply crash_xform_diskIs_trans; eauto.

    - apply crash_xform_sep_star_dist in Hx.
      rewrite crash_xform_or_dist in Hx.
      apply sep_star_or_distr in Hx;
      destruct Hx; autorewrite with crash_xform in H0.

      rewrite GLog.crash_xform_cached in H0.
      destruct_lift H0.
      safecancel.
      or_l; cancel.
      match goal with |- context [?x] => eassign (mk_mstate (Map.empty valu) x) end.
      cancel. auto.
      eauto using sm_ds_valid_synced, sm_vs_valid_sm_synced.
      eassumption.
      eapply crash_xform_diskIs_trans; eauto.

      rewrite GLog.crash_xform_rollback in H0.
      destruct_lift H0.
      safecancel.
      or_r; cancel.
      match goal with |- context [?x] => eassign (mk_mstate (Map.empty valu) x) end.
      cancel. auto.
      eauto using sm_ds_valid_synced, sm_vs_valid_sm_synced.
      eassumption.
      eapply crash_xform_diskIs_trans; eauto.
  Qed.
  Proof.
    unfold read_array.
    hoare.

    rewrite isolateN_fwd with (i:=i) by auto.
    rewrite <- surjective_pairing.
    cancel.
  Qed.
  Proof.
    unfold write_array.
    prestep. norm. cancel.
    unfold rep_inner; intuition.
    pred_apply; cancel.
    eauto.
    subst; pred_apply.
    rewrite isolateN_fwd with (i:=i) by auto.
    rewrite surjective_pairing with (p := selN vs i ($0, nil)).
    cancel.

    step.
    rewrite <- isolateN_bwd_upd by auto.
    cancel.
  Qed.
  Proof.
    unfold read_range; intros.
    safestep. auto. auto. eauto.
    subst; pred_apply; cancel.

    eapply readOnly_refl; eauto.
    eauto.
    safestep.
    reflexivity.
    subst; denote (Map.elements (MSTxn a1)) as Hx; rewrite <- Hx. eauto.
    eapply lt_le_trans; eauto.
    subst; denote (Map.elements (MSTxn a1)) as Hx; rewrite <- Hx.
    pred_apply; cancel.

    step.
    rewrite firstn_S_selN_expand with (def := $0).
    rewrite fold_left_app; simpl.
    erewrite selN_map by omega; subst; auto.
    rewrite map_length; omega.

    unfold rep_inner; cancel.
    step.
    cancel.
    eassign raw; pred_apply.
    cancel; eauto.
    apply GLog.rep_hashmap_subset; eauto.
    Unshelve. exact tt. auto.
  Qed.
  Proof.
    unfold vsupsyn_range; intros.
    erewrite firstn_S_selN with (def := $0) by auto.
    rewrite app_length; simpl.
    rewrite <- repeat_app.
    rewrite combine_app by (autorewrite with lists; auto); simpl.
    rewrite <- app_assoc.
    repeat rewrite firstn_app_l; auto.
    all: autorewrite with lists; rewrite firstn_length_l; omega.
  Qed.
  Proof.
    unfold vsupsyn_range; intros.
    setoid_rewrite skipn_selN_skipn with (def := ($0, nil)) at 4.
    rewrite <- cons_nil_app.
    repeat rewrite skipn_app_eq;
      autorewrite with lists; repeat rewrite firstn_length_l by omega;
      simpl; auto; try omega.
    rewrite firstn_length_l; omega.
  Qed.
  Proof.
    cancel.
  Qed.
  Proof.
    unfold vsupsyn_range; intros.
    apply arrayN_unify.
    rewrite updN_app2; autorewrite with lists.
    all: repeat rewrite firstn_length_l; try omega.
    erewrite firstn_S_selN, repeat_app_tail by omega.
    rewrite combine_app, <- app_assoc.
    f_equal.
    rewrite Nat.sub_diag, updN_0_skip_1, skipn_skipn.
    rewrite Nat.add_1_l, cons_app.
    apply eq_refl.
    rewrite skipn_length; omega.
    rewrite firstn_length_l, repeat_length; omega.
  Qed.
  Proof.
    intros.
    apply list2nmem_arrayN_bound in H0; destruct H0; subst; simpl in *.
    inversion H.
    rewrite replay_disk_length in *.
    omega.
  Qed.
  Proof.
    unfold write_range; intros.
    step.

    safestep. reflexivity. eauto. eauto.
    rewrite vsupsyn_range_length; auto.
    omega.
    rewrite firstn_length_l; omega.

    step.
    eapply vsupsyn_range_progress; eauto.
    unfold rep_inner; cancel.

    step.
    erewrite firstn_oob; eauto.
    eassign raw.
    pred_apply; cancel.
    apply GLog.rep_hashmap_subset; eauto.
    auto.
    auto.
    Unshelve. exact tt. eauto.
  Qed.
  Proof.
    unfold read_cond; intros.
    step.

    safestep.
    safestep.
    safestep.

    eauto. eauto.
    eapply lt_le_trans; eauto. eauto.

    step; step.
    apply not_true_is_false; auto.
    rewrite firstn_S_selN_expand with (def := $0).
    rewrite fold_left_app; simpl.
    erewrite selN_map by omega; subst; auto.
    rewrite map_length; omega.

    pimpl_crash. unfold rep_inner; norm. cancel. intuition simpl. pred_apply.
    eassign (mk_mstate (MSTxn a1) (MSGLog ms'_1)); cancel.
    eexists.
    eapply hashmap_subset_trans; eauto.

    destruct a2.
    safestep.
    or_l; cancel.
    safestep.
    or_r; cancel.
    eassign raw; pred_apply; cancel.
    apply GLog.rep_hashmap_subset; eauto.
    eauto.

    Unshelve. all: eauto; try exact tt; try exact nil.
  Qed.
  Proof.
    intros.
    apply Forall_map_l.
    eapply listmatch_ptsto_list2nmem_inbound.
    pred_apply.
    rewrite listmatch_map_l.
    rewrite listmatch_sym. eauto.
  Qed.
  Proof.
    split; cancel.
  Qed.
  Proof.
    split; cancel.
  Qed.
  Proof.
    unfold listmatch; induction avl; destruct ovl;
    simpl; intros; eauto; destruct_lift H; inversion H2.
    inversion H0; subst.
    rewrite vsupd_vecs_vsupd_notin by auto.
    denote NoDup as Hx.
    refine (_ (IHavl ovl m _ _ Hx)); [ intro | pred_apply; cancel ].
    erewrite (@list2nmem_sel _ _ m a_1 (p_cur, _)) by (pred_apply; cancel).
    erewrite <- vsupd_vecs_selN_not_in; eauto.
    apply sep_star_reorder_helper2.
    eapply list2nmem_updN.
    pred_apply; cancel.
  Qed.
  Proof.
    unfold listmatch; induction al; destruct vsl;
    simpl; intros; eauto; destruct_lift H; inversion H1.
    refine (_ (IHal vsl (vssync m a) _ _)).
    apply pimpl_apply; cancel.
    unfold vssync.
    erewrite <- (@list2nmem_sel _ _ m a) by (pred_apply; cancel).
    apply sep_star_reorder_helper3.
    eapply list2nmem_updN.
    pred_apply; cancel.
  Qed.
  Proof.
    unfold listmatch; induction al; destruct vsl;
    simpl; intros; eauto; destruct_lift H; inversion H1.
    rewrite firstn_nil; simpl; pred_apply; cancel.

    destruct n; simpl.
    apply sep_star_comm; apply sep_star_assoc; apply sep_star_comm.
    apply sep_star_lift_apply'; auto.
    refine (_ (IHal 0 vsl _ m _)); intros.
    simpl in x; pred_apply; cancel.
    pred_apply; repeat cancel.

    apply sep_star_comm; apply sep_star_assoc; apply sep_star_comm.
    apply sep_star_lift_apply'; auto.
    refine (_ (IHal n vsl _ (vssync m a) _)); intros.
    pred_apply; cancel.

    unfold vssync.
    erewrite <- (@list2nmem_sel _ _ m a) by (pred_apply; cancel); simpl.
    apply sep_star_comm in H.
    apply sep_star_assoc in H.
    eapply list2nmem_updN with (y := (p_cur, nil)) in H.
    pred_apply; repeat cancel.
  Qed.
  Proof.
    induction a; intros.
    cbn in *; auto.
    rewrite sm_upd_vecs_cons.
    cbn in *.
    destruct_lifts.
    eapply pimpl_apply.
    2: eapply ptsto_upd'. cancel.
    eapply pimpl_apply in H.
    eapply IHa in H.
    2: cancel.
    pred_apply; cancel.
  Qed.
  Proof.
    induction a; intros.
    cbn in *; auto.
    rewrite sm_sync_vecs_cons.
    cbn in *.
    destruct_lifts.
    eapply pimpl_apply.
    2: eapply ptsto_upd'. cancel.
    eapply pimpl_apply in H.
    eapply IHa in H.
    2: cancel.
    pred_apply; cancel.
  Qed.
  Proof.
    unfold dwrite_vecs.
    step.
    eapply dwrite_ptsto_inbound; eauto.

    step; subst.
    apply map_valid_map0.
    rewrite dsupd_vecs_latest; apply dwrite_vsupd_vecs_ok; auto.
    eapply sm_upd_vecs_listpred_ptsto; eauto.

    (* crash conditions *)
    xcrash.
    or_l; unfold recover_any, rep; cancel.
    xform_normr; cancel.
    eassign x; eassign (mk_mstate vmap0 (MSGLog ms_1), x0); simpl; eauto.
    unfold rep_inner.
    pred_apply; cancel.
    eauto.

    or_r; unfold recover_any, rep; cancel.
    xform_normr; cancel.
    eassign x; eassign (mk_mstate vmap0 (MSGLog ms_1), x0); simpl; eauto.
    unfold rep_inner.
    pred_apply; cancel.
    eauto.
  Qed.
  Proof.
    unfold dsync_vecs, recover_any.
    step.
    eapply listmatch_ptsto_list2nmem_inbound.
    pred_apply; rewrite listmatch_sym; eauto.

    step; subst; try rewrite dssync_vecs_latest.
    apply map_valid_vssync_vecs; auto.
    rewrite <- replay_disk_vssync_vecs_comm.
    f_equal; auto.
    apply dsync_vssync_vecs_ok; auto.
    apply sm_sync_vecs_listpred_ptsto; eauto.

    Unshelve. eauto.
  Qed.
  Proof.
    induction l; intros.
    constructor.
    constructor.
    cbn in H.
    eapply pimpl_apply, ptsto_valid with (a := a) in H.
    2: cancel.
    eapply sm_vs_valid_vs_synced; eauto.
    eapply IHl; eauto.
    pred_apply; cancel.
  Qed.
  Proof.
    induction l; intros.
    constructor.
    constructor.
    cbn in H.
    eapply pimpl_apply, ptsto_valid with (a := a) in H.
    2: cancel.
    eapply sm_ds_valid_ds_synced; eauto.
    eapply IHl; eauto.
    pred_apply; cancel.
  Qed.
  Proof.
    unfold dsync_vecs, recover_any.
    step.
    eapply listmatch_ptsto_list2nmem_inbound.
    pred_apply; rewrite listmatch_sym; eauto.
    eassign (firstn (length al) vsl).
    erewrite <- firstn_skipn with (l := vsl) (n := length al) at 1.
    rewrite listmatch_app_rev. cancel.
    rewrite firstn_length_l in *; auto.
    destruct_lifts.
    erewrite listmatch_length_pimpl in H.
    destruct_lift H.
    autorewrite with lists in *; omega.

    step; subst; try rewrite dssync_vecs_latest.
    apply map_valid_vssync_vecs; auto.
    rewrite <- replay_disk_vssync_vecs_comm.
    f_equal; auto.
    erewrite <- vssync_vecs_nop with (vs := ds!!).
    rewrite vssync_vecs_app', vssync_vecs_app_comm.
    apply dsync_vssync_vecs_ok; auto.

    eapply sm_vs_valid_listpred_Forall; eauto.
    rewrite listpred_app.
    eapply pimpl_apply.
    2: eapply sm_sync_vecs_listpred_ptsto. cancel.
    pred_apply; cancel.

    rewrite dssync_vecs_app.
    rewrite dssync_vecs_nop with (l := synced); auto.
    eapply sm_ds_valid_listpred_Forall; eauto.
    eapply sm_ds_valid_dssync_vecs'; eauto.
    Unshelve. eauto.
  Qed.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply dsync_vecs_additional_ok'.
    intros. norml.
    assert (NoDup all).
    eapply listmatch_nodup with (m := sm) (b := sml).
    pred_apply. rewrite listmatch_sym. cancel.
    assert (length sml = length all) by eauto using listmatch_length_r.
    assert (length vsl = length all) by eauto using listmatch_length_r.
    cancel.

    (* split synced from all in syncedmem *)
    unfold listmatch.
    erewrite listpred_partition with (f := fun x => inb al (snd x)).
    rewrite partition_eq_filter; cbn [fst snd].
    rewrite listpred_permutation with (a := filter _ _).
    2: eapply Permutation.Permutation_sym, filter_elements_permutation; auto.
    2: rewrite map_snd_combine; auto.
    erewrite <- listpred_ptsto_combine_ex.
    rewrite <- sort_by_index_combine with (f := Nat.eqb) (la := sml) (lb := all); eauto.
    eassign 0. repeat eassign true.
    cancel.
    erewrite filter_ext.
    rewrite listpred_ptsto_combine_same; auto.
    solve [apply pimpl_refl | apply sep_star_comm].
    2: intros; cbn.
    2: match goal with |- ?X = ?Y ?y =>
        match eval pattern y in X with
        | ?X' y => unify X' Y end end; auto.
    intros x y Hi.
    rewrite filter_In in Hi. destruct Hi as [Ha Hb].
    denote selN as Hs.
    unfold inb in Hb.
    eapply in_selN_exists in Ha.
    destruct Ha as [i [Hc Ha] ].
    erewrite selN_combine in Ha by auto.
    rewrite <- Ha in *.
    destruct in_dec; cbn in *; try congruence.
    rewrite combine_length_eq2 in Hc by auto.
    eapply Hs in Hc.
    intuition eauto.
    inversion Ha; eauto.
    autorewrite with lists; auto.
    intros.
    eapply in_combine_ex_l; eauto; omega.

    (* split unsynced from all on disk *)
    unfold listmatch.
    rewrite listpred_permutation.
    cancel. solve [reflexivity].
    shelve.
    rewrite combine_app.
    erewrite partition_permutation_app.
    rewrite partition_eq_filter.
    cbn [fst snd].
    apply Permutation.Permutation_app.
    rewrite <- filter_elements_permutation with (a := al); auto.
    rewrite sort_by_index_combine; auto.
    rewrite map_snd_combine; auto.
    intros.
    eapply in_combine_ex_l; auto; omega.
    rewrite <- filter_r; auto.
    autorewrite with lists; auto.
    Unshelve.
    2: autorewrite with lists.
    2: replace (length vsl) with (length all) by auto.
    2: erewrite filter_selN_length with (l := all); eauto.
    eapply pimpl_ok2. eauto.
    cancel.

    (* reassemble disk pred *)
    unfold listmatch.
    rewrite listpred_permutation.
    cancel.
    rewrite combine_app by (rewrite split_length_l, sort_by_index_length; auto).
    symmetry.
    eapply Permutation.Permutation_trans.
    apply partition_permutation_app.
    rewrite partition_eq_filter.
    cbn [fst snd].
    apply Permutation.Permutation_app.
    rewrite <- filter_elements_permutation with (a := al); auto.
    rewrite sort_by_index_combine; auto.
    rewrite map_snd_combine; auto.
    intros.
    eapply in_combine_ex_l; auto; omega.
    cbn beta.
    erewrite filter_ext.
    erewrite filter_r; auto.
    2: intros; cbn.
    2: match goal with |- ?X = ?Y ?y =>
        match eval pattern y in X with
        | ?X' y => unify X' Y end end; auto.
    cbn. reflexivity.

    (* reassemble syncedmem pred *)
    unfold listmatch.
    apply listpred_permutation.
    eapply Permutation.Permutation_trans.
    apply partition_permutation_app.
    rewrite partition_eq_filter; cbn [fst snd].
    apply Permutation.Permutation_app; try reflexivity.
    apply permutation_filter; auto.

    (* reorder sync vec arguments *)
    apply dssync_vecs_permutation.
    symmetry.
    eapply Permutation.Permutation_trans.
    eapply partition_permutation_app.
    rewrite partition_eq_filter; cbn [fst snd].
    apply Permutation.Permutation_app; try reflexivity.
    apply permutation_filter; auto.
  Unshelve.
    all: solve [exact 0 | exact ($0, [])].
  Qed.
  Proof.
    unfold idempred, recover_any, after_crash, before_crash; cancel.
    rewrite rep_hashmap_subset by eauto.
    or_l; cancel.
    rewrite rep_inner_hashmap_subset in * by eauto.
    or_r. safecancel.
    rewrite rep_inner_hashmap_subset in * by eauto.
    denote or as Hor; apply sep_star_or_distr in Hor.
    destruct Hor.
    or_r; or_r.
    norm. cancel.
    intuition.
    pred_apply. norm. cancel.
    or_l; cancel.
    intuition simpl; eauto.
    or_r; or_r.
    norm. cancel.
    intuition.
    pred_apply. norm. cancel.
    rewrite rep_inner_hashmap_subset by eauto.
    or_r; cancel.
    intuition simpl; eauto.
  Qed.
  Proof.
    intros.
    rewrite crash_xform_intact.
    xform_norm.
    rewrite notxn_after_crash_diskIs.
    rewrite after_crash_idempred.
    cancel.
    pred_apply.
    rewrite dssync_vecs_nthd.
    rewrite crash_xform_diskIs_vssync_vecs; eauto.
    rewrite map_length in *; auto.
  Qed.
  Proof.
    intros.
    unfold rep, before_crash, rep_inner.
    xform_norm. cancel.
    xform_norm. cancel.
    xform_norm. norm.
    cancel.
    intuition simpl; eauto.
    pred_apply.
    norm.
    cancel.
    2: eauto.
    unfold GLog.rep.
    intros. norm.
    cancel.
    rewrite MLog.rep_synced_pimpl.
    cancel.
    intuition simpl; eauto.
    intuition simpl; eauto.
    eauto using sm_ds_valid_synced, sm_vs_valid_sm_synced.
  Qed.