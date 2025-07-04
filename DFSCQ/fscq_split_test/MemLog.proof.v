  Proof.
    unfold rep, synced_rep, unsync_rep; destruct st; intros; eauto 20.
  Qed.
  Proof.
    unfold would_recover_before; eauto.
  Qed.
  Proof.
    unfold would_recover_either; eauto 10.
  Qed.
  Proof.
    unfold rep; intros.
    destruct st; cancel.
    all: eauto.
    all: erewrite DLog.rep_hashmap_subset; eauto; cancel.
    or_l; cancel.
    or_r; cancel.
    Unshelve. all: easy.
  Qed.
  Proof.
    unfold would_recover_either; intros; cancel.
    all: erewrite rep_hashmap_subset; eauto; cancel.
  Qed.
  Proof.
    unfold rep, map_replay, unsync_rep, synced_rep in *.
    cancel; eauto.
    or_l; cancel.
    unfold equal_unless_in; intuition.
  Qed.
  Proof.
    unfold rep, map_replay, unsync_rep, synced_rep in *.
    cancel; eauto.
    or_l.
    eassign na.
    unfold DLog.rep. cancel; eauto.
    cancel.
    unfold log_valid; intuition.
    unfold KNoDup; auto.
    inversion H1.
    inversion H1.
  Qed.
  Proof.
    unfold equal_unless_in; firstorder.
  Qed.
  Proof.
    induction l; intros; simpl; auto.
    destruct a; simpl.
    inversion H; subst.
    rewrite <- IHl by auto.

    rewrite vsupd_vecs_vsupd_notin by auto.
    rewrite vssync_vsupd_eq.
    rewrite updN_vsupd_vecs_notin; auto.
  Qed.
  Proof.
    unfold synced_rep; intros.
    apply arrayN_unify.
    apply apply_synced_data_ok'.
    apply KNoDup_NoDup; auto.
  Qed.
  Proof.
    unfold equal_unless_in; induction l; intros; simpl.
    rewrite firstn_nil; simpl; intuition.
    split; intuition;
    destruct n; simpl; auto;
    destruct a; inversion H; simpl in *; intuition; subst.

    rewrite vsupd_vecs_vsupd_notin.
    rewrite vsupd_length, vsupd_vecs_length; auto.
    rewrite <- firstn_map_comm.
    contradict H2.
    eapply in_firstn_in; eauto.

    pose proof (IHl d n H5) as [Hx Hy].
    rewrite Hy by auto.
    rewrite vsupd_vecs_vsupd_notin.
    unfold vsupd; rewrite selN_updN_ne; auto.
    rewrite <- firstn_map_comm.
    contradict H4.
    eapply in_firstn_in; eauto.
  Qed.
  Proof.
    unfold unsync_rep, map_replay; cancel.
    apply apply_unsync_applying_ok'.
    apply KNoDup_NoDup; auto.
  Qed.
  Proof.
    induction l; intros; simpl.
    rewrite firstn_nil; simpl; auto.

    destruct a; inversion H; simpl in *; subst; intuition.
    destruct n; simpl; auto.
    rewrite vsupd_vecs_vsupd_notin by auto.
    unfold vsupd.
    rewrite selN_updN_ne by auto.
    rewrite vsupd_vecs_selN_not_in; auto.

    unfold vssync.
    rewrite -> updN_vsupd_vecs_notin by auto.
    rewrite <- IHl; auto.
    rewrite selN_updN_ne by auto.
    unfold vsupd.
    rewrite selN_updN_ne; auto.
  Qed.
  Proof.
    unfold unsync_rep, equal_unless_in; cancel.
    rewrite vssync_vecs_length, vsupd_vecs_length; auto.
    apply apply_unsync_syncing_ok'.
    apply KNoDup_NoDup; auto.
    eauto.
  Qed.
  Proof.
    unfold rep; intros.
    cancel; eauto.
    rewrite DLog.rep_rollback_pimpl; eauto.
    cancel.
  Qed.
  Proof.
    unfold rep; intros.
    cancel; eauto.
    rewrite DLog.rep_synced_pimpl; eauto.
    cancel.
  Qed.
  Proof.
    unfold would_recover_before, would_recover_either; cancel.
  Qed.
  Proof.
    unfold would_recover_before; cancel.
    Unshelve. eauto.
  Qed.
  Proof.
    unfold would_recover_either; cancel.
  Qed.
  Proof.
    unfold would_recover_either; cancel.
    rewrite rep_rollback_pimpl.
    or_r; or_r; or_r; cancel.
  Qed.
  Proof.
    unfold would_recover_before; cancel.
  Qed.
  Proof.
    unfold would_recover_either; intros.
    (** FIXME:
     * `cancel` works slowly when there are existentials.
     *  (when calling `apply finish_frame`)
     *)
    norm; unfold stars; simpl; auto.
    or_r; or_l; cancel.
  Qed.
  Proof.
    unfold would_recover_either; cancel.
  Qed.
  Proof.
    unfold would_recover_either; intros.
    norm; unfold stars; simpl; auto.
    or_r; or_r; cancel.
  Qed.
  Proof.
    unfold init, rep.
    step.
    step.
    eapply goodSize_trans; [ | eauto ]; omega.
    apply map_valid_map0.
  Qed.
  Proof.
    unfold read.
    prestep.

    cancel.
    step.
    subst.
    eapply replay_disk_eq; eauto.
    eassign dummy1; pred_apply; cancel.
    pimpl_crash; cancel; auto. cancel.

    unfold synced_rep; cancel.
    subst; eapply synced_data_replay_inb; eauto.
    eassign ((Map.elements ms_1)); pred_apply; cancel.

    prestep.
    cancel; subst; auto.
    assert (selN dummy1 a ($0, nil) = (vs_cur, vs_old)) as Hx.
    eapply replay_disk_none_selN; eauto.
    pred_apply; cancel.
    destruct (selN _ a _); inversion Hx; auto.

    erewrite DLog.rep_hashmap_subset; eauto.
    eauto.
    erewrite replay_disk_none_selN; try eassumption.
    eassign (vs_cur, vs_old); eauto.
    eexists. pred_apply; cancel.

    reflexivity.

    pimpl_crash; cancel; eauto.
    erewrite DLog.rep_hashmap_subset; eauto.
  Qed.
  Proof.
    unfold flush_noapply.
    step.
    eapply log_valid_entries_valid; eauto.
    hoare.

    or_l.
    cancel; unfold map_merge.
    rewrite replay_mem_app; eauto.
    apply MapFacts.Equal_refl.
    apply map_valid_replay_mem'; auto.
    eapply log_valid_replay; eauto.
    apply replay_disk_replay_mem; auto.

    repeat xcrash_rewrite.
    xform. cancel.
    xform_normr; cancel.
    or_l; cancel.
    auto. auto.
    xform_normr; cancel.
    or_r; cancel.
    auto. auto.
    Unshelve. auto.
  Qed.
  Proof.
    intros. rewrite vssync_vecs_length, vsupd_vecs_length; auto.
  Qed.
  Proof.
    intros.
    eapply length_eq_map_valid; eauto.
    rewrite vssync_vecs_length, vsupd_vecs_length; auto.
  Qed.
  Proof.
    intros; rewrite apply_synced_data_ok'. auto.
    apply KNoDup_NoDup; auto.
  Qed.
  Proof.
    intros; rewrite apply_synced_data_ok'; auto.
    rewrite replay_disk_twice; auto.
    apply KNoDup_NoDup; auto.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    destruct a; inversion H; subst; simpl in *.
    assert (~ In k (map fst l)).
    contradict H2.
    apply In_KIn; auto.

    rewrite replay_disk_updN_comm; auto.
    rewrite IHl; unfold vsupd; auto.
    rewrite replay_disk_updN_comm; auto.
    rewrite updN_twice.
    rewrite replay_disk_updN_comm; auto.
  Qed.
  Proof.
    intros.
    apply replay_disk_vsupd_vecs'.
    auto.
  Qed.
  Proof.
    unfold apply; intros.
    step.
    unfold synced_rep; cancel.
    step.
    rewrite vsupd_vecs_length.
    apply map_valid_Forall_synced_map_fst; auto.
    safestep.
    erewrite DLog.rep_hashmap_subset.
    cancel.
    auto. auto.
    safestep.
    unfold synced_rep; eauto.
    rewrite vssync_vecs_length, vsupd_vecs_length; eauto.
    rewrite replay_disk_vssync_vsupd_vecs; auto.

    (* crash conditions *)
    xcrash.
    or_r; safecancel; eauto.

    xcrash.
    or_l; safecancel; eauto.
    rewrite replay_disk_vssync_vsupd_vecs.
    or_r; unfold synced_rep; cancel.

    xcrash.
    or_r; safecancel.
    unfold synced_rep; cancel.
    rewrite DLog.rep_hashmap_subset; eauto.
    eauto.
    rewrite vsupd_vecs_length; eauto.
    eapply length_eq_map_valid; eauto.
    rewrite vsupd_vecs_length; auto.
    erewrite <- LogReplay.replay_disk_vsupd_vecs; eauto.

    xcrash.
    or_r; safecancel.
    unfold synced_rep; cancel.
    rewrite DLog.rep_hashmap_subset; eauto.
    eauto.
    rewrite vsupd_vecs_length; eauto.
    eapply length_eq_map_valid; eauto.
    rewrite vsupd_vecs_length; auto.
    erewrite <- LogReplay.replay_disk_vsupd_vecs; eauto.

    Unshelve. all: eauto.
  Qed.
  Proof.
    unfold flush; intros.

    (* Be careful: only unfold rep in the preconditon,
       otherwise the goal will get messy as there are too many
       disjuctions in post/crash conditons *)
    prestep.
    unfold rep at 1.
    cancel.
    step.
    cancel.
    or_l; cancel.
    unfold rep; cancel.
    unfold map_replay.
    rewrite length_nil with (l:=ents); eauto.

    (* case 1: apply happens *)
    prestep.
    cancel; auto.
    step.
    safestep.
    unfold rep; cancel. auto.
    safestep.
    step.

    (* crashes *)
    xcrash.
    rewrite flushing_recover_after; cancel.
    xcrash.
    rewrite recover_before_either; cancel.

    (* case 2: no apply *)
    prestep.
    unfold rep at 1.
    cancel; auto.
    step.

    (* crashes *)
    xcrash.
    rewrite flushing_recover_after; cancel.

    xcrash.
    unfold would_recover_either, rep.
    eapply pimpl_exists_r; eexists.
    or_l; cancel; eauto.
  Qed.
  Proof.
    unfold dwrite, would_recover_before.
    step.

    (* case 1: apply happens *)
    prestep.
    denote rep as Hx; unfold rep, synced_rep in Hx; destruct_lift Hx.
    norm. cancel. intuition simpl.
    pred_apply; unfold rep, synced_rep; cancel.
    auto.

    unfold rep, synced_rep.
    safestep.
    replace (length _) with (length (replay_disk (Map.elements ms_1) dummy0)).
    eapply list2nmem_inbound; eauto.
    erewrite replay_disk_length.
    erewrite replay_disk_eq_length_eq; eauto.

    step.
    unfold rep, synced_rep; cancel.
    rewrite DLog.rep_hashmap_subset; eauto.
    eauto.
    unfold vsupd; autorewrite with lists; auto.
    apply map_valid_updN; auto.
    unfold vsupd, map_replay.
    rewrite replay_disk_updN_comm.
    denote (replay_disk _ _ = replay_disk _ _) as Hreplay.
    rewrite Hreplay.
    f_equal. f_equal. f_equal.
    erewrite <- replay_disk_selN_other at 1.
    erewrite list2nmem_sel with (x := (vs_cur, vs_old)).
    erewrite <- Hreplay; eauto.
    eauto.
    intuition. denote In as HIn.
    apply In_map_fst_MapIn in HIn.
    eapply map_empty_not_In; eauto.
    replace (Map.elements _) with (@nil (addr * valu)).
    auto.
    symmetry; apply MapProperties.elements_Empty; auto.
    eapply list2nmem_updN; eauto.

    (* crashes for case 1 *)
    norm'l.
    xcrash.
    or_r; cancel.
    xform_normr; cancel.
    unfold rep, synced_rep, unsync_rep, map_replay.
    xform_normr; cancel; eauto.
    erewrite DLog.rep_hashmap_subset; eauto.
    rewrite vsupd_length; eauto.
    eapply length_eq_map_valid; eauto.
    apply vsupd_length.
    unfold vsupd, map_replay.
    rewrite replay_disk_updN_comm.
    denote (replay_disk _ _ = replay_disk _ _) as Hreplay.
    rewrite Hreplay.
    f_equal. f_equal. f_equal.
    erewrite <- replay_disk_selN_other at 1.
    erewrite list2nmem_sel with (x := (vs_cur, vs_old)).
    erewrite <- Hreplay; eauto.
    eauto.
    intuition. denote In as HIn.
    apply In_map_fst_MapIn in HIn.
    eapply map_empty_not_In; eauto.
    replace (Map.elements _) with (@nil (addr * valu)).
    auto.
    symmetry; apply MapProperties.elements_Empty; auto.
    eapply list2nmem_updN; eauto.

    xcrash.
    or_l; cancel.
    xform; cancel.
    xform_normr.
    norm. cancel.
    intuition simpl; pred_apply.
    unfold would_recover_before.
    denote map_replay as Hd. rewrite <- Hd; cancel.
    or_l; cancel.
    or_r; cancel.

    (* case 2: no apply *)
    denote (rep _ _ _) as Hx.
    unfold rep, synced_rep, map_replay in Hx; destruct_lift Hx.
    step.
    erewrite <- replay_disk_length.
    eapply list2nmem_inbound; eauto.

    step.
    unfold rep, synced_rep, map_replay; cancel.
    erewrite DLog.rep_hashmap_subset; eauto.
    eauto.
    unfold vsupd; autorewrite with lists; auto.
    apply map_valid_updN; auto.
    unfold eqlen, vsupd; autorewrite with lists; auto.
    eapply replay_disk_updN_eq_not_in; eauto.
    eapply list2nmem_updN; eauto.

    (* crashes for case 2 *)
    xcrash.
    or_r; cancel.
    xform_normr; cancel.
    unfold rep, synced_rep, unsync_rep, map_replay.
    xform_normr; cancel; eauto.
    erewrite DLog.rep_hashmap_subset; eauto.
    rewrite vsupd_length; eauto.
    eapply length_eq_map_valid; eauto.
    apply vsupd_length.
    eapply replay_disk_updN_eq_not_in; eauto.
    eapply list2nmem_updN; eauto.

    Unshelve. all: eauto. exact (Synced 0 nil).
  Qed.
  Proof.
    unfold dsync.
    step.
    step.
    subst; erewrite <- replay_disk_length.
    eapply list2nmem_inbound; eauto.
    step.

    step.
    rewrite DLog.rep_hashmap_subset; eauto.
    unfold vssync; autorewrite with lists; auto.
    apply map_valid_updN; auto.
    setoid_rewrite <- replay_disk_vssync_comm.
    unfold vssync.
    erewrite <- list2nmem_sel; eauto; simpl.
    eapply list2nmem_updN; eauto.
    setoid_rewrite replay_disk_vssync_comm.
    auto.

    (* crashes *)
    all: rewrite DLog.rep_hashmap_subset; eauto.
  Qed.
  Proof.
    intros.
    eapply map_valid_equal; eauto.
    eapply length_eq_map_valid; eauto.
    rewrite synced_list_length.
    erewrite <- possible_crash_list_length; eauto.
  Qed.
  Proof.
    unfold equal_unless_in, possible_crash_list, synced_list.
    intros; simpl in *; autorewrite with lists in *; intuition.
    destruct (lt_dec i (length b)).

    destruct (H4 i l0).
    rewrite <- H0.
    rewrite <- H3 by auto.
    rewrite selN_combine; simplen.

    contradict H0.
    rewrite <- H3 by auto.
    rewrite selN_combine by simplen; simpl.
    rewrite repeat_selN; simplen.
    repeat rewrite selN_oob; simplen.
  Qed.
  Proof.
    unfold equal_unless_in, synced_list; intuition; simpl in *.
    simplen.
    destruct (lt_dec a0 (length d)).
    destruct (Nat.eq_dec a a0); simplen.
    repeat rewrite selN_updN_ne by auto.
    rewrite <- H2; simplen; tauto.
    repeat rewrite selN_oob; simplen.
  Qed.
  Proof.
    unfold equal_unless_in; firstorder.
  Qed.
  Proof.
    unfold equal_unless_in; firstorder.
  Qed.
  Proof.
    induction l; intuition; simpl.
    eapply list_selN_ext; intros.
    simplen.
    apply H0; auto.

    inversion H; simpl in *; subst.
    eapply IHl; auto.
    eapply equal_unless_in_updN; eauto.
  Qed.
  Proof.
    intros.
    eapply equal_unless_in_replay_disk'; eauto.
    apply equal_unless_in_sym; auto.
  Qed.
  Proof.
    induction ents; simpl; intros.
    eapply list2nmem_crash_xform; eauto.
    inversion H; destruct a; simpl in *; subst.
    rewrite synced_list_updN.
    eapply IHents; eauto.
    apply possible_crash_list_updN; auto.
  Qed.
  Proof.
    induction ents; simpl; intros.
    erewrite <- crash_xform_list2nmem_list_eq; eauto.
    destruct a; simpl in *.
    rewrite synced_list_updN.
    eapply IHents; eauto.
    apply possible_crash_list_updN; auto.
  Qed.
  Proof.
      intros.
      eapply map_valid_equal.
      apply MapFacts.Equal_sym.
      apply replay_mem_app; auto.
      apply MapFacts.Equal_refl.
      apply map_valid_replay_mem'.
      destruct H2; split; intros; auto.
      specialize (H3 _ _ H4); destruct H3.
      simplen.
      eapply map_valid_equal; eauto.
      unfold map_valid; intros.
      destruct (H0 _ _ H3); simplen.
  Qed.
  Proof.
    unfold vsmerge; simpl in *; intuition simpl in *; subst.
    left; auto.
    right.
    eapply incl_tran; eauto.
    apply incl_refl.
  Qed.
  Proof.
    unfold possible_crash; intuition.
    specialize (H0 a).
    destruct (listupd_sel_cases (vsupd_vecs l avl) a st m ($0, nil)).
    denote listupd as Hx; destruct Hx as [Hx Heq]; rewrite Heq; intuition.

    intuition; denote listupd as Hx; rewrite Hx.
    eapply arrayN_selN_subset with (a := a) (def := ($0, nil)) in H;
    repeat deex; try congruence.
    erewrite <- vsupd_vecs_length; eauto.

    eapply arrayN_selN_subset with (a := a) (def := ($0, nil)) in H; auto.
    right; repeat deex; repeat eexists; eauto.
    replace vs0 with vs in * by congruence.
    apply vsupd_vecs_selN_vsmerge_in; auto.
    eapply in_vsmerge_incl_trans; eauto.
    erewrite <- vsupd_vecs_length; eauto.
  Qed.
  Proof.
    intros.
    rewrite BUFCACHE.crash_xform_rep.
    unfold rep, map_replay, synced_rep; xform_norm.
    cancel; xform_normr.
    rewrite <- BUFCACHE.crash_xform_rep_r.
    cancel.

    eassign (listupd raw (DataStart xp) (vsupd_vecs d avl)).
    denote arrayN as Ha; eapply arrayN_listupd_subset with (l := (vsupd_vecs d avl)) in Ha.

    pred_apply; cancel.
    eauto.
    rewrite vsupd_vecs_length; auto.
    apply map_valid_vsupd_vecs; auto.
    rewrite replay_disk_vsupd_vecs_nonoverlap.
    repeat rewrite vsupd_vecs_length; auto.
    apply not_true_is_false; auto.
    repeat rewrite vsupd_vecs_length; auto.
    erewrite <- firstn_skipn with (l := avl) (n := n).
    rewrite vsupd_vecs_app.
    eapply possible_crash_vsupd_vecs_listupd; eauto.
  Qed.
  Proof.
    intros.
    eapply dwrite_vecs_xcrash_ok; eauto.
    rewrite overlap_empty; auto.
    apply map_valid_empty; auto.
  Qed.
  Proof.
    unfold rep, synced_rep, unsync_rep, map_replay; intros.
    xform_norml.
    - rewrite DLog.xform_rep_synced.
      rewrite crash_xform_arrayN_subset.
      cancel; eauto. simplen.
      eapply length_eq_map_valid; eauto. simplen.

      eapply list2nmem_replay_disk_crash_xform; eauto.
      erewrite <- equal_unless_in_replay_disk; eauto.
      unfold diskIs; auto.

    - rewrite DLog.xform_rep_truncated.
      rewrite crash_xform_arrayN_subset.
      cancel; eauto; try solve [simplen].

      eapply length_eq_map_valid; eauto; simplen.
      eapply list2nmem_replay_disk_crash_xform; eauto.
      rewrite replay_disk_twice; auto.
      unfold diskIs; auto.

      apply MapFacts.Equal_refl.
      apply map_valid_map0.
      eapply list2nmem_replay_disk_crash_xform; eauto.
      unfold diskIs; cbn; auto.
  Qed.
  Proof.
    intros.
    rewrite synced_applying.
    xform_norm.
    rewrite crash_xform_applying; cancel.
  Qed.
  Proof.
    intros.
    rewrite crash_xform_applying; eauto.
    norml; unfold stars; simpl.
    rewrite synced_applying; cancel.
  Qed.
  Proof.
    unfold rep, synced_rep, unsync_rep, map_replay; intros.
    xform_norml.

    - rewrite crash_xform_arrayN_subset.
      rewrite DLog.xform_rep_synced.
      cancel.
      or_l; cancel; eauto; try solve [simplen].
      or_l; cancel.
      eapply list2nmem_replay_disk_crash_xform; eauto; easy.
      eapply length_eq_map_valid; eauto; simplen.

    - rewrite crash_xform_arrayN_subset.
      rewrite DLog.xform_rep_extended.
      cancel.

      or_l; cancel; eauto; try solve [simplen].
      or_l; cancel.
      eapply list2nmem_replay_disk_crash_xform; eauto; easy.
      eapply length_eq_map_valid; eauto; simplen.

      or_l; cancel; eauto; try solve [simplen].
      or_r; cancel.
      eassign (replay_mem (Map.elements ms ++ ents) vmap0).
      erewrite replay_disk_replay_mem; auto.
      rewrite replay_mem_app'.
      eapply list2nmem_replay_disk_crash_xform; eauto; easy.
      rewrite replay_mem_app'.
      symmetry.
      apply replay_mem_app; auto.
      eapply map_valid_replay_mem_synced_list.
      eassign x0.
      3: apply MapFacts.Equal_refl.
      rewrite replay_mem_app'.
      eapply map_valid_replay_mem'; eauto.
      eapply log_valid_replay; eauto.
      auto.

      or_r; cancel; eauto; try solve [simplen].
      eapply length_eq_map_valid; eauto; simplen.
      eapply list2nmem_replay_disk_crash_xform; eauto; easy.
  Qed.
  Proof.
    unfold rep, synced_rep, map_replay; intros.
    xform_norml.
    rewrite DLog.xform_rep_recovering, crash_xform_arrayN_subset.
    cancel.
    or_r; cancel; eauto; try solve [simplen].
    eapply length_eq_map_valid; eauto; simplen.
    eapply list2nmem_replay_disk_crash_xform; eauto; easy.

    or_l; cancel; eauto; try solve [simplen].
    eapply length_eq_map_valid; eauto; simplen.
    eapply list2nmem_replay_disk_crash_xform; eauto; easy.
  Qed.
  Proof.
    unfold rep, synced_rep; intros.
    xform_norm.
    rewrite DLog.xform_rep_rollback, crash_xform_arrayN_subset.
    cancel; eauto; try solve [simplen].
    eapply length_eq_map_valid; eauto; simplen.
    unfold map_replay in *; subst.
    eapply list2nmem_replay_disk_crash_xform; eauto; easy.
  Qed.
  Proof.
    unfold would_recover_before; intros.
    xform_norm.
    rewrite crash_xform_applying; cancel.
    rewrite crash_xform_synced; cancel.
  Qed.
  Proof.
    unfold would_recover_either, recover_either_pred; intros.
    xform_norm.
    rewrite crash_xform_synced by eauto; cancel.
    or_l; cancel.
    or_l; cancel.
    rewrite crash_xform_synced by eauto; cancel.
    or_l; cancel.
    or_r; cancel.
    rewrite crash_xform_flushing by eauto; cancel.
    or_l; cancel.
    or_l; cancel.
    or_l; cancel.
    or_r; cancel.
    rewrite crash_xform_applying by eauto; cancel.
    or_l; cancel.
    or_l; cancel.
    rewrite crash_xform_recovering' by eauto; cancel.
    or_l; cancel.
    or_l; cancel.
  Qed.
  Proof.
    unfold recover_either_pred; intros.
    rewrite crash_xform_recovering'.
    cancel.
    or_l; cancel.
    or_l; cancel.
  Qed.
  Proof.
    unfold recover_either_pred, would_recover_either.
    intros; xform_norm; cancel.
    erewrite rep_rollback_pimpl. cancel.
  Qed.
  Proof.
    intros.
    unfold recover_either_pred.
    xform_norm.

    rewrite crash_xform_synced; cancel.
    or_l; cancel.
    or_l; cancel.
    eapply crash_xform_diskIs_trans; eauto.

    rewrite crash_xform_synced; cancel.
    or_l; cancel.
    or_r; cancel.
    eapply crash_xform_diskIs_trans; eauto.

    rewrite crash_xform_rollback; cancel.
    or_r; cancel.
    eapply crash_xform_diskIs_trans; eauto.
  Qed.
  Proof.
    unfold recover, recover_either_pred, rep.
    prestep. norm'l. unfold stars; cbn.
    denote or as Hx. apply sep_star_or_distr in Hx.
    destruct Hx; destruct_lift H;
    denote (Map.Equal _ _) as Heq.
    safecancel. eassign F_. cancel. or_l; cancel.
    unfold synced_rep; auto. auto.

    denote or as Hx. apply sep_star_or_distr in Hx.
    destruct Hx; destruct_lift H.

    (* Synced, case 1: We crashed to the old disk. *)
    prestep. norm. cancel.
    intuition simpl; auto. pred_apply; cancel.
    prestep. norm. cancel.
    intuition simpl; auto.
    pred_apply. cancel.
    or_l; cancel.
    rewrite <- Heq; auto.
    rewrite <- Heq; auto.
    cancel.
    xcrash; eauto.
    rewrite DLog.rep_synced_pimpl; cancel.
    or_l; cancel.

    (* Synced, case 2: We crashed to the new disk. *)
    prestep. norm. cancel.
    intuition simpl; auto. pred_apply; cancel.
    prestep. norm. cancel.
    intuition simpl; auto. pred_apply; cancel.
    or_r; cancel.
    rewrite <- Heq; auto.
    rewrite <- Heq; auto.
    norm'l.
    xcrash; eauto.
    rewrite DLog.rep_synced_pimpl; cancel.
    or_r; cancel.
    denote or as Hx. apply sep_star_or_distr in Hx.
    destruct Hx; destruct_lift H.
    xcrash; eauto.
    or_l; cancel.
    xcrash; eauto.
    or_r; cancel.

    (* Rollback *)
    safecancel.
    eassign F_; cancel.
    or_r; cancel.
    unfold synced_rep; auto. auto.
    prestep. norm. cancel.
    intuition simpl; auto. pred_apply; cancel.
    prestep. norm. cancel.
    intuition simpl; auto.
    pred_apply. cancel.
    or_l; cancel.
    rewrite <- Heq; auto.
    rewrite <- Heq; auto.
    norm'l.
    xcrash; eauto.
    rewrite DLog.rep_synced_pimpl; cancel.
    or_l; cancel.
    xcrash; eauto.
    or_l; cancel.

    Unshelve. exact valu. all: eauto. all: econstructor; eauto.
  Qed.
  Proof.
    unfold dwrite_vecs, would_recover_before.
    step.

    (* case 1: apply happens *)
    step.
    prestep.
    unfold rep at 1.
    unfold synced_rep, map_replay in *.
    cancel; auto.
    erewrite <- replay_disk_length.
    eauto.

    step.
    unfold rep, synced_rep, map_replay; cancel.
    rewrite DLog.rep_hashmap_subset; eauto.
    eauto.
    rewrite vsupd_vecs_length; auto.
    apply map_valid_vsupd_vecs; auto.
    repeat rewrite replay_disk_empty; auto.

    (* crashes for case 1 *)
    norm'l. unfold stars; cbn.
    xcrash.
    or_r.
    rewrite dwrite_vecs_xcrash_ok_empty; eauto.
    xform_norm; cancel.
    xform_normr; cancel.
    eassign x2; eassign (x1_1, x1_2); eauto.
    pred_apply; eauto.
    pred_apply; rewrite firstn_oob; eauto.
    erewrite DLog.rep_hashmap_subset; eauto.

    xcrash.
    or_l; cancel.
    xform_normr; cancel.

    (* case 2: no apply *)
    denote rep as Hx; unfold rep, synced_rep, map_replay in Hx.
    destruct_lift Hx.
    step.
    erewrite <- replay_disk_length; eauto.

    step.
    unfold rep, synced_rep, map_replay; cancel.
    erewrite DLog.rep_hashmap_subset; eauto.
    eauto.
    rewrite vsupd_vecs_length; auto.
    apply map_valid_vsupd_vecs; auto.
    apply replay_disk_vsupd_vecs_nonoverlap; auto.
    apply not_true_is_false; auto.

    (* crashes for case 2 *)
    xcrash.
    or_r.
    rewrite dwrite_vecs_xcrash_ok; eauto.
    xform_norm; cancel.
    xform_normr; cancel.
    eassign x2; eassign (x1_1, x1_2); eauto.
    pred_apply; eauto.
    pred_apply; rewrite firstn_oob; eauto.
    erewrite DLog.rep_hashmap_subset; eauto.
  Qed.
  Proof.
    unfold dsync_vecs, rep, synced_rep, map_replay.
    step.
    subst; erewrite <- replay_disk_length; eauto.

    step.
    erewrite DLog.rep_hashmap_subset; eauto.
    rewrite vssync_vecs_length; auto.
    apply map_valid_vssync_vecs; auto.
    apply replay_disk_vssync_vecs_comm.
    erewrite DLog.rep_hashmap_subset; eauto.
  Qed.