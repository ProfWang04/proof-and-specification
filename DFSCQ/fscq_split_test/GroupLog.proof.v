  Proof.
    destruct ms as [m c]; destruct m.
    destruct ms' as [m' c']; destruct m'.
    unfold MLog.readOnly, readOnly; simpl; congruence.
  Qed.
  Proof.
    unfold rep; destruct st; intros; eauto.
  Qed.
  Proof.
    unfold would_recover_any; intros; auto.
  Qed.
  Proof.
    unfold effective; intros.
    rewrite nthd_popn; auto.
  Qed.
  Proof.
    unfold effective; intros.
    rewrite latest_popn; auto.
  Qed.
  Proof.
    unfold effective; intros.
    rewrite length_popn.
    omega.
  Qed.
  Proof.
    unfold effective; intros.
    rewrite length_popn.
    omega.
  Qed.
  Proof.
    unfold would_recover_any, rep.
    intros. norm.
    cancel.
    rewrite nthd_effective, Nat.add_0_r.
    apply MLog.synced_recover_either.
    intuition.
  Qed.
  Proof.
    unfold rep.
    intros. norm.
    cancel.
    rewrite MLog.rep_synced_pimpl.
    eassign (mk_mstate vmap0 nil (MSMLog ms)).
    cancel.
    intuition simpl; auto.
    unfold vmap_match; simpl; congruence.
    unfold dset_match; intuition.
    apply Forall_nil.
    constructor.
  Qed.
  Proof.
    unfold would_recover_any, rep; intros; cancel.
  Qed.
  Proof.
    unfold would_recover_any, rep; intros.
    norm. unfold stars; simpl.
    rewrite nthd_0; cancel.
    rewrite MLog.rollback_recover_either.
    2: intuition.
    eauto.
    eauto.
  Qed.
  Proof.
    unfold rep; intros.
    cancel.
    rewrite MLog.rep_rollback_pimpl.
    auto.
  Qed.
  Proof.
    unfold rep; intros.
    destruct st; cancel.
    erewrite MLog.rep_hashmap_subset; eauto.
    erewrite MLog.would_recover_either_hashmap_subset; eauto.
    erewrite MLog.rep_hashmap_subset; eauto.
    erewrite MLog.rep_hashmap_subset; eauto.
  Qed.
  Proof.
    intros.
    apply list2nmem_ptsto_bound in H0.
    erewrite <- replay_seq_latest_length; auto.
    apply H.
  Qed.
  Proof.
    unfold vmap_match, dset_match.
    intros ds ts; destruct ds; revert l.
    induction ts; intuition; simpl in *;
      denote ReplaySeq as Hs;inversion Hs; subst; simpl.
    denote ptsto as Hx; rewrite singular_latest in Hx by easy; simpl in Hx.
    erewrite surjective_pairing at 1.
    erewrite <- list2nmem_sel; eauto; simpl; auto.

    rewrite H0 in H1.
    eapply IHts.
    split; eauto.
    eapply Forall_cons2; eauto.

    apply MapFacts.Equal_refl.
    eapply replay_mem_find_none_mono; eauto.

    rewrite latest_cons in *.
    eapply ptsto_replay_disk_not_in'; [ | | eauto].
    eapply map_find_replay_mem_not_in; eauto.
    denote Forall as Hx; apply Forall_inv in Hx; apply Hx.
  Qed.
  Proof.
    induction 1; simpl in *; intuition.
    rewrite latest_cons; subst.
    unfold latest in *; simpl in *.
    rewrite <- IHReplaySeq by (eapply Forall_cons2; eauto).
    rewrite replay_disk_replay_mem; auto.
    inversion H1; subst.
    eapply log_valid_length_eq.
    unfold ents_valid in *; intuition; eauto.
    rewrite replay_disk_length; auto.
  Qed.
  Proof.
    unfold vmap_match, dset_match; intuition.
    eapply replay_disk_eq; eauto.
    eexists; rewrite H0.
    erewrite replay_seq_replay_mem; eauto.
  Qed.
  Proof.
    unfold dset_match, pushd, ents_valid; intuition; simpl in *.
    apply Forall_cons; auto; split; auto.
    eapply log_valid_length_eq; eauto.
    erewrite replay_seq_latest_length; eauto.
    constructor; auto.
  Qed.
  Proof.
      unfold vmap_match; simpl; apply MapFacts.Equal_refl.
  Qed.
  Proof.
      unfold dset_match; split; [ apply Forall_nil | constructor ].
  Qed.
  Proof.
    intros.
    erewrite replay_seq_length; eauto.
    apply H.
  Qed.
  Proof.
    unfold dset_match, ents_valid; intuition; simpl in *.
    destruct (lt_dec i (length ts)).
    eapply Forall_selN with (i := i) in H0; intuition.
    eapply log_valid_length_eq; eauto.
    erewrite replay_seq_nthd_length; eauto.
    rewrite selN_oob by omega.
    unfold log_valid, KNoDup; intuition; inversion H.
  Qed.
  Proof.
    induction ts; intros; simpl.
    unfold vmap_match in *; simpl in *.
    rewrite H in H0.
    unfold KIn in H0.
    apply InA_nil in H0; intuition.

    destruct (in_dec Nat_as_OT.eq_dec a0 (map fst a)).
    (* The address was written by the newest transaction. *)
    exists a; intuition.

    unfold vmap_match in *; simpl in *.
    remember (fold_right replay_mem vmap0 ts) as vmap_ts.
    destruct (in_dec Nat_as_OT.eq_dec a0 (map fst (Map.elements vmap_ts))).
    (* The address was written by an older transaction. *)
    replace a0 with (fst (a0, v)) in * by auto.
    apply In_fst_KIn in i.
    eapply IHts in i.
    deex.
    exists t; intuition.
    congruence.
    eapply Forall_cons2; eauto.
    rewrite Forall_forall in H1.
    specialize (H1 a).
    simpl in *; intuition.

    (* The address wasn't written by an older transaction. *)
    denote KIn as HKIn.
    apply KIn_fst_In in HKIn.
    apply In_map_fst_MapIn in HKIn.
    apply In_MapsTo in HKIn.
    deex.
    eapply replay_mem_not_in' in H1.
    denote (Map.MapsTo) as Hmap.
    eapply MapsTo_In in Hmap.
    eapply In_map_fst_MapIn in Hmap.
    apply n0 in Hmap; intuition.
    auto.
    rewrite <- H.
    eauto.
  Qed.
  Proof.
    intros.

    assert (HNoDup: Forall (@KNoDup valu) ts).
      unfold dset_match in *; simpl in *; intuition.
      unfold ents_valid, log_valid in *.
      eapply Forall_impl; try eassumption.
      intros; simpl; intuition.
      intuition.

    unfold log_valid; intuition;
    eapply vmap_match_find in H; eauto.
    deex.
    denote In as HIn.
    unfold dset_match in *; intuition.
    rewrite Forall_forall in H.
    eapply H in H3.
    unfold ents_valid, log_valid in *; intuition.
    replace 0 with (fst (0, v)) in * by auto.
    apply In_fst_KIn in HIn.
    apply H5 in HIn; intuition.

    deex.
    denote In as HIn.
    unfold dset_match in *; intuition.
    rewrite Forall_forall in H.
    eapply H in H2.
    unfold ents_valid, log_valid in *; intuition.
    replace a with (fst (a, v)) in * by auto.
    apply In_fst_KIn in HIn.
    apply H5 in HIn; intuition.
  Qed.
  Proof.
    unfold dset_match, ents_valid; intuition.
    destruct (lt_dec i (length ts)).
    eapply Forall_selN with (i := i) (def := nil) in H1; intuition.
    eapply le_not_gt; eauto.
    rewrite selN_oob in H; simpl in H; omega.
  Qed.
  Proof.
    unfold ents_valid in *; intros.
    rewrite Forall_forall in *; intuition.
    eapply log_valid_length_eq; eauto.
    apply H; auto.
    apply H; auto.
  Qed.
  Proof.
    unfold dset_match; intuition.
    repeat erewrite replay_seq_nthd; eauto.
    erewrite skipn_sub_S_selN_cons; simpl; eauto.
  Qed.
  Proof.
    intros; simpl in *.
    denote dset_match as Hdset.
    apply dset_match_length in Hdset as Hlength.
    unfold dset_match in *.
    intuition.

    unfold vmap_match in *.
    rewrite H.
    erewrite replay_seq_replay_mem; eauto.
    erewrite nthd_oob; eauto.
    omega.
  Qed.
  Proof.
    intros.
    unfold dset_match; intuition simpl.
    unfold ents_valid.
    apply Forall_forall; intros.
    inversion H3; subst; clear H3.
    split.
    eapply dset_match_log_valid_grouped; eauto.
    setoid_rewrite <- Map.cardinal_1; eauto.

    inversion H4.

    econstructor.
    simpl.
    erewrite dset_match_replay_disk_grouped; eauto.
    erewrite dset_match_length; eauto.
    rewrite nthd_oob; auto.
    constructor.
  Qed.
  Proof. 
    unfold would_recover_any, rep.
    intros; norm'r.
    rewrite <- latest_nthd.
    rewrite latest_effective.
    eassign (mk_mstate vmap0 ts vmap0); simpl.
    cancel.
    apply MLog.recover_before_either.
    intuition simpl; auto.
    rewrite cuttail_length; omega.
  Qed.
  Proof. 
    unfold would_recover_any, rep.
    intros; norm'r.
    rewrite nthd_0.
    eassign (mk_mstate vmap0 ts vmap0); simpl.
    rewrite MLog.recover_before_either.
    cancel.
    intuition simpl; auto.
    omega.
  Qed.
  Proof.
    intros.
    rewrite MLog.synced_recover_before.
    eapply recover_before_any; eauto.
  Qed.
  Proof.
    unfold would_recover_any, rep.
    safecancel.
    inversion H1.
    apply nelist_subset_latest.
  Qed.
  Proof.
    unfold would_recover_any, rep.
    safecancel.
    inversion H1.
    apply nelist_subset_latest.
  Qed.
  Proof.
    unfold rep, dset_match; intuition.
    destruct_lift H.
    denote ReplaySeq as Hx.
    apply replay_seq_latest_length in Hx; simpl in Hx; rewrite <- Hx.
    rewrite latest_effective; auto.
  Qed.
  Proof.
    unfold rep; intros.
    norml; unfold stars; simpl.
    assert (MSTxns ms = nil) as Heq.
    apply dset_match_length in H2; simpl in H2.
    apply length_nil; auto.
    rewrite Heq in *; cancel.
    rewrite nthd_0, Nat.sub_0_r; simpl.
    rewrite latest_nthd; cancel.
    unfold effective.
    rewrite Nat.sub_0_r; simpl.
    rewrite popn_oob; auto.
  Qed.
  Proof.
    unfold init, rep.
    step.
    step.
    apply vmap_match_nil.
    apply dset_match_nil.
  Qed.
  Proof.
    intros.
    rewrite <- nthd_0.
    rewrite nthd_effective.
    rewrite Nat.add_0_r; auto.
  Qed.
  Proof.
    unfold effective; simpl; intros.
    rewrite popn_pushd_comm by omega; auto.
  Qed.
  Proof.
    unfold read, rep.
    prestep.
    cancel.

    (* case 1 : return from vmap *)
    step.
    eapply diskset_vmap_find_ptsto; eauto.
    rewrite latest_effective; eauto.
    pimpl_crash; cancel.

    (* case 2: read from MLog *)
    cancel.
    eexists; apply list2nmem_ptsto_cancel_pair.
    erewrite dset_match_nthd_effective_fst; eauto.
    eapply diskset_ptsto_bound_latest; eauto.
    rewrite latest_effective; eauto.

    step; subst.
    erewrite fst_pair; eauto.
    erewrite dset_match_nthd_effective_fst; eauto.
    eapply diskset_vmap_find_none; eauto.
    rewrite latest_effective; eauto.
    pimpl_crash; cancel.
    eassign (mk_mstate (MSVMap ms_1) (MSTxns ms_1) ms'_1); cancel.
    all: auto.
  Qed.
  Proof.
    unfold submit, rep.
    step.
    step.
    or_r; cancel.
    rewrite nthd_pushd' by omega; eauto.

    unfold vmap_match in *; simpl.
    denote! (Map.Equal _ _) as Heq.
    rewrite Heq; apply MapFacts.Equal_refl.

    rewrite effective_pushd_comm.
    erewrite <- latest_effective.
    apply dset_match_ext; auto.
    rewrite latest_effective; auto.
    step.
    Unshelve. all: try exact vmap0; eauto.
  Qed.
  Proof.
    unfold flushall_nomerge, would_recover_any, rep.
    prestep.
    cancel.

    rewrite nthd_effective, Nat.add_0_r.
    apply sep_star_comm.

    - safestep.
      eapply dset_match_log_valid_selN; eauto.
      safestep.

      (* flush() returns true *)
      erewrite dset_match_nthd_S by eauto; cancel.
      eexists.

      (* flush() returns false, this is impossible *)
      exfalso; eapply dset_match_ent_length_exfalso; eauto.

      (* crashes *)
      subst; repeat xcrash_rewrite.
      xform_norm; cancel.
      xform_normr. safecancel.
      eassign (mk_mstate vmap0 (MSTxns ms_1) vmap0); simpl.
      rewrite selR_inb by eauto; cancel.
      all: simpl; auto; omega.

    - safestep.
      rewrite nthd_oob, latest_effective, nthd_0.
      cancel.
      erewrite <- dset_match_length; eauto.
      apply dset_match_nil.

    - cancel.
      xcrash_rewrite.
      (* manually construct an RHS-like pred, but replace hm'' with hm *)
      instantiate (1 := (exists raw cs, BUFCACHE.rep cs raw *
        [[ (F * exists ms n, 
          [[ dset_match xp (effective ds (length (MSTxns ms))) (MSTxns ms)
            /\ n <= length (MSTxns ms) ]] *
          MLog.would_recover_either xp (nthd n (effective ds (length (MSTxns ms))))
           (selR (MSTxns ms) n nil) hm)%pred raw ]])%pred ).
      xform_norm; cancel.
      xform_normr; safecancel.
      apply MLog.would_recover_either_hashmap_subset.
      all: eauto.
    Unshelve. all: constructor.
  Qed.
  Proof.
    unfold flushall.
    safestep.

    prestep; denote rep as Hx; unfold rep in Hx; destruct_lift Hx.
    cancel.
    erewrite dset_match_nthd_effective_fst; eauto.
    eapply dset_match_log_valid_grouped; eauto.

    prestep; unfold rep; safecancel.
    erewrite dset_match_nthd_effective_fst; eauto.
    erewrite dset_match_replay_disk_grouped; eauto.
    erewrite nthd_oob; eauto.
    rewrite latest_effective, nthd_0; eauto.
    erewrite dset_match_length at 1; eauto.
    apply dset_match_nil.

    denote (length _ > _) as Hf; contradict Hf.
    setoid_rewrite <- Map.cardinal_1; omega.
    apply dset_match_nil.

    xcrash.
    erewrite dset_match_nthd_effective_fst; eauto.
    unfold would_recover_any, rep.
    destruct (MSTxns ms_1);
    norm; unfold stars; simpl.

    unfold vmap_match in *; simpl in *.
    denote (Map.Equal _ vmap0) as Heq.
    rewrite Heq.
    replace (Map.elements _) with (@nil (Map.key * valu)) by auto.
    rewrite nthd_effective.
    eassign (mk_mstate vmap0 nil (MSMLog ms_1)); simpl.
    rewrite Nat.add_0_r, selR_oob by auto.
    cancel.
    intuition.

    eassign (fst (effective ds (S (length t))), latest ds :: nil).
    eassign (mk_mstate vmap0 (Map.elements (MSVMap ms_1) :: nil) (MSMLog ms_1)); simpl.
    rewrite nthd_0.
    unfold selR; simpl; rewrite nthd_0; simpl.
    cancel.

    assert (length (snd ds) > 0).
    denote dset_match as Hx.
    apply dset_match_length in Hx; simpl in Hx.
    rewrite cuttail_length in Hx; omega.
    intuition.
    rewrite <- nthd_0, nthd_effective, Nat.add_0_r.
    apply nelist_subset_nthd_latest; omega.

    unfold effective; simpl; rewrite popn_0.
    replace (S (length t)) with (length (c :: t)) by auto.
    erewrite dset_match_nthd_effective_fst; eauto.
    erewrite <- latest_effective; eauto.
    eapply dset_match_grouped; eauto; simpl.
    rewrite cuttail_length; omega.

    safestep.
    repeat match goal with
              | [ H := ?e |- _ ] => subst H
            end; cancel.
    step.

    Unshelve. all: try exact nil; eauto; try exact vmap0.
  Qed.
  Proof.
    unfold flushall_noop; intros.
    safestep.
    step.
    apply cached_latest_cached.
  Qed.
  Proof.
    unfold flushsync.
    step.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.
    xcrash.
    denote rep as Hx; unfold rep in Hx.
    destruct_lift Hx.
    eapply recover_before_any; eauto.
  Qed.
  Proof.
    unfold flushsync_noop.
    safestep.
    step.
    apply cached_latest_cached.
  Qed.
  Proof.
    unfold ents_valid; intros.
    rewrite Forall_forall in *.
    intros.
    specialize (H _ H1); intuition.
    eapply log_valid_length_eq; eauto.
  Qed.
  Proof.
    unfold vmap_match; induction ts; intros.
    apply Forall_nil.
    constructor; simpl in *.
    eapply map_find_replay_mem_not_in.
    rewrite <- H0; auto.

    eapply IHts.
    2: apply MapFacts.Equal_refl.
    eapply replay_mem_find_none_mono.
    rewrite <- H0; auto.
  Qed.
  Proof.
    unfold dset_match; intuition; simpl in *.
    eapply forall_ents_valid_length_eq; try eassumption.
    apply length_updN.
    apply replay_seq_dsupd_notin; auto.
    eapply vmap_match_notin; eauto.
  Qed.
  Proof.
    induction ts; simpl; auto; intros.
    inversion H; subst.
    constructor; auto.
    split; destruct H2.
    apply log_vaild_filter; eauto.
    eapply le_trans.
    apply filter_length. auto.
  Qed.
  Proof.
    intros; apply forall_ents_valid_ents_filter; auto.
  Qed.
  Proof.
    intros; apply forall_ents_valid_ents_filter; auto.
  Qed.
  Proof.
    unfold dset_match; intuition; simpl in *.
    eapply ents_valid_length_eq.
    2: rewrite length_updN; auto.
    apply forall_ents_valid_ents_remove; auto.
    apply replay_seq_dsupd_ents_remove; auto.
  Qed.
  Proof.
    unfold dset_match; intuition; simpl in *; auto.
    eapply ents_valid_length_eq.
    2: apply eq_sym; apply vssync_vecs_length.
    auto.
    apply replay_seq_dssync_vecs_ents; auto.
  Qed.
  Proof.
    unfold dset_match; intuition; simpl in *.
    eapply forall_ents_valid_length_eq; try eassumption.
    apply length_updN.
    apply replay_seq_dssync_notin; auto.
  Qed.
  Proof.
    unfold effective, dsupd; simpl; intros.
    rewrite map_length.
    apply dmap_popn_comm.
  Qed.
  Proof.
    unfold effective, dsupd_vecs; simpl; intros.
    rewrite map_length.
    apply dmap_popn_comm.
  Qed.
  Proof.
    unfold effective, dssync_vecs; simpl; intros.
    rewrite map_length.
    apply dmap_popn_comm.
  Qed.
  Proof.
    unfold effective, dssync; simpl; intros.
    rewrite map_length.
    apply dmap_popn_comm.
  Qed.
  Proof.
    unfold rep; cancel.
    rewrite nthd_0; simpl.
    rewrite synced_recover_any; auto.
    rewrite effective_dsupd_comm, map_length.
    eapply dset_match_dsupd; eauto.
  Qed.
  Proof.
    unfold rep; cancel.
    rewrite nthd_0; simpl.
    unfold would_recover_any, rep.
    rewrite synced_recover_any; auto.
    rewrite effective_dssync_vecs_comm.
    eapply dset_match_dssync_vecs; eauto.
  Qed.
  Proof.
    unfold rep; cancel.
    rewrite nthd_0; simpl.
    unfold would_recover_any, rep.
    rewrite synced_recover_any; eauto.
  Qed.
  Proof.
    unfold dwrite', rep.
    step.
    erewrite dset_match_nthd_effective_fst; eauto.
    safestep.
    3: eauto.

    erewrite dset_match_nthd_effective_fst; eauto; simpl.
    erewrite dset_match_length, map_length; eauto.
    rewrite dsupd_nthd.
    cancel.
    rewrite effective_dsupd_comm.
    eapply dset_match_dsupd_notin; eauto.

    (* crashes *)
    subst; repeat xcrash_rewrite.
    xform_norm.
    or_l; cancel.
    xform_normr; cancel.
    erewrite dset_match_nthd_effective_fst; eauto.
    rewrite recover_before_any_fst by eauto; cancel.

    or_r; cancel.
    xform_normr; cancel.
    xform_normr; cancel.
    rewrite nthd_0; simpl.
    eassign (mk_mstate vmap0 nil x_1); simpl; cancel.
    all: simpl; eauto.
    apply dset_match_nil.
  Qed.
  Proof.
    intros.
    apply list2nmem_ptsto_bound in H0.
    erewrite dset_match_nthd_effective_fst; eauto.
    erewrite <- replay_seq_latest_length; auto.
    rewrite latest_effective; auto.
    apply H.
  Qed.
  Proof.
    unfold dwrite, rep.
    step.
    prestep; unfold rep; cancel.
    prestep; unfold rep; safecancel.
    substl (MSVMap a0); eauto.
    substl (MSTxns a0); simpl.
    rewrite Nat.sub_0_r, <- latest_nthd.
    simpl; pred_apply; cancel.
    auto.

    step.
    cancel.
    repeat xcrash_rewrite; xform_norm.

    or_l; cancel.
    xform_normr; cancel.

    or_r; cancel.
    do 2 (xform_norm; cancel).
    repeat rewrite nthd_0; simpl.
    substl (MSTxns a0); simpl.
    rewrite Nat.sub_0_r, <- latest_nthd.
    rewrite <- dsupd_latest.
    rewrite synced_recover_any; eauto.

    rewrite effective_dsupd_comm, map_length.
    eapply dset_match_dsupd; eauto.
    cancel.
    repeat xcrash_rewrite; xform_norm.
    or_l; cancel.
    xform_normr; cancel.

    (* 2nd case: no flushall *)
    prestep; unfold rep; cancel.
    apply MapFacts.not_find_in_iff; auto.
    eapply list2nmem_ptsto_cancel_pair.
    eapply diskset_ptsto_bound_effective; eauto.

    prestep. norm. cancel.
    intuition simpl. pred_apply.
    repeat rewrite map_length.
    rewrite <- surjective_pairing in *.
    erewrite dset_match_nthd_effective_fst; eauto.
    erewrite diskset_vmap_find_none; eauto; auto.
    cancel.
    erewrite <- diskset_vmap_find_none with (v := vs_cur).
    erewrite <- dset_match_nthd_effective_fst; eauto.
    all: eauto.
    apply MapFacts.not_find_in_iff; auto.
    rewrite latest_effective; eauto.
    apply MapFacts.not_find_in_iff; auto.
    rewrite latest_effective; eauto.

    cancel.
    repeat xcrash_rewrite; xform_norm.
    or_l; cancel.
    xform_normr; cancel.

    or_r; cancel.
    do 2 (xform_norm; cancel).

    rewrite nthd_0; simpl.
    rewrite <- surjective_pairing in *; simpl.
    rewrite <- dsupd_nthd.
    rewrite MLog.synced_recover_before.
    rewrite dsupd_nthd.
    erewrite dset_match_nthd_effective_fst by eauto.
    rewrite <- dsupd_fst, <- effective_dsupd_comm.
    rewrite recover_before_any_fst.
    erewrite diskset_vmap_find_none; eauto.
    apply MapFacts.not_find_in_iff; auto.
    rewrite latest_effective; eauto.
    rewrite effective_dsupd_comm.
    eapply dset_match_dsupd; eauto.
    rewrite map_length; eauto.
    rewrite map_length; auto.
  Qed.
  Proof.
    unfold dsync.
    prestep; unfold rep; cancel.
    eapply list2nmem_ptsto_cancel_pair.
    eapply diskset_ptsto_bound_effective; eauto.

    prestep; unfold rep; cancel.
    rewrite map_length.
    rewrite dssync_nthd; cancel.
    rewrite effective_dssync_comm.
    eapply dset_match_dssync; eauto.

    cancel.
    rewrite MLog.synced_recover_before.
    erewrite dset_match_nthd_effective_fst; eauto.
    rewrite recover_before_any_fst; eauto.
    Unshelve. eauto.
  Qed.
  Proof.
    unfold vmap_match; induction ts; intros.
    apply Forall_nil.
    rewrite H0 in H; simpl in *.
    constructor; simpl in *.
    eapply nonoverlap_replay_mem_disjoint; eauto.
    eapply IHts.
    2: apply MapFacts.Equal_refl.
    eapply replay_mem_nonoverlap_mono; eauto.
  Qed.
  Proof.
    unfold dset_match; intuition; simpl in *.
    eapply forall_ents_valid_length_eq; try eassumption.
    apply vsupd_vecs_length.
    apply replay_seq_dsupd_vecs_disjoint; auto.
    eapply vmap_match_nonoverlap; eauto.
  Qed.
  Proof.
    unfold dwrite_vecs'.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.
    rewrite map_length.
    rewrite dsupd_vecs_nthd; cancel.
    rewrite effective_dsupd_vecs_comm.
    eapply dset_match_dsupd_vecs_nonoverlap; eauto.

    xcrash.
    or_l; xform_norm; cancel.
    xform_normr; cancel.
    erewrite dset_match_nthd_effective_fst by eauto.
    rewrite recover_before_any_fst by eauto; cancel.

    or_r; xform_norm; cancel.
    xform_normr; cancel.
    rewrite nthd_0.
    repeat erewrite dset_match_nthd_effective_fst by eauto.
    eassign (mk_mstate vmap0 nil x0_1); simpl; cancel.
    all: simpl; eauto.
    apply dset_match_nil.
  Qed.
  Proof.
    intros.
    erewrite dset_match_nthd_effective_fst by eauto.
    rewrite Forall_forall in *; intros.
    erewrite <- replay_seq_latest_length; eauto.
    rewrite latest_effective; eauto.
    unfold dset_match in *; intuition eauto.
  Qed.
  Proof.
    unfold dwrite_vecs, rep.
    step.
    prestep; unfold rep; cancel.
    prestep; unfold rep; safecancel.
    substl (MSVMap a).
    apply overlap_empty; apply map_empty_vmap0.
    eapply effective_avl_addrs_ok; eauto.
    auto.

    step.
    cancel.
    repeat xcrash_rewrite; xform_norm.

    or_l; cancel.
    xform_normr; cancel.

    or_r; cancel.
    do 2 (xform_norm; cancel).
    repeat rewrite nthd_0; simpl.
    substl (MSTxns a); simpl.
    rewrite Nat.sub_0_r, <- latest_nthd.
    rewrite <- dsupd_vecs_latest.
    rewrite synced_recover_any; eauto.
    eassign (MSTxns a); substl (MSTxns a); simpl.
    unfold effective; rewrite popn_oob by omega.
    apply dset_match_nil.

    cancel.
    repeat xcrash_rewrite; xform_norm.
    or_l; cancel.
    xform_normr; cancel.

    prestep; unfold rep; cancel.
    apply not_true_iff_false; auto.
    eapply effective_avl_addrs_ok; eauto.

    step.
    cancel.
    repeat xcrash_rewrite; xform_norm.
    or_l; cancel.
    xform_normr; cancel.

    or_r; cancel.
    do 2 (xform_norm; cancel).
    repeat rewrite nthd_0; simpl.
    erewrite dset_match_nthd_effective_fst by eauto.
    rewrite <- dsupd_vecs_fst, <- effective_dsupd_vecs_comm.
    rewrite MLog.synced_recover_before.
    rewrite recover_before_any_fst.
    auto.

    rewrite effective_dsupd_vecs_comm.
    eapply dset_match_dsupd_vecs_nonoverlap.
    apply not_true_is_false; eauto.
    all: eauto.
  Qed.
  Proof.
    unfold dsync_vecs.
    prestep; unfold rep; cancel.
    erewrite dset_match_nthd_effective_fst by eauto.
    rewrite Forall_forall in *; intros.
    erewrite <- replay_seq_latest_length; eauto.
    rewrite latest_effective; eauto.
    unfold dset_match in *; intuition eauto.

    prestep; unfold rep; cancel.
    rewrite map_length.
    rewrite dssync_vecs_nthd; cancel.
    rewrite effective_dssync_vecs_comm.
    eapply dset_match_dssync_vecs; eauto.

    cancel.
    erewrite dset_match_nthd_effective_fst by eauto.
    rewrite MLog.synced_recover_before.
    rewrite recover_before_any_fst; eauto.
  Qed.
  Proof.
    unfold recover_any_pred; intros; auto 10.
  Qed.
  Proof.
    unfold effective; intros.
    apply nelist_subset_popn'; auto.
  Qed.
  Proof.
    unfold would_recover_any, recover_any_pred, rep; intros.
    xform_norm.
    rewrite MLog.crash_xform_either.
    erewrite dset_match_length in H3; eauto.
    denote NEListSubset as Hds.
    eapply NEListSubset_effective in Hds.
    eapply nelist_subset_nthd in Hds as Hds'; eauto.
    deex.
    denote nthd as Hnthd.
    unfold MLog.recover_either_pred; xform_norm.

    - norm. cancel.
      eassign (mk_mstate vmap0 nil ms'); eauto.
      or_l; cancel.
      apply dset_match_nil.
      intuition simpl.
      eassumption.
      setoid_rewrite Hnthd; auto.

    - destruct (Nat.eq_dec x0 (length (MSTxns x))) eqn:Hlength; subst.
      norm. cancel.
      or_l; cancel.
      rewrite nthd_0.
      eassign (mk_mstate vmap0 nil ms'); eauto.
      auto.
      apply dset_match_nil.
      eassign n; intuition; simpl.
      setoid_rewrite Hnthd.
      pred_apply.
      rewrite selR_oob by auto; simpl; auto.

      denote (length (snd x1)) as Hlen.
      eapply nelist_subset_nthd with (n':=S x0) in Hds; eauto.
      deex.
      clear Hnthd.
      denote nthd as Hnthd.
      norm. cancel.
      or_l; cancel.
      rewrite nthd_0.
      eassign (mk_mstate vmap0 nil ms'); eauto.
      auto.
      apply dset_match_nil.
      eassign n1.
      unfold selR in *.
      destruct (lt_dec x0 (length (MSTxns x))); intuition.
      pred_apply.
      erewrite dset_match_nthd_S in *; eauto.
      setoid_rewrite Hnthd; auto.
      denote dset_match as Hx.
      apply dset_match_length in Hx; simpl in Hx; omega.
      denote dset_match as Hx. 
      apply dset_match_length in Hx; simpl in Hx; simpl.
      rewrite cuttail_length in *. omega.

    - norm. cancel.
      or_r; cancel.
      eassign (mk_mstate vmap0 nil ms'); eauto.
      auto.
      auto.
      eassign n.
      intuition.
      setoid_rewrite Hnthd.
      pred_apply.
      erewrite nthd_effective, dset_match_length; eauto.
  Qed.
  Proof.
    unfold recover_any_pred, rep; intros.
    xform_norm.
    rewrite MLog.crash_xform_recovering.
    instantiate (1:=nil).
    unfold MLog.recover_either_pred.
    norm.
    unfold stars; simpl.
    or_l; cancel.
    eassign (mk_mstate vmap0 nil ms'); cancel.
    auto.
    apply dset_match_nil.
    intuition simpl; eauto.
    or_l; cancel.
    eassign (mk_mstate vmap0 nil ms'); cancel.
    auto.
    apply dset_match_nil.
    intuition simpl; eauto.
    or_r; cancel.
    eassign (mk_mstate vmap0 nil ms'); cancel.
    auto.
    apply dset_match_nil.
    intuition simpl; eauto.
  Qed.
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite MLog.crash_xform_synced; norm.
    eassign (mk_mstate vmap0 nil ms'); simpl.
    cancel.
    intuition simpl.
    auto.
    apply dset_match_nil.
    pred_apply.
    cancel.
    omega.
  Qed.
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite MLog.crash_xform_rollback.
    cancel.
    eassign (mk_mstate vmap0 nil ms'); eauto.
    all: auto.
  Qed.
  Proof.
    unfold recover_any_pred; intros.
    xform_norm.
    rewrite cached_recover_any; cancel.
    rewrite rollback_recover_any; cancel.
  Qed.
  Proof.
    unfold recover_any_pred, rep; intros.
    xform_norm.
    - rewrite MLog.crash_xform_synced.
      norm.
      eassign (mk_mstate (MSVMap x1) (MSTxns x1) ms'); cancel.
      or_l; cancel.
      replace d' with x in *.
      intuition simpl; eauto.
      apply list2nmem_inj.
      eapply crash_xform_diskIs_eq; eauto.
      intuition.
      erewrite Nat.min_l.
      eassign x0.
      eapply crash_xform_diskIs_trans; eauto.
      auto.

    - rewrite MLog.crash_xform_rollback.
      norm.
      eassign (mk_mstate (MSVMap x1) (MSTxns x1) ms'); cancel.
      or_r; cancel.
      denote (dset_match) as Hdset; inversion Hdset as (_, H').
      inversion H'.
      auto.
      intuition simpl; eauto.
      eapply crash_xform_diskIs_trans; eauto.
  Qed.
  Proof.
    unfold recover, recover_any_pred, rep.
    prestep. norm'l.
    denote or as Hx.
    apply sep_star_or_distr in Hx.
    destruct Hx; destruct_lift H; safecancel.

    (* Cached *)
    unfold MLog.recover_either_pred; cancel.
    rewrite sep_star_or_distr; or_l; cancel.
    eassign F. cancel.
    or_l; cancel. auto.

    safestep. eauto.
    apply dset_match_nil.
    eassumption.
    apply dset_match_nil.
    instantiate (1:=nil); cancel.

    repeat xcrash_rewrite.
    xform_norm.
    cancel.
    xform_norm; cancel.
    xform_norm; cancel.
    rewrite crash_xform_sep_star_dist; cancel.
    xform_norm.
    norm. cancel.
    pred_apply.
    norm. cancel.

    eassign (mk_mstate vmap0 nil x1); eauto.
    intuition simpl; eauto.
    cancel.
    intuition simpl; eauto.

    (* Rollback *)
    unfold MLog.recover_either_pred; cancel.
    rewrite sep_star_or_distr; or_r; cancel.
    auto.

    safestep. eauto.
    apply dset_match_nil.
    eassumption.
    apply dset_match_nil.
    instantiate (1:=nil); cancel.

    repeat xcrash_rewrite.
    xform_norm.
    cancel.
    xform_norm; cancel.
    xform_norm; cancel.
    rewrite crash_xform_sep_star_dist; cancel.
    xform_norm.
    norm. cancel.
    pred_apply.
    norm. cancel.

    eassign (mk_mstate vmap0 nil x1); eauto.
    intuition simpl; eauto.
    cancel.
    intuition simpl; eauto.
  Qed.