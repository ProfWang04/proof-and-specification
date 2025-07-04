Proof.
  apply Map.empty_1.
Qed.
  Proof.
    induction l; intros; simpl; auto.
    rewrite IHl.
    rewrite length_updN; auto.
  Qed.
  Proof.
    induction l; simpl; intuition; simpl in *.
    rewrite updN_comm by auto.
    apply IHl; auto.
  Qed.
  Proof.
    induction l; simpl; intuition; simpl in *.
    rewrite IHl; auto.
    rewrite selN_updN_ne; auto.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    inversion H.
    inversion H0; subst.
    destruct a; intuition; simpl.
    inversion H2; subst.
    rewrite replay_disk_updN_comm by auto.
    rewrite selN_updN_eq; auto.
    erewrite replay_disk_length; auto.
    simpl in *.
    apply IHl; auto.
    rewrite length_updN; auto.
  Qed.
  Proof.
    intros.
    eapply replay_disk_selN_In; eauto.
    apply KNoDup_NoDup; auto.
  Qed.
  Proof.
    intros.
    apply replay_disk_selN_In_KNoDup; auto.
    apply InA_eqke_In.
    apply MapFacts.elements_mapsto_iff; auto.
  Qed.
  Proof.
    intros.
    apply replay_disk_selN_other; auto.
    contradict H.
    erewrite MapFacts.elements_in_iff.
    apply in_map_fst_exists_snd in H; destruct H.
    eexists. apply In_InA; eauto.
  Qed.
  Proof.
    intros.
    eapply list_selN_ext.
    autorewrite with lists; auto.
    intros.
    destruct (eq_nat_dec pos a); subst; autorewrite with lists in *.
    rewrite selN_updN_eq by (autorewrite with lists in *; auto).
    apply replay_disk_selN_MapsTo; auto.
    apply Map.add_1; auto. reflexivity.

    rewrite selN_updN_ne by auto.
    case_eq (Map.find pos ds); intros; autorewrite with lists in *.
    (* [pos] is in the transaction *)
    apply Map.find_2 in H0.
    setoid_rewrite replay_disk_selN_MapsTo at 2; eauto.
    erewrite replay_disk_selN_MapsTo; eauto.
    apply Map.add_2; eauto.
    (* [pos] is not in the transaction *)
    repeat rewrite replay_disk_selN_not_In; auto.
    apply MapFacts.not_find_in_iff; auto.
    apply MapFacts.not_find_in_iff.
    rewrite MapFacts.add_neq_o by auto; auto.
    Unshelve.
    exact ($0, nil).
  Qed.
  Proof.
    intros.
    destruct H0.
    eapply list2nmem_sel with (def := ($0, nil)) in H0 as Hx.
    erewrite replay_disk_selN_MapsTo in Hx.
    inversion Hx; auto.
    apply Map.find_2; auto.
    apply list2nmem_ptsto_bound in H0.
    repeat rewrite replay_disk_length in *; auto.
  Qed.
  Proof.
    intros.
    destruct H0.
    eapply list2nmem_sel in H0 as Hx.
    rewrite Hx.
    rewrite replay_disk_selN_not_In; eauto;
    apply MapFacts.not_find_in_iff; auto.
  Qed.
  Proof.
    intros.
    destruct H.
    apply list2nmem_ptsto_bound in H.
    autorewrite with lists in *; auto.
  Qed.
  Proof.
    intros.
    apply Map.is_empty_2 in H.
    apply MapProperties.elements_Empty in H.
    rewrite H.
    simpl; auto.
  Qed.
  Proof.
    intros; hnf; intro.
    unfold replay_mem.
    rewrite <- Map.fold_1.
    rewrite MapProperties.fold_identity; auto.
  Qed.
  Proof.
    induction l using rev_ind; intros.
    rewrite app_nil_r; simpl.
    rewrite replay_mem_map0; auto.
    rewrite app_assoc.
    setoid_rewrite fold_left_app; simpl.
    rewrite <- IHl; auto.
  Qed.
  Proof.
    induction l2 using rev_ind; intros.
    rewrite app_nil_r; simpl.
    rewrite H; auto.
    rewrite app_assoc.
    setoid_rewrite fold_left_app; simpl.
    rewrite <- IHl2; auto.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    hnf; intro.
    apply IHl.
    apply MapFacts.add_m; auto.
  Qed.
  Proof.
    unfold Proper, respectful; intros; subst.
    apply replay_mem_equal; auto.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    destruct a; simpl.
    rewrite <- IHl.
    apply replay_mem_equal.
    apply map_add_comm.
    contradict H; inversion H0; subst.
    constructor; hnf; simpl; auto.
    contradict H.
    apply InA_cons.
    right; auto.
    inversion H0; auto.
  Qed.
  Proof.
    induction l; intros; simpl; auto.
    destruct a; simpl in *.
    destruct (addr_eq_dec k0 k).
    left; auto.
    right.
    inversion H; subst.
    apply In_map_fst_MapIn in H0.
    rewrite replay_mem_add in H0 by auto.
    apply MapFacts.add_neq_in_iff in H0; auto.
    apply IHl; auto.
    apply In_map_fst_MapIn; auto.
  Qed.
  Proof.
    induction l; intros; simpl; auto.
    destruct a; inversion H; subst; simpl.
    rewrite IHl by auto.
    rewrite replay_disk_updN_comm.
    rewrite <- replay_disk_add.
    f_equal; apply eq_sym.
    apply mapeq_elements.
    apply replay_mem_add; auto.
    contradict H2.
    apply In_fst_KIn; simpl.
    apply In_replay_mem_mem0; auto.
  Qed.
  Proof.
    induction l1; intros; simpl.
    induction l2; simpl; auto.
    inversion H0; subst.
    erewrite mapeq_elements.
    2: apply replay_mem_add; destruct a; auto.
    rewrite replay_disk_add.
    rewrite <- IHl2 by auto.
    apply replay_disk_updN_comm.
    contradict H3.
    apply In_fst_KIn; auto.

    induction l2; destruct a; simpl; auto.
    inversion H; simpl; subst.
    erewrite mapeq_elements.
    2: apply replay_mem_add; auto.
    rewrite replay_disk_add.
    rewrite replay_disk_updN_comm.
    f_equal.

    apply replay_disk_replay_mem0; auto.
    contradict H3.
    apply In_fst_KIn; auto.

    destruct a0; simpl in *.
    inversion H; inversion H0; simpl; subst.
    rewrite replay_disk_updN_comm.
    rewrite IHl2 by auto.
    rewrite <- replay_disk_add.
    f_equal.
    apply eq_sym.
    apply mapeq_elements.
    apply replay_mem_add; auto.
    contradict H7.
    apply In_fst_KIn; simpl; auto.
  Qed.
  Proof.
    intros.
    unfold map_merge.
    setoid_rewrite mapeq_elements at 3.
    2: eapply replay_mem_equal with (m2 := m1); auto.
    rewrite replay_disk_merge' by auto.
    f_equal.
    apply mapeq_elements.
    apply replay_mem_equal.
    apply replay_mem_map0.
  Qed.
  Proof.
    induction l; intros; auto.
    destruct a; simpl in *; intuition.
    apply IHl; auto.
    inversion H; subst; auto.
    rewrite replay_mem_add in H1.
    apply Map.add_3 in H1; auto.
    inversion H; auto.
    inversion H; auto.
  Qed.
  Proof.
    intros.
    eapply replay_mem_not_in'; eauto.
    contradict H0.
    apply In_map_fst_MapIn; auto.
  Qed.
  Proof.
    induction l; intros; auto.
    destruct a; inversion H; simpl; subst.
    rewrite replay_mem_add by auto.
    rewrite IHl by auto.
    setoid_rewrite replay_mem_add; auto.
    apply map_add_repeat.
  Qed.
  Proof.
    unfold map_merge; intros.
    apply map_merge_repeat'; auto.
  Qed.
  Proof.
    unfold map_merge, replay_mem; intros.
    rewrite <- Map.fold_1.
    apply MapProperties.fold_rec_nodep; auto.
    intros.
    rewrite H0.
    apply MapFacts.Equal_mapsto_iff; intros.

    destruct (eq_nat_dec k0 k); subst; split; intros.
    apply MapFacts.add_mapsto_iff in H1; intuition; subst; auto.
    apply MapFacts.add_mapsto_iff; left; intuition.
    eapply MapFacts.MapsTo_fun; eauto.
    eapply Map.add_3; hnf; eauto.
    eapply Map.add_2; hnf; eauto.
  Qed.
  Proof.
    induction l; intros; simpl; auto.
    inversion H.
    destruct a; simpl in *; intuition; subst.
    rewrite updN_twice; auto.
    inversion H0; subst.
    setoid_rewrite <- IHl at 2; eauto.
    rewrite updN_comm; auto.
    contradict H3; subst.
    apply In_fst_KIn; auto.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    destruct a; inversion H; subst; simpl.
    rewrite <- replay_disk_updN_comm.
    rewrite IHl; auto.
    rewrite updN_twice; auto.
    contradict H2.
    apply In_fst_KIn; auto.
  Qed.
  Proof.
    induction l; destruct l'; simpl; intros; subst;
    repeat rewrite replay_disk_length; autorewrite with lists; auto.
    setoid_rewrite <- length_updN.
    eapply IHl; eauto.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    erewrite list2nmem_sel with (x := v); eauto.
    apply list2nmem_ptsto_cancel.
    eapply list2nmem_ptsto_bound; eauto.

    inversion H0; destruct a; subst.
    erewrite list2nmem_sel with (x := v); eauto.
    eapply IHl; simpl; auto.
    rewrite replay_disk_updN_comm, selN_updN_ne.
    apply list2nmem_ptsto_cancel.
    apply list2nmem_ptsto_bound in H1.
    rewrite replay_disk_length, length_updN in *; auto.
    intuition.
    contradict H4.
    apply In_KIn; auto.
    Unshelve. all: eauto.
  Qed.
  Proof.
    intros.
    eapply ptsto_replay_disk_not_in'; eauto.
    contradict H.
    apply In_map_fst_MapIn; auto.
  Qed.
  Proof.
    unfold vsupd; intros.
    rewrite replay_disk_updN_comm.
    repeat f_equal.
    erewrite <- replay_disk_selN_not_In; eauto.
    eapply list2nmem_sel; eauto.
    contradict H.
    apply In_map_fst_MapIn; eauto.
  Qed.
  Proof.
    intros.
    eapply replay_disk_updN_eq_not_in; eauto.
    apply MapFacts.not_find_in_iff.
    rewrite MapFacts.elements_o.
    apply MapProperties.elements_Empty in H.
    rewrite H; auto.
  Qed.
  Proof.
    induction l; simpl; intros; intuition.
    destruct a; subst; simpl.
    destruct (In_dec (eq_nat_dec) n (map fst l)).
    apply IHl; auto.
    rewrite replay_disk_updN_comm by auto.
    destruct (lt_dec n (length d)).
    rewrite selN_updN_eq; auto.
    rewrite replay_disk_length; auto.
    rewrite selN_oob; auto.
    rewrite length_updN, replay_disk_length; omega.
  Qed.
  Proof.
    induction l; simpl; auto; intros.
    rewrite IHl; unfold vssync; destruct a; simpl in *.
    destruct (addr_eq_dec a0 n); subst.
    - repeat rewrite updN_twice.
      destruct (lt_dec n (length d)).
      repeat rewrite selN_updN_eq; auto.
      rewrite selN_oob; repeat rewrite updN_oob; auto; try omega.
    - repeat rewrite selN_updN_ne by auto.
      rewrite updN_comm; auto.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    rewrite <- IHl by auto.
    rewrite replay_disk_vssync_comm_list; auto.
  Qed.
  Proof.
    intros; apply replay_disk_vssync_comm_list.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    rewrite <- IHl by auto.
    rewrite replay_disk_vssync_comm; auto.
  Qed.
  Proof.
    intros.
    apply MapProperties.elements_Empty in H.
    rewrite H; simpl; auto.
  Qed.
  Proof.
    intros.
    eapply list_selN_ext with (default := ($0, nil)); intros.
    repeat rewrite replay_disk_length; rewrite length_updN; auto.
    rewrite replay_disk_updN_comm.

    destruct (Nat.eq_dec pos a); subst.
    rewrite selN_updN_eq; [ apply eq_sym | ].
    eapply list2nmem_sel; eauto.
    rewrite replay_disk_length in *; eauto.

    rewrite selN_updN_ne by auto.
    case_eq (Map.find pos m); intros.
    apply Map.find_2 in H1.
    rewrite replay_disk_length in *.
    repeat erewrite replay_disk_selN_MapsTo; eauto.
    apply Map.remove_2; eauto.

    apply MapFacts.not_find_in_iff in H1.
    setoid_rewrite replay_disk_selN_not_In; auto.
    apply not_in_remove_not_in; auto.

    rewrite In_map_fst_MapIn.
    apply Map.remove_1; now auto.
  Qed.
  Proof.
    intros.
    rewrite replay_disk_updN_comm.
    erewrite <- updN_twice.
    eapply list2nmem_updN.
    rewrite <- replay_disk_updN_comm.
    erewrite <- replay_disk_remove_updN_eq; eauto.

    rewrite In_map_fst_MapIn; apply Map.remove_1; now auto.
    rewrite In_map_fst_MapIn; apply Map.remove_1; now auto.
  Qed.
  Proof.
    intros.
    eapply list_selN_ext with (default := ($0, nil)); intros.
    repeat rewrite replay_disk_length; rewrite length_updN; auto.
    rewrite replay_disk_updN_comm.
    rewrite length_updN in H0.

    destruct (Nat.eq_dec pos a); subst.
    repeat rewrite selN_updN_eq; auto.
    rewrite replay_disk_length in *; eauto.

    repeat rewrite selN_updN_ne by auto.
    rewrite H at 1.
    case_eq (Map.find pos m); intros.
    apply Map.find_2 in H1.
    repeat erewrite replay_disk_selN_MapsTo; eauto.
    apply Map.remove_2; eauto.

    apply MapFacts.not_find_in_iff in H1.
    setoid_rewrite replay_disk_selN_not_In; auto.
    apply not_in_remove_not_in; auto.

    rewrite In_map_fst_MapIn.
    apply Map.remove_1; now auto.
  Qed.
  Proof.
    induction l; simpl; intros.
    rewrite MapFacts.add_eq_o; congruence.
    destruct a; simpl.
    destruct (addr_eq_dec n a0); subst.
    rewrite map_add_repeat.
    apply IHl.
    rewrite map_add_comm by auto.
    apply IHl.
  Qed.
  Proof.
    induction l; intuition; simpl in *.
    eapply IHl; intuition eauto; subst.
    destruct a0; simpl in *.
    contradict H.
    apply replay_mem_add_find_none.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    destruct a; simpl in *.
    destruct (addr_eq_dec n a0); subst.
    contradict H.
    apply replay_mem_add_find_none.
    erewrite <- MapFacts.add_neq_o; eauto.
  Qed.
  Proof.
    induction ents; auto; intros; simpl.
    destruct a; simpl.
    destruct (addr_eq_dec n a0); subst; auto.
    simpl; intuition.
    eapply IHents; eauto.
  Qed.
  Proof.
    induction ents; intros; simpl; auto.
    destruct a; simpl.
    destruct (addr_eq_dec n a0); subst; simpl; auto.
    rewrite <- replay_disk_updN_comm by auto.
    rewrite <- IHents.
    rewrite <- replay_disk_updN_comm by auto.
    rewrite updN_twice; auto.
  Qed.
  Proof.
    unfold map_valid, map0; intuition; exfalso;
    apply MapFacts.empty_mapsto_iff in H; auto.
  Qed.
  Proof.
    unfold map_valid; intros.
    exfalso; eapply map_empty_find_exfalso; eauto.
    apply Map.find_1; eauto.
  Qed.
  Proof.
    unfold map_valid; intros.
    destruct (addr_eq_dec a0 a); subst.
    eauto.
    eapply H.
    eapply Map.add_3; hnf; eauto.
  Qed.
  Proof.
    unfold map_valid; simpl; intuition.
    eapply H; eauto.
    rewrite length_updN.
    eapply H; eauto.
  Qed.
  Proof.
    unfold map_valid; intros.
    erewrite <- H0.
    eapply H.
    eapply Map.remove_3; eauto.
  Qed.
  Proof.
    induction d; unfold map_valid; simpl; intros; split;
    eapply H0; rewrite H; eauto.
  Qed.
  Proof.
    unfold map_valid. intros * Hv Hlen * Hm. split; firstorder.
    specialize (Hv _ _ Hm) as [? ?]. omega.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    apply IHl.
    apply map_valid_updN; auto.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    apply IHl.
    apply map_valid_updN; auto.
  Qed.
  Proof.
    unfold map_valid; intros.
    apply Forall_forall; intros.
    autorewrite with lists.
    destruct x; simpl.
    apply (H n w).
    apply Map.elements_2.
    apply In_InA; auto.
  Qed.
  Proof.
    unfold map_valid; intros.
    apply Forall_forall; intros.
    autorewrite with lists.
    apply In_map_fst_MapIn in H0.
    apply MapFacts.elements_in_iff in H0.
    destruct H0.
    eapply (H x).
    apply Map.elements_2; eauto.
  Qed.
  Proof.
    unfold map_valid; induction d; intros.
    rewrite replay_disk_length; eauto.
    split.
    apply (H a0 v); auto.
    rewrite replay_disk_length.
    apply (H a0 v); auto.
  Qed.
  Proof.
    unfold map_valid; intros.
    destruct (MapFacts.In_dec ms1 a).
    apply MapFacts.in_find_iff in i.
    destruct (Map.find a ms1) eqn:X.
    eapply H.
    apply MapFacts.find_mapsto_iff; eauto.
    tauto.
    eapply H0.
    eapply replay_mem_not_in; eauto.
  Qed.
  Proof.
    unfold map_valid; induction d; intros.
    rewrite replay_disk_length; eauto.
    split.
    apply (H a0 v); auto.
    rewrite replay_disk_length.
    apply (H a0 v); auto.
  Qed.
  Proof.
    unfold log_valid; intuition.
  Qed.
  Proof.
    unfold map_valid, log_valid; intuition;
    apply KIn_exists_elt_InA in H0;
    destruct H0; simpl in H0;
    eapply H; eauto;
    apply Map.elements_2; eauto.
  Qed.
  Proof.
    unfold log_valid, DLog.entries_valid; intuition.
    rewrite Forall_forall.
    intros; destruct x.
    unfold PaddedLog.entry_valid, PaddedLog.addr_valid; intuition.
    eapply H3; eauto; simpl.
    apply In_fst_KIn.
    eapply in_map; eauto.

    simpl; subst.
    rewrite replay_disk_length in *.
    eapply goodSize_trans; [ | apply H].
    apply Nat.lt_le_incl.
    eapply H3.
    apply In_fst_KIn.
    eapply in_map; eauto.
  Qed.
  Proof.
    unfold log_valid; intuition.
    apply KNoDup_filter; eauto.
    edestruct H1; eauto.
    eapply InA_filter; eauto.
    edestruct H1; eauto.
    eapply InA_filter; eauto.
  Qed.
  Proof.
    unfold map_valid, log_valid; intros.
    destruct (InA_dec (@eq_key_dec valu) (a, v) ents).
    eapply H; eauto.
    eapply H0.
    eapply replay_mem_not_in'.
    3: eauto. apply H.
    contradict n.
    apply In_fst_KIn; simpl; auto.
  Qed.
  Proof.
    unfold log_valid, map_valid; intros.
    split; intros.
    apply H0.
    rewrite replay_disk_length in H0.
    eapply H0; eauto.
  Qed.
  Proof.
    unfold log_valid; intuition.
    eapply H2; eauto.
    substl (length d').
    eapply H2; eauto.
  Qed.
  Proof.
    unfold log_valid; induction l; intros; intuition; auto.
    destruct a; inversion H0; subst; simpl.
    rewrite replay_disk_updN_comm.
    rewrite IHl.
    setoid_rewrite mapeq_elements at 2.
    2: apply replay_mem_add; auto.
    rewrite replay_disk_add; auto.
    split; auto; intros.
    eapply H1.
    apply InA_cons_tl; eauto.
    contradict H3.
    apply In_fst_KIn; auto.
  Qed.
  Proof.
    unfold Proper, respectful; intros; subst; split;
    apply map_valid_equal; auto.
    apply MapFacts.Equal_sym; auto.
  Qed.
  Proof.
    unfold Proper, respectful, impl; intros; subst.
    eapply map_valid_equal; eauto.
  Qed.
  Proof.
    unfold Proper, respectful, impl, flip; intros; subst.
    apply MapFacts.Equal_sym in H.
    eapply map_valid_equal; eauto.
  Qed.
  Proof.
    intros.
    eapply log_valid_length_eq; eauto.
    erewrite <- possible_crash_list2nmem_length; eauto.
  Qed.
  Proof.
    induction ents; intros; simpl.
    unfold replay_disk; simpl; auto.
    eapply possible_crash_log_valid in H as H'; eauto.

    apply IHents.
    unfold log_valid in *.
    split.
    unfold KNoDup.
    eapply KNoDup_cons_inv; intuition eauto.
    intros.
    rewrite length_updN.
    eapply H.
    unfold KIn in *.
    eapply InA_cons_tl; eauto.

    repeat erewrite listupd_memupd; eauto.
    eapply possible_crash_upd; auto.
    destruct a; simpl; auto.

    unfold log_valid in *; intuition.
    eapply H2 with (v:=snd a).
    unfold KIn.
    eapply InA_cons_hd.
    unfold Map.eq_key; now eauto.

    unfold log_valid in *; intuition.
    eapply H3 with (v:=snd a).
    unfold KIn.
    eapply InA_cons_hd.
    unfold Map.eq_key; now eauto.
  Qed.
  Proof.
    intros.
    eapply crash_xform_diskIs in H0.
    destruct_lift H0.
    unfold diskIs in *; subst.
    eapply crash_xform_diskIs_r; unfold diskIs; eauto.
    eapply possible_crash_replay_disk; auto.
  Qed.
  Proof.
    induction l; intros; simpl; auto.

    destruct (in_dec eq_nat_dec (fst a) (map fst l));
    denote KNoDup as HKNoDup;
    apply KNoDup_cons_inv in HKNoDup.
    rewrite replay_disk_updN_absorb; auto.
    rewrite replay_disk_updN_absorb; auto.
    rewrite <- IHl; auto.
    unfold vsupd.
    rewrite replay_disk_updN_absorb; auto.

    rewrite vsupd_vecs_vsupd_notin; auto.
    unfold vsupd.
    rewrite updN_twice.
    repeat rewrite replay_disk_updN_comm; auto.
    rewrite IHl; auto.
  Qed.
  Proof.
    induction n; destruct l; simpl; try congruence; firstorder.
    destruct (MapFacts.In_dec m n0); auto.
    rewrite Map.mem_1; auto.
    apply MapFacts.not_mem_in_iff in n1; rewrite n1 in *; auto.
  Qed.
  Proof.
    induction l; intros; simpl.
    inversion H.
    destruct (MapFacts.In_dec ms a); auto.
    rewrite Map.mem_1; auto.
    apply MapFacts.not_mem_in_iff in n as Hx; rewrite Hx in *; auto.
    inversion H; destruct (addr_eq_dec a a0); subst; firstorder.
  Qed.
  Proof.
    induction al; simpl; auto; intros.
    replace (Map.mem a m) with false; eauto.
    symmetry.
    eapply MapFacts.not_mem_in_iff.
    apply map_empty_not_In; auto.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    destruct (MapFacts.In_dec m (fst a)); simpl in *.
    rewrite Map.mem_1 in H; congruence.
    apply MapFacts.not_mem_in_iff in n as Hx; rewrite Hx in *; auto.
    rewrite <- IHl by auto.
    unfold vsupd, vsmerge.
    rewrite replay_disk_updN_comm.
    erewrite replay_disk_selN_not_In; eauto.
    contradict n.
    apply In_map_fst_MapIn; eauto.
  Qed.
  Proof.
    induction l; intros; auto; simpl.
    destruct (Map.mem a m1) eqn:?; destruct (Map.mem a m2) eqn:?; auto.
    rewrite H in Heqb; congruence.
    rewrite H in Heqb; congruence.
  Qed.
  Proof.
    unfold Proper, respectful, impl; intros; subst.
    apply overlap_equal; auto.
  Qed.
  Proof.
    induction al; intuition; simpl in *.
    apply disjoint_nil_l.
    destruct (Map.mem a (replay_mem ents d)) eqn:?; try congruence.
    apply disjoint_cons_l.
    eapply IHal; eauto.
    eapply map_find_replay_mem_not_in.
    rewrite MapFacts.mem_find_b in Heqb.
    destruct (Map.find a (replay_mem ents d)) eqn:?; try congruence.
    eauto.
  Qed.
  Proof.
    induction al; simpl; intros; auto.
    destruct (Map.mem a m) eqn:?; 
    destruct (Map.mem a (replay_mem ents m)) eqn:?; try congruence.
    rewrite MapFacts.mem_find_b in *.
    destruct (Map.find a m) eqn:?; try congruence.
    destruct (Map.find a (replay_mem ents m)) eqn:?; try congruence.
    apply replay_mem_find_none_mono in Heqo0; congruence.
    eapply IHal; eauto.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    destruct (In_dec addr_eq_dec (fst a) (map fst ents)); simpl in *.
    specialize (H (fst a)); simpl in H; intuition.
    rewrite <- IHl.
    unfold vsupd, vsmerge.
    rewrite replay_disk_updN_comm by auto.
    erewrite replay_disk_selN_other; auto.
    unfold disjoint in *; firstorder.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    destruct (In_dec addr_eq_dec a (map fst ents)); simpl in *.
    specialize (H a); simpl in H; intuition.
    rewrite <- IHl.
    unfold vssync, vsmerge.
    rewrite replay_disk_updN_comm by auto.
    erewrite replay_disk_selN_other; auto.
    unfold disjoint in *; firstorder.
  Qed.