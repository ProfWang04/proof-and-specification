  Proof.
    unfold items_valid; intuition.
    rewrite length_updN; auto.
    apply Forall_wellformed_updN; auto.
  Qed.
  Proof.
    unfold items_valid; intuition.
    eapply synced_list_ipack_length_ok; eauto.
  Qed.
  Proof.
    unfold items_valid; intuition.
    eapply ipack_length_eq; eauto.
  Qed.
  Proof.
    unfold get, rep.
    safestep.
    cbv [BFILE.datatype]; cancel.

    (* [rewrite selN_val2block_equiv] somewhere *)
    rewrite synced_list_length, ipack_length.
    apply div_lt_divup; auto.
    subst; rewrite synced_list_selN; simpl.

    safestep; msalloc_eq.
    erewrite selN_val2block_equiv.
    apply ipack_selN_divmod; auto.
    apply list_chunk_wellformed; auto.
    unfold items_valid in *; intuition; auto.
    apply Nat.mod_upper_bound; auto.
    cancel.
  Qed.
  Proof.
    unfold put, rep.
    hoare; subst.

    (* [rewrite block2val_updN_val2block_equiv] somewhere *)

    rewrite synced_list_length, ipack_length; apply div_lt_divup; auto.
    rewrite synced_list_length, ipack_length; apply div_lt_divup; auto.
    msalloc_eq. cancel.
    unfold items_valid in *; intuition auto.

    destruct (r_). cancel.

    apply arrayN_unify.
    rewrite synced_list_selN, synced_list_updN; f_equal; simpl.
    rewrite block2val_updN_val2block_equiv.
    apply ipack_updN_divmod; auto.
    apply list_chunk_wellformed.
    unfold items_valid in *; intuition; auto.
    apply Nat.mod_upper_bound; auto.

    apply items_valid_updN; auto.
    unfold items_valid, RALen in *; simpl; intuition.
    rewrite length_updN; auto.
  Qed.
  Proof.
    intros.
    unfold items_valid, RALen in *; intuition.
    erewrite ipack_app, synced_list_app by eauto.
    rewrite arrayN_app, Nat.add_0_l; cancel.
    rewrite synced_list_length, ipack_length.
    substl (length items); rewrite divup_mul; auto.
    assert (length (synced_list (ipack (updN block0 O e))) = 1).
    rewrite synced_list_length, ipack_length.
    rewrite block0_repeat, length_updN, repeat_length, divup_same; auto.

    rewrite arrayN_ptsto_selN_0; auto.
    rewrite synced_list_selN; unfold ipack.
    erewrite selN_map, list_chunk_spec; simpl.
    rewrite setlen_exact; eauto.
    rewrite length_updN, block0_repeat, repeat_length; auto.
    setoid_rewrite list_chunk_length.
    rewrite length_updN, block0_repeat, repeat_length, divup_same; auto.
    Unshelve. exact $0.
  Qed.
  Proof.
    unfold items_valid, RALen in *; intuition; simpl.
    repeat rewrite app_length; simpl.
    rewrite block0_repeat, length_updN, repeat_length.
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l; omega.
    apply Forall_append; auto.
    apply Forall_updN; auto.
    rewrite block0_repeat.
    apply Forall_repeat.
    apply item0_wellformed.
  Qed.
  Proof.
    unfold extend, rep.
    prestep. norm. cancel. intuition. eauto. eauto. eauto.
    safestep.

    or_l; safecancel.
    or_r. norm; [ cancel | intuition eauto ].
    simpl; pred_apply; norm; [ | intuition ].
    cancel; apply extend_ok_helper; auto.
    apply extend_item_valid; auto.
  Qed.
  Proof.
    unfold readall, rep.
    safestep.
    step; msalloc_eq.

    rewrite synced_list_length, ipack_length; subst.
    unfold items_valid in *; intuition.
    substl (length items); rewrite divup_mul; auto.

    step; msalloc_eq.
    subst; rewrite synced_list_map_fst.
    unfold items_valid, RALen in *; intuition.
    erewrite iunpack_ipack_firstn; eauto.
    rewrite firstn_oob; auto.
    substl (length items); auto.
    cancel.
  Qed.
  Proof.
    unfold init, rep.
    step.
    safestep.
    msalloc_eq. destruct (MSAllocC a); cancel.
    pred_apply; cancel.
    step.

    subst; rewrite Nat.sub_diag; simpl.
    unfold list2nmem; simpl.
    apply emp_empty_mem.

    cancel.
  Qed.
  Proof.
    unfold ifind, rep.
    safestep.
    safestep. auto. msalloc_eq; cancel. eauto.
    pred_apply; cancel. eauto.
    safestep.
    safestep.
    safestep.
    cbv [BFILE.datatype]; cancel.

    eapply ifind_length_ok; eauto.
    Hint Resolve
         ifind_list_ok_cond
         ifind_result_inbound
         ifind_result_item_ok.
    unfold items_valid in *; intuition idtac.
    safestep; msalloc_eq; try cancel.

    unfold items_valid, RALen in *; intuition.
    eapply ifind_block_none_progress; eauto.
    cancel.

    safestep; msalloc_eq.
    destruct a1; cancel.
    match goal with
    | [ H: forall _, Some _ = Some _ -> _ |- _ ] =>
      edestruct H; eauto
    end.
    or_r; cancel.
    or_l; cancel.
    unfold items_valid, RALen in *; intuition.
    cancel.
    apply LOG.rep_hashmap_subset; auto.
    Unshelve.  all: try exact tt; eauto.
  Qed.
  Proof.
    unfold get_array.
    hoare.
    eapply list2nmem_ptsto_bound; eauto.
    subst; apply eq_sym.
    eapply list2nmem_sel; eauto.
  Qed.
  Proof.
    unfold put_array.
    hoare.
    eapply list2nmem_ptsto_bound; eauto.
    eapply list2nmem_updN; eauto.
  Qed.
  Proof.
    unfold extend_array.
    hoare.
    or_r; cancel.

    rewrite block0_repeat.
    fold Rec.data.
    replace (updN (repeat item0 items_per_val) 0 e) with
            ([e] ++ (repeat item0 (items_per_val - 1))).
    replace (length items + 1) with (length (items ++ [e])).
    rewrite app_assoc.
    apply list2nmem_arrayN_app.
    apply list2nmem_app; auto.
    rewrite app_length; simpl; auto.
    rewrite updN_0_skip_1 by (rewrite repeat_length; auto).
    rewrite skipn_repeat; auto.
  Qed.
  Proof.
    unfold ifind_array; intros.
    repeat monad_simpl_one.
    eapply pimpl_ok2. eauto with prog.
    safecancel.
    repeat monad_simpl_one.
    eapply pimpl_ok2. eauto with prog.
    safecancel.
    cancel.
    or_r; cancel.
    apply list2nmem_ptsto_cancel; auto.
  Qed.
  Proof.
    unfold rep, items_valid; intuition.
    destruct_lift H; auto.
  Qed.
  Proof.
    unfold rep, items_valid; cancel.
  Qed.
  Proof.
    intros.
    destruct (lt_dec i (length l)).
    apply Forall_selN; auto.
    eapply items_wellformed; eauto.
    rewrite selN_oob by omega.
    apply item0_wellformed.
  Qed.
  Proof.
    unfold rep, items_valid; intuition.
    destruct_lift H; auto.
  Qed.
  Proof.
    unfold rep, items_valid; cancel.
  Qed.
  Proof.
    unfold pack_unpack_cond; intuition.
    destruct H1.
    eapply iunpack_ipack; eauto.
  Qed.
  Proof.
    eapply cond_left_inv_inj with (f' := unpack) (PB := fun _ => True).
    unfold cond_left_inverse; intuition.
    apply pack_unpack_id; auto.
  Qed.
  Proof.
    eapply cond_left_inv_inj with (f' := map fst) (PB := fun _ => True).
    unfold cond_left_inverse; intuition.
    apply synced_list_map_fst; auto.
  Qed.
  Proof.
    unfold rep, items_valid; intros.
    destruct_lift H; destruct_lift H0; subst.
    apply ipack_injective; unfold pack_unpack_cond; eauto.
    apply synced_list_injective; auto.
    eapply arrayN_list_eq; eauto.
  Qed.
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite crash_xform_arrayN_synced.
    cancel.
  Qed.
  Proof.
    unfold rep; intros.
    destruct_lift H0; subst.
    eapply BFILE.file_crash_synced in H.
    intuition. rewrite <- H1.
    pred_apply; cancel.
    unfold items_valid, RALen in *; intuition congruence.
    eapply BFILE.arrayN_synced_list_fsynced; eauto.
  Qed.
  Proof.
    intros.
    apply eq_sym.
    eapply rep_items_eq; eauto.
    eapply file_crash_rep; eauto.
  Qed.