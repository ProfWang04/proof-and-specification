  Proof.
    unfold items_valid; intuition.
    rewrite length_updN; auto.
    apply Forall_wellformed_updN; auto.
  Qed.
  Proof.
    induction len; simpl; intros; auto using items_valid_updN.
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
    rewrite synced_list_length, ipack_length.
    apply div_lt_divup; auto.

    safestep.
    subst; rewrite synced_list_selN; simpl.
    erewrite selN_val2block_equiv.
    apply ipack_selN_divmod; auto.
    apply list_chunk_wellformed; auto.
    unfold items_valid in *; intuition; auto.
    apply Nat.mod_upper_bound; auto.
  Qed.
  Proof.
    unfold put, rep.
    hoare; subst.

    (* [rewrite block2val_updN_val2block_equiv] somewhere *)

    rewrite synced_list_length, ipack_length; apply div_lt_divup; auto.
    rewrite synced_list_length, ipack_length; apply div_lt_divup; auto.
    unfold items_valid in *; intuition auto.

    apply arrayN_unify.
    rewrite synced_list_selN, synced_list_updN; f_equal; simpl.
    rewrite block2val_updN_val2block_equiv.
    apply ipack_updN_divmod; auto.
    apply list_chunk_wellformed.
    unfold items_valid in *; intuition; auto.
    apply Nat.mod_upper_bound; auto.
    apply items_valid_updN; auto.
  Qed.
  Proof.
    unfold read, rep.
    hoare.

    rewrite synced_list_length, ipack_length.
    unfold items_valid in *; intuition.
    substl (length items); rewrite divup_mul; auto.

    subst; rewrite synced_list_map_fst.
    unfold items_valid in *; intuition.
    eapply iunpack_ipack_firstn; eauto.
  Qed.
  Proof.
    unfold write, rep.
    hoare.

    unfold items_valid in *; intuition; auto.
    erewrite synced_list_length, items_valid_length_eq; eauto.
    rewrite vsupsyn_range_synced_list; auto.
    erewrite synced_list_length, items_valid_length_eq; eauto.
  Qed.
  Proof.
    unfold init, rep.
    hoare.

    rewrite repeat_length; omega.
    rewrite vsupsyn_range_synced_list by (rewrite repeat_length; auto).
    apply arrayN_unify; f_equal.
    apply repeat_ipack_item0.

    unfold items_valid; intuition.
    rewrite repeat_length; auto.
    apply Forall_repeat.
    apply item0_wellformed.
  Qed.
  Proof.
    unfold ifind, rep.
    safestep. eauto.
    eassign items.
    pred_apply_instantiate; cancel.
    eauto.

    safestep.
    safestep.
    safestep.
    eapply ifind_length_ok; eauto.

    unfold items_valid in *; intuition idtac.
    step.
    cancel.

    safestep.
    destruct a; cancel.
    match goal with
    | [ H: forall _, Some _ = Some _ -> _ |- _ ] =>
      edestruct H; eauto
    end.
    or_r; cancel.
    pimpl_crash.
    eassign (exists ms', LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm)%pred.
    cancel.
    erewrite LOG.rep_hashmap_subset; eauto.

    Unshelve. exact tt.
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
    unfold rep; intuition.
    destruct_lift H0.
    unfold items_valid in *; subst; intuition.
    apply list2nmem_arrayN_length in H1.
    rewrite H, H3 in H1.
    eapply Nat.mul_le_mono_pos_r.
    apply items_per_val_gt_0.
    auto.
  Qed.
  Proof.
    intros.
    eapply arrayN_list2nmem in H0.
    rewrite <- H; simpl in *; auto.
    exact item0.
  Qed.
  Proof.
    unfold read_array.
    hoare.
    eapply read_array_length_ok; eauto.
    subst; eapply read_array_list_ok; eauto.
  Qed.
  Proof.
    unfold ifind_array; intros.
    hoare.
    or_r; cancel.
    apply list2nmem_ptsto_cancel; auto.
  Qed.
  Proof.
    intros a f v1 v2 c H.
    subst; auto.
  Qed.
  Proof.
    unfold items_valid.
    intros ra.
    generalize (RALen ra) as r; intro r; destruct r.
    intros; subst; simpl in *; intuition.
    rewrite length_nil with (l := l2); auto.
    rewrite length_nil with (l := l1); auto.
    induction r; intros; intuition.
    simpl in *; rewrite plus_0_r in *.
    rewrite ipack_one in *; auto.
    rewrite ipack_one in *; auto.
    match goal with [H : _::_ = _::_ |- _] => inversion H; clear H end.
    unfold block2val, word2val, eq_rec_r, eq_rec in *.
    simpl in *.
    eq_rect_eq; auto; unfold Rec.well_formed; simpl; intuition.
    repeat match goal with
      [ lx : itemlist,
        Hl : length ?lx = _,
        H : context [ipack ?lx] |- _] =>
        erewrite <- firstn_skipn with (l := lx) (n := items_per_val) in H;
        erewrite ipack_app with (na := 1) in H;
        [> erewrite <- firstn_skipn with (l := lx) | ];
        [> erewrite ipack_one with (l := firstn _ _) in H | ]
    end; simpl in *; try rewrite plus_0_r in *.
    match goal with [H: _::_ = _::_ |- _ ] => inversion H end.
    unfold block2val, word2val, eq_rec_r, eq_rec in *.
    simpl in *.
    eq_rect_eq.
    f_equal; eauto.
    apply IHr; intuition.
    all : repeat (
          auto || lia || split  ||
          unfold item in *      ||
          rewrite skipn_length  ||
          apply forall_skipn    ||
          apply forall_firstn   ||
          apply firstn_length_l ).
  Qed.
  Proof.
    intros.
    unfold rep in *.
    repeat match goal with
      [ H : (_ * (exis _))%pred _ |- _ ] => destruct_lift H
      end.
    match goal with
      [ H : context[synced_list _] |- _] =>  eapply arrayN_unify', synced_list_inj in H
    end.
    eapply ipack_inj; eauto.
    repeat rewrite synced_list_length.
    repeat rewrite ipack_length.
    f_equal.
    unfold items_valid in *; intuition.
    unfold item in *.
    omega.
    eassumption.
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
    unfold rep; intros; split.
    xform_norm.
    rewrite crash_xform_arrayN_synced; cancel.
    cancel.
    xform_normr; cancel.
    rewrite <- crash_xform_arrayN_r; eauto.
    apply possible_crash_list_synced_list.
  Qed.
  Proof.
    unfold rep.
    intros.
    destruct_lifts.
    eauto using LRA.item_wellformed.
  Qed.
  Proof.
    unfold rep.
    intros xp l c m H.
    rewrite LRA.items_length_ok_pimpl in H.
    pred_apply.
    cancel.
  Qed.
  Proof.
    unfold rep.
    intros.
    xform_norm.
    rewrite LRA.xform_rep.
    split; cancel.
  Qed.
  Proof.
    unfold cache_rep, M.mm.
    intro l. generalize 0. revert l.
    induction l; intros.
    intro; auto.
    simpl. unfold_sep_star.
    repeat exists (M.mm _ (Cache.empty _)).
    intuition.
    cbv. intro. repeat deex. congruence.
    right.
    intro; auto.
  Qed.
  Proof.
    unfold rep. cancel.
    apply cache_rep_empty.
  Qed.
  Proof.
    induction l; cbn; intros; auto.
    unfold sep_star in H.
    rewrite sep_star_is in H.
    unfold sep_star_impl in H.
    repeat deex.
    all: eapply mem_union_sel_none.
    all : solve [
      cbv in H2; intuition auto; apply H3; omega |
      eapply IHl; eauto; omega].
  Qed.
  Proof.
    unfold cache_rep.
    intros items i cache v d.
    change (Cache.find i cache) with (M.mm _ cache i).
    generalize (M.mm item cache).
    clear cache.
    intros.
    eapply isolateN_fwd in H1; eauto.
    autorewrite with core in *.
    unfold cache_ptsto in H1 at 2.
    eapply pimpl_trans in H1.
    2 : rewrite sep_star_assoc, sep_star_comm, sep_star_assoc; reflexivity.
    2 : reflexivity.
    unfold sep_star in H1.
    rewrite sep_star_is in H1.
    unfold sep_star_impl, or, ptsto, emp in H1.
    intuition repeat deex.
    erewrite mem_union_addr in H by eauto.
    inversion H. eauto.
    rewrite mem_union_sel_none in H; try congruence.
    apply mem_union_sel_none.
    eapply arrayN_cache_ptsto_oob; eauto. omega.
    eapply arrayN_cache_ptsto_oob; eauto.
    rewrite firstn_length_l; omega.
  Qed.
  Proof.
    unfold cache_rep in *.
    intros.
    rewrite M.mm_add_upd.
    destruct (M.mm _ cache i) eqn:?.
    eapply cache_rep_some in H0 as ?; eauto.
    rewrite Mem.upd_nop; eauto.
    rewrite Heqo. f_equal. eauto.
    generalize dependent (M.mm _ cache). clear cache.
    intros.
    eapply arrayN_mem_upd_none; eauto.
    edestruct arrayN_except as [H' _]; eauto; apply H' in H0; clear H'.
    unfold sep_star in *.
    rewrite sep_star_is in *.
    unfold sep_star_impl in *.
    repeat deex.
    apply mem_union_none_sel in Heqo.
    cbv [cache_ptsto or ptsto] in *.
    intuition try congruence.
    apply emp_empty_mem_only in H5. subst.
    rewrite mem_union_empty_mem'. auto.
    cbv [cache_ptsto ptsto or].
    left.
    intuition (destruct addr_eq_dec); eauto; congruence.
  Unshelve.
    exact item0.
  Qed.
  Proof.
    cbv [cache_ptsto or].
    intros.
    left.
    intuition auto.
    pose proof (@ptsto_upd _ addr_eq_dec _ i v v0 emp).
    eapply pimpl_trans; try apply H; try pred_apply; cancel.
    pose proof (@ptsto_upd_disjoint _ addr_eq_dec _ emp i v).
    eapply pimpl_trans; try apply H; try pred_apply; try cancel.
    cbv in *; auto.
  Qed.
  Proof.
    unfold cache_rep in *.
    intros.
    rewrite M.mm_add_upd.
    generalize dependent (M.mm _ cache). clear cache.
    intros.
    edestruct arrayN_isolate as [H' _]; eauto; apply H' in H0; clear H'.
    edestruct arrayN_isolate as [_ H']; [| apply H'; clear H'].
    rewrite length_updN; eauto.
    simpl in *.
    rewrite selN_updN_eq by auto.
    rewrite firstn_updN_oob by auto.
    rewrite skipn_updN by auto.
    revert H0.
    unfold_sep_star.
    intuition repeat deex.
    assert (mem_disjoint m0 (Mem.upd m3 i v)).
    cbv [cache_ptsto or ptsto] in H6.
    cbv [mem_disjoint Mem.upd] in *.
    intuition repeat deex.
    destruct addr_eq_dec; subst; eauto 10.
    destruct addr_eq_dec; subst; eauto 10.
    erewrite arrayN_cache_ptsto_oob in H6; eauto; try congruence.
    rewrite firstn_length_l; omega.
    apply mem_disjoint_union in H0 as ?.
    assert (mem_disjoint (Mem.upd m3 i v) m2).
    cbv [cache_ptsto or ptsto] in H6.
    cbv [mem_disjoint Mem.upd] in *.
    intuition repeat deex.
    destruct addr_eq_dec; subst; eauto 10.
    destruct addr_eq_dec; subst; eauto 10.
    erewrite arrayN_cache_ptsto_oob in H9; eauto; try congruence; omega.
    repeat eexists; try eapply cache_ptsto_upd; eauto.
    rewrite mem_union_comm with (m1 := m0) by auto.
    repeat rewrite <- mem_union_upd.
    f_equal.
    apply mem_union_comm, mem_disjoint_comm; auto.
    apply mem_disjoint_mem_union_split_l; auto.
    apply mem_disjoint_comm.
    eapply mem_disjoint_union_2.
    apply mem_disjoint_comm.
    eauto.
  Unshelve. all : eauto.
  Qed.
  Proof.
    unfold get_array, get, rep.
    hoare.
    all : eauto using cache_rep_some, cache_rep_add.
  Qed.
  Proof.
    unfold put_array, put, rep.
    hoare.
    eapply list2nmem_ptsto_bound; eauto.
    eapply cache_rep_updN; eauto.
    eapply list2nmem_ptsto_bound; eauto.
    eapply list2nmem_updN; eauto.
  Qed.