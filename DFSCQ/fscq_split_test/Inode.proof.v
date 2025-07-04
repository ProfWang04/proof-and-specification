    Proof.
      unfold items_per_val; rewrite valulen_is; apply Nat.eqb_eq; compute; reflexivity.
    Qed.
    Proof.
      unfold IRLen, upd_len; intros; simpl.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.
    Proof. intros; simpl; auto. Qed.

    Fact upd_len_get_dind : forall ir n, IRDindPtr (upd_len ir n) = IRDindPtr ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_len_get_tind : forall ir n, IRTindPtr (upd_len ir n) = IRTindPtr ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_len_get_blk : forall ir n, IRBlocks (upd_len ir n) = IRBlocks ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_len_get_iattr : forall ir n, IRAttrs (upd_len ir n) = IRAttrs ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_irec_get_len : forall ir len ibptr dibptr tibptr dbns,
      goodSize addrlen len -> IRLen (upd_irec ir len ibptr dibptr tibptr dbns) = len.
    Proof.
      intros; cbn.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.
    Proof.
      intros; cbn.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.
    Proof.
      intros; cbn.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.
    Proof.
      intros; cbn.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.
    Proof. intros; simpl; auto. Qed.

    Fact upd_irec_get_iattr : forall ir len ibptr dibptr tibptr dbns,
      IRAttrs (upd_irec ir len ibptr dibptr tibptr dbns) = IRAttrs ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_irec_eq_upd_len : forall ir len, goodSize addrlen len ->
      upd_len ir len = upd_irec ir len (IRIndPtr ir) (IRDindPtr ir) (IRTindPtr ir) (IRBlocks ir).
    Proof.
      intros; simpl. unfold upd_len.
      unfold upd_irec, IRIndPtr, IRDindPtr, IRTindPtr, IRBlocks.
      repeat rewrite natToWord_wordToNat. simpl.
      repeat match goal with [|- context [fst ?x] ] => destruct x; simpl end.
      reflexivity.
    Qed.
    Proof.
      intros. apply wordToNat_good.
    Qed.
    Proof.
      intros. apply wordToNat_good.
    Qed.
    Proof.
      intros. apply wordToNat_good.
    Qed.
    Proof.
      intros. apply wordToNat_good.
    Qed.
  Proof.
    unfold rep; intros.
    norml; unfold stars; simpl.
    rewrite IRec.items_length_ok_pimpl.
    rewrite listmatch_length_pimpl.
    cancel.
    cbn in *.
    rewrite combine_length_eq in * by auto.
    congruence.
  Qed.
  Proof.
    intros; subst.
    eapply IRec.item_wellformed; eauto.
  Qed.
  Proof.
    intros; simpl in H.
    destruct i; repeat destruct p.
    repeat destruct d0; repeat destruct p; intuition.
  Qed.
  Proof.
    intros.
    apply direct_blocks_length.
    eapply irec_well_formed; eauto.
  Qed.
  Proof.
    intros.
    eapply IRec.item_wellformed with (i := inum) in H.
    setoid_rewrite <- H0 in H.
    unfold Rec.well_formed in H; simpl in H; intuition.
  Qed.
  Proof.
    intros. unfold rep.
    split; norm; unfold stars; simpl.
    all : intuition eauto.
    all : rewrite listmatch_piff_replace.
    all : try cancel.
    all : intros; unfold inode_match, BALLOCC.bn_valid.
    all : destruct x.
    all : rewrite Ind.rep_bxp_switch by (eassumption||symmetry; eassumption).
    all : rewrite H in *.
    all : split; cancel.
  Qed.
  Proof.
    unfold rep.
    cancel.
    rewrite IRec.rep_clear_cache.
    cancel.
    all: auto.
  Qed.
  Proof.
    intros.
    cbn in *.
    split; apply Ind.rep_keep_blocks.
    all: repeat match goal with
    | [ |- context [fst ?p] ] => destruct p; cbn
    | [ |- context [snd ?p] ] => destruct p; cbn
    end.
    all: reflexivity.
  Qed.
  Proof.
    intros; subst; auto.
  Qed.
  Proof.
    intros; subst; auto.
  Qed.
  Proof.
    unfold inode_match.
    unfold IRec.Defs.item0 at 1.
    rewrite Rec.of_word_zero_reczero; cbn.
    intros.
    rewrite Ind.rep_piff_direct by (cbn; omega).
    unfold Ind.rep_direct.
    split; cancel; rewrite ?Ind.indrep_0 by auto; try cancel.
    constructor.
    setoid_rewrite Rec.of_word_zero_reczero.
    repeat constructor.
    apply list_same_repeat.
  Qed.
  Proof.
    induction n; simpl; intros.
    unfold listmatch; cancel.
    rewrite listmatch_cons.
    rewrite <- IHn.
    rewrite inode_match_init_emp.
    cancel.
  Qed.
  Proof.
    unfold init, rep.
    step.
    cbv; auto.
    step.
    unfold IRec.rep. cancel.
    rewrite combine_repeat.
    apply inode_match_init_ok.
    apply IRec.cache_rep_empty.
    autorewrite with lists; auto.
    apply Ind.pred_fold_left_repeat_emp.
  Qed.
  Proof.
    unfold getlen, rep; pose proof irec0.
    safestep.
    simplen.
    step.

    extract.
    denote Ind.rep as Hx; unfold Ind.rep in Hx; destruct_lift Hx.
    seprewrite; subst; eauto.
  Unshelve.
    all: eauto.
  Qed.
  Proof.
    unfold getattrs, rep.
    safestep.
    simplen.

    step.
    extract.
    destruct_lifts.
    seprewrite; subst; eauto.
  Unshelve.
    all: eauto.
  Qed.
  Proof.
    unfold setattrs, rep.
    safestep.
    simplen.

    step.
    irec_wf.
    sepauto.

    safestep.
    erewrite combine_updN_l.
    eapply listmatch_updN_selN;
      rewrite ?combine_length_eq by auto; simplen.
    eassign (mk_inode (IBlocks ino) attr).
    erewrite selN_combine with (b0 := emp) by auto.
    unfold inode_match; cancel; sepauto.
    auto.
    simplen.
    sepauto.

    eauto.
    cancel.
    cancel; eauto.
    Unshelve. exact irec0.
    all: eauto.
  Qed.
  Proof.
    unfold updattr, rep.
    safestep.
    simplen.

    safestep.
    filldef; abstract (destruct kv; cbn; subst; irec_wf).
    sepauto.

    safestep.
    rewrite combine_updN.
    eapply listmatch_updN_selN; erewrite ?selN_combine; simplen.
    4, 5: sepauto.
    seprewrite.
    eassign (@emp addr addr_eq_dec bool).
    unfold inode_match; cancel.
    rewrite updN_selN_eq. auto.

    simplen.
    cancel.
    cancel; eauto.
  Unshelve.
    all: solve [eauto | exact irec0].
  Qed.
  Proof.
    unfold getbnum, rep.
    safestep.
    simplen.

    prestep; norml.
    extract; seprewrite.
    cancel; eauto.
    step.
    rewrite listmatch_isolate with (a := combine ilist _) (i := inum) by simplen.
    unfold inode_match. rewrite selN_combine by simplen. cancel.
    cancel.
  Unshelve.
    all: eauto.
  Qed.
  Proof.
    unfold getallbnum, rep.
    safestep.
    simplen.

    prestep; norml.
    extract; seprewrite.
    cancel.
    step.
    rewrite listmatch_isolate with (a := combine ilist _) (i := inum) by simplen.
    unfold inode_match. rewrite selN_combine by simplen. cancel.
    cancel.
  Unshelve.
    all: eauto.
  Qed.
  Proof.
    unfold shrink, rep.
    safestep.
    simplen.

    extract; seprewrite.
    safestep.
    rewrite listmatch_isolate with (a := combine ilist _) (i := inum) by simplen.
    unfold inode_match at 2. rewrite selN_combine by simplen. cancel.
    Ind.psubst.
    rewrite Ind.pred_fold_left_selN_removeN. cancel.
    step.
    subst; unfold BPtrSig.upd_irec, BPtrSig.IRLen. simpl.
    unfold Ind.rep in *. rewrite BPtrSig.upd_irec_get_blk in *.
    match goal with H: context [lift_empty] |- _ => destruct_lift H end.
    smash_rec_well_formed.
    sepauto.

    match goal with H: context [lift_empty] |- _ => destruct_lift H end.
    safestep.
    4, 5: sepauto.
    rewrite combine_updN, listmatch_updN_removeN.
    cancel.
    unfold BPtrSig.upd_len, BPtrSig.IRLen, cuttail; simpl.
    cancel.
    match goal with [H : context [Ind.rep _ _ ?x ?l] |- context [length ?l] ] =>
      unfold Ind.rep in H; unfold BPtrSig.IRLen in H; destruct_lift H;
      substl (length l); cancel
    end.
    apply forall_firstn; auto.
    simplen.
    simplen.
    rewrite Ind.pred_fold_left_updN_removeN by simplen.
    split; cancel.
    simplen.
    cancel; auto.
    cancel; auto.
  Unshelve.
    all: solve [eauto | exact (inode0, emp) | exact IRec.Defs.item0].
  Qed.
  Proof.
    unfold reset, rep.
    safestep.
    simplen.

    extract; seprewrite.
    safestep.
    rewrite listmatch_isolate with (a := combine ilist _) (i := inum) by simplen.
    unfold inode_match. rewrite selN_combine by simplen. cancel.
    Ind.psubst.
    rewrite Ind.pred_fold_left_selN_removeN. cancel.
    step.
    subst; unfold BPtrSig.upd_irec, BPtrSig.IRLen. simpl.
    smash_rec_well_formed.
    repeat match goal with |- let (_, _) := ?y in _ => destruct y; intuition idtac end.
    unfold Ind.rep in *. rewrite BPtrSig.upd_irec_get_blk in *.
    match goal with H: context [lift_empty] |- _ => destruct_lift H end. auto.
    sepauto.

    safestep.
    4, 5, 6: sepauto.
    rewrite combine_updN, listmatch_updN_removeN.
    unfold inode_match, BPtrSig.upd_len, BPtrSig.IRLen; simpl.
    rewrite rep_upd_attrs. cbn.
    unfold cuttail.
    match goal with [H : context [Ind.rep _ _ ?x ?l] |- context [length ?l] ] =>
      unfold Ind.rep in H; destruct_lift H; substl (length l)
    end.
    cancel.
    auto using forall_firstn.
    simplen.
    simplen.
    rewrite Ind.pred_fold_left_updN_removeN. split; cancel.
    simplen.
    simplen.
    cancel; auto.
    cancel; auto.
  Unshelve.
    all: solve [eauto | exact IRec.Defs.item0 | exact (inode0, emp)].
  Qed.
  Proof.
    unfold IRec.rep, IRec.LRA.rep, IRec.LRA.items_valid; intros.
    destruct_lift H.
    denote Forall as Hx.
    apply Forall_selN with (i := inum) (def := irec0) in Hx; auto.
    apply direct_blocks_length in Hx.
    setoid_rewrite <- H0 in Hx.
    cbv in Hx; cbv in a.
    smash_rec_well_formed.
  Qed.
  Proof.
    unfold grow, rep.
    safestep.
    simplen.

    extract; seprewrite.
    match goal with H: context [lift_empty] |- _ => destruct_lift H end.
    safestep.
    eauto.
    rewrite listmatch_isolate with (a := combine ilist _) (i := inum) by simplen.
    unfold inode_match. rewrite selN_combine by simplen. cancel.
    Ind.psubst.
    rewrite Ind.pred_fold_left_selN_removeN. cancel.
    step.
    eapply grow_wellformed; eauto.
    simplen.
    sepauto.

    step.
    or_r; cancel.
    4: sepauto.
    rewrite combine_updN, listmatch_updN_removeN.
    cancel.
    substl (IAttr (selN ilist inum inode0)); eauto.
    eauto using Forall_app, BALLOCC.bn_valid_roundtrip.
    simplen.
    simplen.
    rewrite Ind.pred_fold_left_updN_removeN by simplen.
    split; cancel.
    simplen.
    cancel; auto.
    cancel; auto.

  Unshelve.
    all: eauto; exact emp.
  Qed.
  Proof.
    intros.
    unfold inode_match.
    destruct x.
    split.
    intros m H'. destruct_lifts.
    pred_apply. cancel.
    eapply Ind.rep_IFs_sync_invariant with (m := m).
    pred_apply. cancel.
    cancel.
  Qed.
  Proof.
    unfold INODE.rep.
    intros.
    destruct_lifts.
    rewrite SyncedMem.sm_sync_invariant_piff by eauto.
    eapply Ind.sm_sync_invariant_pred_fold_left.
    rewrite listmatch_lift_l in H.
    destruct_lifts.
    erewrite <- Forall_combine_r; try eassumption.
    split; intro H'; exact H'.
    eassign (fun x y => inode_match bxp x y).
    intros.
    rewrite inode_match_sm_sync_invariant.
    destruct x; cbn.
    split; cancel.
  Qed.
  Proof.
    intros; split;
    unfold pimpl; intros; pred_apply;
    unfold rep in H; destruct_lift H; cancel.
    extract at inum.
    unfold inode_match in H.
    erewrite selN_combine in * by auto.
    destruct_lifts; eauto.
  Unshelve.
    all: eauto.
  Qed.
  Proof.
    intros.
    setoid_rewrite inode_rep_bn_valid_piff at 1; cancel.
    specialize (H1 _ H).
    rewrite Forall_forall in H1.
    eapply H1; eauto.
    apply in_selN; eauto.
  Qed.
  Proof.
    unfold inode_match; split.
    xform_norm.
    rewrite Ind.xform_rep; cancel.
    cancel.
    xform_normr.
    rewrite Ind.xform_rep; cancel.
  Qed.
  Proof.
    intros.
    intros m H'. pred_apply; cancel.
    eapply Ind.sm_sync_invariant_pred_fold_left.
    eapply listmatch_lift_l with (P := fun x => sm_sync_invariant (snd x)) in H'.
    destruct_lifts.
    eapply Forall_combine_r; eauto.
    intuition.
    eassign (fun x y => inode_match bxp x y).
    intro x. destruct x. intros.
    rewrite inode_match_sm_sync_invariant.
    split; cancel.
  Qed.
  Proof.
    unfold rep; intros; split.
    xform_norm.
    rewrite IRec.xform_rep.
    rewrite xform_listmatch_idem.
    rewrite listmatch_inode_match_sm_sync_invariant by auto.

    cancel.
    eapply sm_sync_invariant_piff; eauto.
    apply crash_xform_inode_match.

    cancel.
    xform_normr.
    rewrite IRec.xform_rep.
    rewrite xform_listmatch_idem.
    cancel.
    apply crash_xform_inode_match.
  Qed.