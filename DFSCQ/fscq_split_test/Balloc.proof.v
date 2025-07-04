  Proof.
    intro H.
    apply valulen_nonzero.
    apply Nat.divide_0_l.
    rewrite <- H.
    apply word_size_ok.
  Qed.
  Proof.
    unfold items_per_val. simpl.
    pose proof WBSig.word_size_nonzero.
    rewrite Rounding.mul_div; try omega.
    apply Nat.mod_divide; auto.
    apply WBSig.word_size_ok.
  Qed.
  Proof.
    intros.
    unfold bits.
    pose proof (Rec.array_of_word_length (Rec.WordF 1)) as H.
    simpl in H.
    rewrite H.
    reflexivity.
  Qed.
  Proof.
    unfold bits, Rec.of_word. simpl. intros.
      eq_rect_simpl; repeat f_equal;
      erewrite ?whd_eq_rect_mul, ?wtl_eq_rect_mul;
      reflexivity.
  Qed.
  Proof.
    unfold HasAvail.
    unfold state, full.
    generalize Defs.itemsz.
    intros.
    rewrite bits_length.
    induction s; intros.
    cbv in *. congruence.
    rewrite bits_cons.
    destruct b.
    + destruct (weq s (wones n)); try (simpl in *; congruence).
      eapply IHs in n0.
      match goal with H : { x | _ } |- _ =>
        let y := fresh "i" in
        let H' := fresh "H" in
        destruct H as [y [? H'] ];
        exists (S y);
        split; [ omega |
          intros d; rewrite <- (H' d)];
          clear H'
      end.
      reflexivity.
    + exists 0.
      split; auto; omega.
  Defined.
  Proof.
    intros.
    unfold bits.
    eq_rect_simpl.
    rewrite Rec.to_of_id.
    eq_rect_simpl.
    reflexivity.
  Qed.
  Proof.
    unfold set_bit, bits, bit.
    intros.
    rewrite (bits_of_word s).
    eq_rect_simpl.
    pose proof (Rec.word_updN_equiv (Rec.WordF 1)) as Ha.
    simpl in Ha.
    specialize (Ha sz n (@Rec.to_word (Rec.ArrayF (Rec.WordF 1) sz) (@bits sz s))).
    change v with (@Rec.to_word (Rec.WordF 1) v) at 1.
    rewrite Ha by auto.
    rewrite Rec.of_to_id; auto.
    unfold Rec.well_formed. split; auto.
    rewrite length_updN.
    rewrite Rec.of_to_id.
    auto using bits_length.
    apply Rec.of_word_well_formed.
  Qed.
  Proof.
    unfold to_bits. intros.
    erewrite concat_hom_length, map_length.
    reflexivity.
    apply Forall_forall; intros.
    rewrite in_map_iff in *.
    deex. auto using bits_length.
  Qed.
  Proof.
    unfold freelist_bmap_equiv; split; intros.
    eapply Forall_remove; intuition eauto.
    eapply Forall_impl; try eassumption.
    simpl; intros.
    rewrite length_updN; eauto.

    split; intuition; intros.

    destruct (addr_eq_dec a a0); subst.
    rewrite selN_updN_eq by auto.
    exfalso; eapply remove_In; eauto.
    rewrite selN_updN_ne by auto.
    apply H3.
    eapply remove_still_In; eauto.

    destruct (addr_eq_dec a a0); subst.
    contradict H1.
    rewrite selN_updN_eq by auto.
    discriminate.
    apply remove_other_In; auto.
    apply H3.
    erewrite <- selN_updN_ne; eauto.
  Qed.
  Proof.
    unfold to_bits.
    intros.
    pose proof (Nat.div_mod bn Defs.itemsz) as Hbn.
    rewrite Hbn at 4 by auto.
    rewrite plus_comm, mult_comm.
    rewrite updN_concat; f_equal.
    rewrite map_updN; f_equal.
    rewrite bits_set_avail.
    f_equal.
    erewrite selN_map; auto.
    apply Nat.mod_upper_bound; auto.
    apply Nat.mod_upper_bound; auto.
    apply Forall_forall; intros.
    rewrite in_map_iff in H0. deex.
    rewrite bits_length. auto.
  Qed.
  Proof.
    unfold freelist_bmap_equiv; split; intuition; intros.

    constructor.
    rewrite length_updN; eauto.

    eapply Forall_impl; try eassumption.
    simpl; intros.
    rewrite length_updN; eauto.

    destruct (addr_eq_dec a a0); subst.
    rewrite selN_updN_eq by auto.
    unfold Avail; auto.
    rewrite selN_updN_ne by auto.
    apply H2.
    inversion H; congruence.

    destruct (addr_eq_dec a a0); subst; simpl; auto.
    right; apply H2.
    erewrite <- selN_updN_ne; eauto.
  Qed.
  Proof.
    unfold freelist_bmap_equiv, Avail.
    intros; apply H; auto.
  Qed.
  Proof.
    intros.
    unfold BmpSig.RALen.
    rewrite BmpSig.blocksz_ok.
    cbn [Rec.len BmpSig.itemtype].
    auto using mult_assoc.
  Qed.
  Proof.
    unfold Bmp.rep, Bmp.items_valid; intros.
    destruct_lift H0.
    eapply lt_le_trans; eauto.
    rewrite to_bits_length.
    setoid_rewrite H6.
    rewrite bits_len_rewrite; auto.
  Qed.
  Proof.
    unfold Bmp.rep, Bmp.items_valid; intros.
    destruct_lift H.
    apply Nat.div_lt_upper_bound; auto.
    setoid_rewrite H6.
    rewrite mult_comm.
    rewrite bits_len_rewrite.
    auto.
  Qed.
  Proof.
    induction n; intros; simpl.
    reflexivity.
    rewrite bits_cons.
    shatter_word x.
    simpl.
    congruence.
  Qed.
  Proof.
    intros.
    unfold to_bits.
    rewrite plus_comm.
    rewrite updN_concat; auto.
    rewrite map_updN.
    erewrite selN_map by auto.
    rewrite bits_set_avail by auto.
    reflexivity.
    apply Forall_forall.
    intros.
    rewrite in_map_iff in *.
    deex; subst.
    apply bits_length.
  Qed.
  Proof.
    intros.
    apply Rounding.div_lt_mul_lt.
    omega.
    rewrite Nat.div_add_l by omega.
    rewrite Nat.div_small by omega.
    omega.
  Qed.
  Proof.
    intros.
    destruct (lt_dec n (sz * length l)).
    unfold to_bits.
    erewrite <- selN_selN_hom; try (rewrite ?map_length, ?wbits_length; eauto).
    erewrite selN_map; auto.
    apply Nat.div_lt_upper_bound; auto.
    apply Forall_map, Forall_forall; intros.
    rewrite bits_length; auto.
    rewrite selN_oob.
    rewrite selN_oob with (n := _ / _).
    rewrite bits_rep_bit.
    rewrite repeat_selN'; auto.
    apply Nat.div_le_lower_bound; solve [auto | omega].
    rewrite to_bits_length, mult_comm. omega.
  Qed.
  Proof.
    unfold avail_nonzero; intros.
    unfold Avail.
    apply ifind_list_ok_bound in H0 as H1; simpl in H1.
    rewrite bits_length in *.
    rewrite selN_to_bits by auto.
    rewrite Nat.div_add_l by auto.
    rewrite Nat.div_small by auto.
    rewrite Nat.add_0_r.
    rewrite plus_comm.
    rewrite Nat.mod_add by auto.
    rewrite Nat.mod_small by auto.
    apply ifind_list_ok_cond in H0 as H2.
    simpl in *.
    destruct weq; subst; try congruence.
    eapply ifind_list_ok_item in H0.
    simpl in *.
    rewrite Nat.sub_0_r in *.
    erewrite selN_inb with (d1 := d') in H0.
    apply H0.
    auto.
  Qed.
  Proof.
    intros.
    destruct (shatter_word_S w); repeat deex.
    rewrite wor_wone.
    rewrite bits_cons.
    reflexivity.
  Qed.
  Proof.
    unfold ifind_byte.
    unfold Defs.itemsz. simpl.
    generalize (WBSig.word_size_nonzero).
    generalize WBSig.word_size.
    unfold avail_nonzero; intros.
    unfold Avail.
    denote (ifind_list _ _ _ = _) as Hl.
    apply ifind_list_ok_bound in Hl as ?; simpl in *.
    rewrite bits_length in *.
    rewrite selN_to_bits by auto.
    rewrite Nat.div_small by auto.
    rewrite Nat.mod_small by auto.
    apply ifind_list_ok_cond in Hl as ?.
    simpl in *.
    destruct weq; subst; try congruence.
    eapply ifind_list_ok_item in Hl as ?.
    simpl in *.
    rewrite Nat.sub_0_r in *.
    destruct n; try congruence.
    rewrite bits_wor_wone in *.
    destruct ii; simpl in H0.
    compute [selN inuse avail natToWord mod2] in *. congruence.
    match goal with |- context [selN ?l 0 ?d] =>
      rewrite selN_inb with (d1 := d') (d2 := d) in H3;
      pose proof (shatter_word_S (selN l 0 d)); repeat deex
    end.
    denote (selN _ _ _ = _) as Hx.
    rewrite Hx in *.
    rewrite bits_cons.
    simpl in *.
    erewrite selN_inb by (rewrite bits_length; omega). eauto.
    Unshelve.
    all : eauto; solve [exact nil | exact None].
  Qed.
  Proof.
    unfold ifind_byte, state.
    generalize (WBSig.word_size_nonzero).
    unfold Defs.itemsz. simpl.
    generalize WBSig.word_size.
    intros n H' w b H.
    eapply ifind_list_ok_cond in H as Ha.
    eapply ifind_list_ok_item in H as Hb.
    cbn in *.
    destruct n; try congruence.
    rewrite bits_wor_wone in *.
    simpl in *.
    destruct weq; compute in *; congruence.
    Unshelve. eauto.
  Qed.
  Proof.
    unfold Bmp.Defs.item0, Defs.itemsz, BmpSig.itemtype.
    simpl.
    generalize WBSig.word_size.
    induction n; simpl.
    intros. inversion H.
    intros.
    unfold Rec.of_word.
    fold Nat.mul.
    eq_rect_simpl.
    rewrite whd_eq_rect_mul.
    compute [natToWord].
    erewrite wtl_eq_rect_mul.
    destruct n0; [reflexivity | apply IHn].
    omega.
  Qed.
  Proof.
    unfold freelist_bmap_equiv; intuition; intros.
    - eapply Forall_forall.
      intros.
      eapply in_seq in H.
      rewrite to_bits_length.
      rewrite repeat_length.
      rewrite bits_len_rewrite. omega.
    - rewrite selN_to_bits by auto.
      rewrite repeat_selN; auto.
      rewrite avail_item0.
      unfold Avail; auto.
      apply Nat.mod_upper_bound; auto.
      eapply in_seq in H.
      apply Nat.div_lt_upper_bound; auto.
      rewrite mult_comm, bits_len_rewrite.
      intuition idtac.
    - apply in_seq; intuition.
      destruct (lt_dec a (BMPLen xp * valulen)); try omega.
      rewrite selN_oob in *.
      cbv in *; congruence.
      rewrite to_bits_length.
      rewrite repeat_length.
      rewrite bits_len_rewrite.
      omega.
  Qed.
  Proof.
    split; generalize dependent start;
      induction l; cbn; intuition.
    all: repeat match goal with
    | _ => omega
    | [H: context [if ?x then _ else _] |- _ ] => destruct x; subst
    | [H: In _ (_ :: _) |- _] => destruct H; subst
    | [H: In _ _ |- _] => apply IHl in H
    end.
  Qed.
  Proof.
    induction l; cbn; intros.
    constructor.
    repeat match goal with
    |- context [if ?x then _ else _] => destruct x; subst
    end; auto.
    constructor; auto.
    intro.
    apply bits_to_freelist_bound in H. omega.
  Qed.
  Proof.
    induction l; cbn; intuition.
    repeat match goal with
    | _ => omega
    | [H: context [if ?x then _ else _] |- _ ] => destruct x; subst
    | [H: In _ (_ :: _) |- _] => destruct H; subst
    | [H: In _ _ |- _] => apply IHl in H
    end.
  Qed.
  Proof.
    unfold bit in *.
    induction l; cbn; intuition.
    cbv in *; congruence.
    destruct i;
    repeat match goal with
    | _ => omega
    | _ => solve [auto]
    | [H: context [_ + S _] |- _] => rewrite <- plus_Snm_nSm in H
    | [H: context [if ?x then _ else _] |- _ ] => destruct x; subst
    | [H: In _ (_ :: _) |- _] => destruct H; subst
    | [H: In _ _ |- _] => apply IHl in H
    end.
    apply bits_to_freelist_bound in H0. omega.
    shatter_word a. destruct x; cbv in *; congruence.
    shatter_word a. destruct x; cbv in *; congruence.
    destruct i;
    repeat match goal with
    | _ => omega
    | _ => solve [auto | cbv in *; congruence]
    | _ => rewrite <- plus_Snm_nSm
    | [|- context [if ?x then _ else _] ] => destruct x; subst
    | [H: In _ (_ :: _) |- _] => destruct H; subst
    | [|- In _ _ ] => apply IHl
    end.
    autorewrite with core. intuition.
    right. rewrite IHl; auto. omega.
  Qed.
  Proof.
    induction bs; rewrite ?to_bits_length in *; cbn; intuition.
    apply in_app_or in H. destruct H.
    apply bits_to_freelist_bound in H. omega.
    apply IHbs in H. omega.
    apply in_app_or in H. destruct H.
    apply bits_to_freelist_bound in H.
    rewrite bits_length in *. enough (length bs * sz >= 0). omega.
    apply Nat.mul_nonneg_nonneg; omega.
    apply IHbs in H. omega.
    apply in_app_or in H. destruct H.
    destruct x; try omega.
    apply bits_to_freelist_no_zero in H. intuition.
    apply IHbs in H. omega.
  Qed.
  Proof.
    induction bs; cbn; intuition.
    cbv in *; congruence.
    destruct (in_dec addr_eq_dec (start + i) (word_to_freelist a start)) as [H' | H'].
    apply bits_to_freelist_bound in H' as ?.
    apply bits_to_freelist_spec in H'; auto.
    rewrite selN_app1; auto; omega.
    apply in_app_or in H0 as Ha. destruct Ha as [Ha | Ha]; intuition.
    apply itemlist_to_freelist'_bound in Ha as ?.
    replace (start + i) with ((start + sz) + (i - sz)) in H by omega.
    apply IHbs in H.
    rewrite selN_app2; rewrite bits_length.
    rewrite <- H in *.
    replace (start + sz + (i - sz)) with (start + i) in * by omega; auto.
    omega.
    destruct (lt_dec i (length (bits a))).
    rewrite selN_app1 in * by omega.
    rewrite <- bits_to_freelist_spec in *; eauto.
    eapply in_app_iff. right.
    rewrite selN_app2 in * by omega.
    rewrite bits_length in *.
    replace (start + i) with ((start + sz) + (i - sz)) in * by omega.
    rewrite IHbs; eauto.
  Qed.
  Proof.
    induction l1; cbn; intros; auto.
    inversion H; subst.
    constructor.
    rewrite in_app_iff.
    specialize (H1 a) as ?. intuition.
    apply IHl1; intuition eauto.
  Qed.
  Proof.
    induction bs; cbn; intros.
    constructor.
    apply nodup_app; intuition eauto using bits_to_freelist_nodup.
    apply itemlist_to_freelist'_bound in H0.
    apply bits_to_freelist_bound in H.
    rewrite bits_length in *. omega.
    apply itemlist_to_freelist'_bound in H.
    apply bits_to_freelist_bound in H0.
    rewrite bits_length in *. omega.
  Qed.
  Proof.
    induction bs; cbn; intuition.
    apply in_app_or in H. intuition eauto.
    eapply bits_to_freelist_no_zero; eauto.
  Qed.
  Proof.
    cbn; unfold itemlist_to_freelist; intros.
    replace x with (0 + x) in H by omega.
    eapply itemlist_to_freelist'_bound in H. omega.
  Qed.
  Proof.
    cbn; unfold itemlist_to_freelist; intros.
    replace i with (0 + i) in * by omega.
    auto using itemlist_to_freelist'_spec.
  Qed.
  Proof.
    intros.
    apply itemlist_to_freelist'_nodup.
  Qed.
  Proof.
    intros.
    apply itemlist_to_freelist'_no_zero.
  Qed.
  Proof.
    cbv [permutation freelist_bmap_equiv Avail]; intuition.
    pose proof (itemlist_to_freelist_nodup bs).
    rewrite (NoDup_count_occ addr_eq_dec) in *.
    pose proof count_occ_In as Hc. unfold gt in Hc.
    repeat match goal with
    | H: context [count_occ] |- _ => specialize (H x)
    end.
    destruct (in_dec addr_eq_dec 0 freelist).
    - destruct (addr_eq_dec 0 x); subst.
      rewrite count_occ_remove_eq.
      apply count_occ_not_In.
      apply itemlist_to_freelist_no_zero.
      repeat rewrite count_occ_remove_ne by auto.
      destruct (zerop (count_occ addr_eq_dec freelist x)) as [Ha | Ha];
      destruct (zerop (count_occ addr_eq_dec (itemlist_to_freelist bs) x)) as [Hb | Hb]; try omega.
      all: rewrite <- count_occ_not_In, <- Hc in *.
      apply itemlist_to_freelist_spec in Hb.
      rewrite <- H2 in *. congruence.
      intro; subst.
      eapply itemlist_to_freelist_no_zero; eauto.
      destruct (addr_eq_dec x 0); subst; intuition.
      rewrite H2 in *.
      rewrite <- itemlist_to_freelist_spec in Ha by auto.
      intuition.
    - rewrite remove_not_In by auto.
      destruct (zerop (count_occ addr_eq_dec freelist x)) as [Ha | Ha];
      destruct (zerop (count_occ addr_eq_dec (itemlist_to_freelist bs) x)) as [Hb | Hb]; try omega.
      all: rewrite <- count_occ_not_In, <- Hc in *.
      apply itemlist_to_freelist_spec in Hb.
      rewrite <- H2 in *. congruence.
      intro; subst.
      eapply itemlist_to_freelist_no_zero; eauto.
      destruct (addr_eq_dec x 0); subst; intuition.
      rewrite H2 in *.
      rewrite <- itemlist_to_freelist_spec in Ha by auto.
      intuition.
  Qed.
  Proof.
    unfold init, rep; intros.
    step.
    step.
    eapply seq_NoDup.
    apply freelist_bmap_equiv_init_ok.
    apply in_seq; intuition.
    apply arrayN_listpred_seq_fp; auto.
  Qed.
  Proof.
    unfold full.
    generalize Defs.itemsz.
    induction n; simpl; f_equal; auto.
  Qed.
  Proof.
    unfold ifind_byte.
    intros.
    apply ifind_list_ok_bound in H.
    rewrite bits_length in *.
    simpl in *. auto.
  Qed.
  Proof.
    unfold init_nofree, rep; intros.
    step.
    step.
    unfold Bmp.items_valid; intuition.
    rewrite repeat_length; auto.
    step.
    constructor.
    unfold freelist_bmap_equiv; intuition; intros.
    constructor.
    denote (In _ nil) as Hx; inversion Hx.
    denote (Avail _) as Hx; unfold Avail in Hx.
    rewrite selN_to_bits in * by auto.
    rewrite full_eq_repeat, repeat_selN', bits_rep_bit, repeat_selN' in Hx.
    cbv in Hx. congruence.
    Unshelve.
    all: try exact avail; try exact tt.
  Qed.
  Proof.
    unfold get_free_blocks, rep.
    step.
    step.
    eapply itemlist_to_freelist_no_zero; eauto.
    rewrite firstn_oob by (erewrite Bmp.items_length_ok; eauto).
    apply itemlist_to_freelist_nodup.
    rewrite firstn_oob by (erewrite Bmp.items_length_ok; eauto).
    apply freelist_bmap_equiv_itemlist_to_freelist_spec; eauto.
  Qed.
  Proof.
    unfold steal, rep. intros.
    step.

    unfold freelist_bmap_equiv in *; intuition.
    denote! (Forall _ _) as Hf; eapply Forall_forall in Hf; eauto.
    denote (Bmp.rep _ dummy) as Hr; eapply Bmp.items_length_ok in Hr.
    rewrite to_bits_length in *.
    apply Nat.div_lt_upper_bound; auto.
    rewrite mult_comm; auto.

    assert (bn / Defs.itemsz < length dummy).
    unfold freelist_bmap_equiv in *; intuition.
    denote! (Forall _ _) as Hf; eapply Forall_forall in Hf; eauto.
    denote (Bmp.rep _ dummy) as Hr; eapply Bmp.items_length_ok in Hr.
    rewrite to_bits_length in *.
    apply Nat.div_lt_upper_bound; auto.
    rewrite mult_comm; auto.

    step.
    safestep.

    eapply NoDup_remove; eauto.
    rewrite to_bits_updN_set_avail by auto.
    eapply freelist_bmap_equiv_remove_ok; eauto.
    rewrite to_bits_length.
    apply Rounding.div_lt_mul_lt; auto.

    apply piff_refl.
    denote freepred as Hp; rewrite Hp, listpred_remove.
    eassign bn; cancel.

    intros.
    assert (~ (y |->? * y |->?)%pred m'0) as Hc by apply ptsto_conflict.
    contradict Hc; pred_apply; cancel.
    auto.

  Unshelve.
    all: try exact unit.
    all: eauto.
    all: try exact nil.
    all: intros; try exact True.
  Qed.
  Proof.
    unfold alloc, ifind_avail_nonzero, rep.
    step.
    step.
    step.

    denote (ifind_byte _ = Some _) as Hb.
    apply ifind_byte_inb in Hb as ?; auto.
    or_r; cancel.
    eapply NoDup_remove; eauto.
    rewrite to_bits_set_bit; auto.
    eapply freelist_bmap_equiv_remove_ok; eauto.
    rewrite to_bits_length; apply bound_offset; auto.
    apply piff_refl.
    denote freepred as Hp. rewrite Hp, listpred_remove.
    cancel.

    intros.
    assert (~ (y |->? * y |->?)%pred m'0) as Hc by apply ptsto_conflict.
    contradict Hc; pred_apply; cancel.

    eapply is_avail_in_freelist; eauto.
    destruct addr_eq_dec; subst; eauto.
    rewrite to_bits_length; apply bound_offset; auto.
    denote (ifind_byte _ = Some _) as Hb.
    apply ifind_byte_inb in Hb as Hc; auto.
    rewrite Nat.eq_add_0, Nat.eq_mul_0 in *.
    intuition (subst; exfalso; try destruct addr_eq_dec; eauto).
    eapply bmap_rep_length_ok1; eauto.
    rewrite to_bits_length, length_updN.
    apply bound_offset; auto.
    eapply is_avail_in_freelist; eauto.
    destruct addr_eq_dec; subst; eauto.
    rewrite to_bits_length; apply bound_offset; auto.
    Unshelve.
    all : solve [auto | exact full].
  Qed.
  Proof.
    unfold free, rep.
    hoare.

    eapply bmap_rep_length_ok2; eauto.
    eapply bmap_rep_length_ok2; eauto.
    constructor; eauto.
    intro Hin.
    denote (freepred <=p=> _) as Hfp.
    denote (Fx) as Hx.
    rewrite Hfp in Hx.
    erewrite listpred_pick in Hx by eauto.
    destruct_lift Hx.
    eapply ptsto_conflict_F with (m := mx) (a := bn).
    pred_apply; cancel.

    rewrite to_bits_updN_set_avail; auto.
    apply freelist_bmap_equiv_add_ok; auto.
    rewrite to_bits_length.
    apply Rounding.div_lt_mul_lt; auto.
    eapply bmap_rep_length_ok2; eauto.
    eapply bmap_rep_length_ok2; eauto.
    denote (freepred <=p=> _) as Hfp. apply Hfp.
    Unshelve.
    all: eauto.
  Qed.
  Proof.
    intros.
    unfold rep in H.
    destruct_lift H.
    unfold freelist_bmap_equiv in *. intuition.
    eapply Forall_forall in H1; eauto.
    rewrite Bmp.items_length_ok_pimpl in H.
    rewrite BmpSig.blocksz_ok.
    simpl in *.
    destruct_lifts.
    rewrite to_bits_length in *.
    unfold state in *.
    cbn in *.
    denote (length _ = _) as Ha.
    rewrite Ha in *.
    rewrite mult_assoc.
    assumption.
    Unshelve.
    all : eauto; constructor.
  Qed.
  Proof.
    intros.
    unfold rep in *.
    destruct_lift H.
    unfold freelist_bmap_equiv in *; eauto.
  Qed.
  Proof.
    unfold rep; intros; split.
    xform_norm.
    rewrite Bmp.xform_rep; cancel.
    cancel.
    xform_normr.
    rewrite Bmp.xform_rep; cancel.
  Qed.
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite Bmp.xform_rep; cancel.
    rewrite H2.
    rewrite xform_listpred_ptsto_fp; auto.
  Qed.
  Proof.
    rewrite valulen_is.
    apply Nat.mod_divide; auto.
    unfold word_size.
    congruence.
  Qed.
  Proof.
    compute; congruence.
  Qed.
  Proof.
    cbv. congruence.
  Qed.
  Proof.
    unfold cache_rep. intros.
    inversion H0; subst.
    specialize (H _ (eq_refl)). intuition.
    inversion H; auto.
    destruct (addr_eq_dec 0 n); subst.
    cbn in *; intuition auto.
    rewrite remove_comm.
    erewrite <- remove_not_In with (l := cfreelist) (a := n).
    erewrite <- remove_cons with (l := cfreelist).
    apply permutation_remove; auto.
    inversion H; auto.
  Qed.
  Proof.
    unfold cache_rep. intros.
    specialize (H _ eq_refl).
    inversion H2; subst.
    intuition.
    destruct H4; auto.
    constructor; auto.
    rewrite remove_cons_neq by auto.
    auto using permutation_cons.
  Qed.
  Proof.
    unfold cache_rep. intros.
    specialize (H _ eq_refl). intuition.
    rewrite count_occ_In.
    rewrite <- H3.
    rewrite count_occ_remove_ne by auto.
    rewrite <- count_occ_In. auto.
    rewrite count_occ_In.
    erewrite <- count_occ_remove_ne by eauto.
    rewrite H3.
    rewrite <- count_occ_In. auto.
  Qed.
  Proof.
    cbv [cache_rep]. intros. congruence.
  Qed.
  Proof.
    unfold init, rep; intros.
    step.
    step.
  Qed.
  Proof.
    unfold init_nofree, rep; intros.
    step.
    step.
  Qed.
  Proof.
    unfold get_free_blocks, rep.
    hoare.
    rewrite Heqb. auto.
    unfold cache_rep.
    intros ? Hs. inversion Hs; intuition subst; auto.
    auto using permutation_comm.
  Qed.
  Proof.
    unfold alloc.
    step.
    unfold rep in *.
    step.
    apply_cache_rep.
    destruct (addr_eq_dec n 0); subst; cbn in *; intuition.
    rewrite cache_rep_in by eauto.
    cbn; auto.
    step.
    or_r. cancel; apply_cache_rep.
    eauto using cache_rep_remove_cons.
    subst; cbn in *; intuition.
    eapply Alloc.rep_impl_bn_ok with (freelist := freelist); eauto.
    eapply remove_still_In.
    eapply permutation_in; eauto using permutation_comm.
    cbn; auto.
    eapply remove_still_In.
    eapply permutation_in; eauto using permutation_comm.
    cbn; auto.
  Qed.
  Proof.
    unfold free, rep; intros.
    safestep.
    eauto.
    step.
    unfold cache_free_block.
    destruct MSCache eqn:?; auto.
    eapply cache_rep_add_cons; eauto.
    assert (NoDup (bn :: freelist)) as Hd by (eauto using Alloc.rep_impl_NoDup).
    inversion Hd; subst.
    erewrite <- cache_rep_in by eauto. auto.
  Qed.
  Proof.
    unfold steal, rep; intros.
    safestep.
    step.
  Qed.
  Proof.
    unfold rep, Alloc.rep; intros; split.
    xform_norm.
    rewrite Alloc.Bmp.xform_rep; cancel.
    cancel.
    xform_normr.
    cancel.
    xform_normr.
    rewrite Alloc.Bmp.xform_rep; cancel.
  Qed.
  Proof.
    unfold rep, Alloc.rep; intros.
    xform_norm.
    cancel.
    rewrite Alloc.Bmp.xform_rep; cancel.
    assumption.
    denote (_ <=p=> _) as Hp. rewrite Hp.
    rewrite xform_listpred_ptsto_fp; auto.
  Unshelve.
    all: eauto.
  Qed.
  Proof.
    unfold rep; intros.
    cancel.
  Qed.
  Proof.
    cbv; auto.
  Qed.
  Proof.
    unfold rep, Alloc.rep.
    cancel.
  Qed.
  Proof.
    unfold smrep, Alloc.rep in *.
    intros.
    destruct_lifts.
    rewrite H4 in *.

    eapply arrayN_ptsto_linked.
    eapply pimpl_trans; eauto.
    eapply listpred_pimpl_replace.
    cancel.
  Qed.
  Proof.
    unfold init, rep; intros.
    step.
    step.
    eapply listpred_seq_smrep; eauto.
  Qed.
  Proof.
    unfold init_nofree, rep; intros.
    step.
    step.
  Qed.
  Proof.
    unfold steal, rep, bn_valid.
    step.
    prestep. norm. cancel.
    intuition simpl.
    pred_apply.
    denote pimpl as Hx; rewrite Hx.
    cancel; cancel.
    unfold smrep in *.
    rewrite listpred_remove in *|- by eauto using ptsto_conflict.
    pred_apply; cancel.
    eauto.
    Unshelve. all: try exact addr_eq_dec; auto.
  Qed.
  Proof.
    unfold alloc, rep, bn_valid.
    hoare.
    match goal with
    | [ H1 : (_ =p=> ?F * _)%pred, H2 : context [ ?F ] |- _ ] => rewrite H1 in H2
    end.
    unfold smrep.
    or_r; norm. cancel.
    intuition eauto.
    pred_apply; cancel.
    pred_apply; unfold smrep.
    rewrite listpred_remove; eauto using ptsto_conflict.
    cancel.
  Qed.
  Proof.
    unfold free, rep, bn_valid.
    hoare.
    exists (list2nmem m); pred_apply; cancel.
    unfold FP in *; eauto.
  Qed.
  Proof.
    intros; cancel.
  Qed.
  Proof.
    unfold smrep.
    cancel.
  Qed.
  Proof.
    unfold freevec.
    step.

    prestep; norml.
    denote Fm as Hx.
    denote smrep as Hs.

    destruct l.
    denote (_ < _) as Hy; simpl in Hy; inversion Hy.
    rewrite listpred_isolate with (i := 0) in Hx, Hs by (rewrite skipn_length; omega).
    rewrite skipn_selN, Nat.add_0_r in Hx, Hs.

    (*** extract the exis from |->? *)
    apply sep_star_reorder_helper in Hx.
    apply pimpl_exists_r_star_r in Hx; destruct Hx as [ [? ?] ?].
    destruct_lift Hs.
    safecancel.
    rewrite selN_cons_fold; apply Forall_selN; auto.
    eauto.
    rewrite sep_star_assoc_1, sep_star_comm.
    eauto.

    step.
    rewrite removeN_0_skipn; cancel.
    rewrite selN_cons_fold.
    replace ([n]) with (rev [n]) by auto.
    rewrite <- rev_app_distr.
    rewrite app_comm_cons, <- rev_unit.
    rewrite <- firstn_S_selN by auto.
    cancel.
    rewrite removeN_0_skipn; cancel.
    rewrite selN_cons_fold.
    rewrite smrep_cons.
    rewrite app_comm_cons, <- rev_unit.
    rewrite <- firstn_S_selN by auto.
    cancel.

    step.
    rewrite firstn_oob by auto.
    rewrite skipn_oob by auto.
    step.
    erewrite <- LOG.intact_hashmap_subset; eauto.
    Unshelve. all: eauto; exact tt.
  Qed.
  Proof.
    unfold Sig.xparams_ok; intuition.
    eapply goodSize_trans.
    eapply Nat.lt_le_incl; eauto.
    eapply goodSize_trans.
    eapply mult_le_compat_r; eauto.
    unfold goodSize.
    replace addrlen with (16 + 16 + 16 + 16) by (compute; auto).
    rewrite <- Nat.mul_1_r at 1.
    repeat apply mult_pow2_bound; try apply valulen_bound.
    apply one_lt_pow2.
  Qed.
  Proof.
    unfold rep, bn_valid.
    unfold Alloc.rep, Alloc.Bmp.rep, Alloc.Bmp.items_valid,
       Alloc.BmpSig.xparams_ok; intuition.
    destruct_lift H.
    eapply xparams_ok_goodSize; eauto.
  Qed.
  Proof.
    intros; split.
    unfold pimpl; intros.
    pred_apply; cancel.
    apply emp_star in H.
    eapply bn_valid_goodSize; eauto.
    cancel.
  Qed.
  Proof.
    unfold bn_valid; auto.
  Qed.
  Proof.
    unfold bn_valid; intuition.
    rewrite wordToNat_natToWord_idempotent' in H0; auto.
    eapply xparams_ok_goodSize; eauto.
    rewrite wordToNat_natToWord_idempotent'; auto.
    eapply xparams_ok_goodSize; eauto.
  Qed.
  Proof.
    unfold rep, Alloc.rep, Alloc.Bmp.rep, Alloc.Bmp.items_valid,
       Alloc.BmpSig.xparams_ok; intuition.
    destruct_lift H.
    apply bn_valid_roundtrip'; auto.
  Qed.
  Proof.
    unfold bn_valid; intuition; auto.
    rewrite H; auto.
  Qed.
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite Alloc.xform_rep_rawpred.
    cancel.
    auto.
    unfold FP; intros.
    xform_norm.
    rewrite crash_xform_ptsto.
    cancel.
  Qed.
  Proof.
    unfold smrep, Alloc.rep, Alloc.Alloc.rep in *.
    intros.
    destruct_lifts.
    denote piff as Hp; rewrite Hp in *.

    eapply arrayN_ptsto_linked.
    eapply pimpl_trans; eauto.
    eapply listpred_pimpl_replace.
    cancel.
  Unshelve.
    all: try exact addr_eq_dec. exact unit.
  Qed.
  Proof.
    intros.
    unfold mk_memstate, rep.
    cancel.
  Qed.
  Proof.
    intros.
    unfold mk_memstate, rep.
    cancel.
    rewrite Alloc.rep_clear_mscache_ok.
    cancel.
  Qed.
  Proof.
    unfold init, rep, MSLog; intros.
    step.
    step.
    eapply listpred_seq_smrep; eauto.
  Qed.
  Proof.
    unfold init_nofree, rep, MSLog; intros.
    step.
    step.
  Qed.
  Proof.
    unfold steal, rep, bn_valid, MSLog.
    step.
    prestep. norm. cancel.
    intuition simpl.
    pred_apply.
    denote pimpl as Hx; rewrite Hx.
    cancel; cancel.
    pred_apply; unfold smrep.
    rewrite listpred_remove; eauto using ptsto_conflict.
    cancel.
    eauto.
    Unshelve . all: try exact addr_eq_dec; auto.
  Qed.
  Proof.
    unfold alloc, rep, bn_valid, MSLog.
    hoare.
    match goal with
    | [ H1 : (_ =p=> ?F * _)%pred, H2 : context [ ?F ] |- _ ] => rewrite H1 in H2
    end.
    unfold smrep in *.
    rewrite listpred_remove in * by eauto using ptsto_conflict.
    or_r; cancel.
  Qed.
  Proof.
    unfold free, rep, bn_valid, MSLog.
    hoare.
    exists (list2nmem m); pred_apply; cancel.
    unfold FP in *; eauto.
  Qed.
  Proof.
    intros; cancel.
  Qed.
  Proof.
    unfold smrep.
    cancel.
  Qed.
  Proof.
    unfold freevec.
    safestep.
    eauto.
    eauto.

    prestep; norml.
    denote Fm as Hx.
    denote smrep as Hs.

    destruct l.
    denote (_ < _) as Hy; simpl in Hy; inversion Hy.
    rewrite listpred_isolate with (i := 0) in Hx, Hs by (rewrite skipn_length; omega).
    rewrite skipn_selN, Nat.add_0_r in Hx, Hs.

    (*** extract the exis from |->? *)
    apply sep_star_reorder_helper in Hx.
    apply pimpl_exists_r_star_r in Hx; destruct Hx as [ [? ?] ?].
    destruct_lift Hs.
    safecancel.
    rewrite selN_cons_fold; apply Forall_selN; auto.
    eauto.
    rewrite sep_star_assoc_1, sep_star_comm.
    eauto.

    step.
    rewrite removeN_0_skipn; cancel.
    rewrite selN_cons_fold.
    replace ([n]) with (rev [n]) by auto.
    rewrite <- rev_app_distr.
    rewrite app_comm_cons, <- rev_unit.
    rewrite <- firstn_S_selN by auto.
    cancel.
    rewrite removeN_0_skipn; cancel.
    rewrite selN_cons_fold.
    rewrite smrep_cons.
    rewrite app_comm_cons, <- rev_unit.
    rewrite <- firstn_S_selN by auto.
    cancel.

    step.
    rewrite firstn_oob by auto.
    rewrite skipn_oob by auto.
    step.
    cancel.
    erewrite <- LOG.intact_hashmap_subset; eauto.
    Unshelve. all: eauto; try exact tt. exact (LOG.mk_memstate0 (BUFCACHE.cache0 0)).
  Qed.
  Proof.
    unfold Sig.xparams_ok; intuition.
    eapply goodSize_trans.
    eapply Nat.lt_le_incl; eauto.
    eapply goodSize_trans.
    eapply mult_le_compat_r; eauto.
    unfold goodSize.
    replace addrlen with (16 + 16 + 16 + 16) by (compute; auto).
    rewrite <- Nat.mul_1_r at 1.
    repeat apply mult_pow2_bound; try apply valulen_bound.
    apply one_lt_pow2.
  Qed.
  Proof.
    unfold rep, bn_valid.
    unfold Alloc.rep, Alloc.Alloc.rep, Alloc.Alloc.Bmp.rep, Alloc.Alloc.Bmp.items_valid,
       Alloc.Alloc.BmpSig.xparams_ok; intuition.
    destruct_lift H.
    eapply xparams_ok_goodSize; eauto.
  Qed.
  Proof.
    intros; split.
    unfold pimpl; intros.
    pred_apply; cancel.
    apply emp_star in H.
    eapply bn_valid_goodSize; eauto.
    cancel.
  Qed.
  Proof.
    unfold bn_valid; auto.
  Qed.
  Proof.
    unfold bn_valid; intuition.
    rewrite wordToNat_natToWord_idempotent' in H0; auto.
    eapply xparams_ok_goodSize; eauto.
    rewrite wordToNat_natToWord_idempotent'; auto.
    eapply xparams_ok_goodSize; eauto.
  Qed.
  Proof.
    unfold rep, Alloc.rep, Alloc.Alloc.rep, Alloc.Alloc.Bmp.rep, Alloc.Alloc.Bmp.items_valid,
       Alloc.Alloc.BmpSig.xparams_ok; intuition.
    destruct_lift H.
    apply bn_valid_roundtrip'; auto.
  Qed.
  Proof.
    unfold bn_valid; intuition; auto.
    rewrite H; auto.
  Qed.
  Proof.
    unfold Alloc.rep, rep; intros.
    xform_norm.
    rewrite Alloc.xform_rep_rawpred.
    cancel.
    auto.
    unfold FP; intros.
    xform_norm.
    rewrite crash_xform_ptsto.
    cancel.
  Qed.
  Proof.
    unfold Sig.xparams_ok, ino_valid; intuition.
    eapply goodSize_trans.
    eapply Nat.lt_le_incl; eauto.
    eapply goodSize_trans.
    eapply mult_le_compat_r; eauto.
    unfold goodSize.
    replace addrlen with (16 + 16 + 16 + 16) by (compute; auto).
    rewrite <- Nat.mul_1_r at 1.
    repeat apply mult_pow2_bound; try apply valulen_bound.
    apply one_lt_pow2.
  Qed.
  Proof.
    unfold rep, ino_valid.
    unfold Alloc.rep, Alloc.Alloc.rep, Alloc.Alloc.Bmp.rep, Alloc.Alloc.Bmp.items_valid,
       Alloc.Alloc.BmpSig.xparams_ok; intuition.
    destruct_lift H.
    eapply xparams_ok_goodSize; eauto.
  Qed.
  Proof.
    intros; split.
    unfold pimpl; intros.
    pred_apply; cancel.
    apply emp_star in H.
    eapply ino_valid_goodSize; eauto.
    cancel.
  Qed.
  Proof.
    unfold ino_valid; intuition.
    rewrite wordToNat_natToWord_idempotent'; auto.
    eapply xparams_ok_goodSize; eauto.
  Qed.
  Proof.
    unfold rep, Alloc.rep, Alloc.Alloc.rep, Alloc.Alloc.Bmp.rep, Alloc.Alloc.Bmp.items_valid,
       Alloc.Alloc.BmpSig.xparams_ok; intuition.
    destruct_lift H.
    apply ino_valid_roundtrip'; auto.
  Qed.
  Proof.
    auto using Alloc.rep_clear_cache.
  Qed.