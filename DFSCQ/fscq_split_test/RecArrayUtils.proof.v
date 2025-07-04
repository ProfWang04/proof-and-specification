  Proof.
    unfold val2word, word2val, eq_rec_r, eq_rec; simpl; intros.
    rewrite eq_rect_nat_double.
    erewrite eq_rect_eq_dec; auto.
  Qed.
  Proof.
    unfold val2word, word2val, eq_rec_r, eq_rec; simpl; intros.
    rewrite eq_rect_nat_double.
    erewrite eq_rect_eq_dec; auto.
  Qed.
  Proof.
    unfold block2val, val2block; small_t.
  Qed.
  Proof.
    unfold block2val, val2block; small_t.
  Qed.
  Proof.
    induction bl; intros; small_t.
    destruct i; rewrite Forall_forall in *.
    small_t; apply H; intuition.
    apply IHbl; rewrite Forall_forall.
    small_t; apply H; intuition.
  Qed.
  Proof.
    generalize blocksz_ok.
    rewrite valulen_is.
    intros; intro.
    rewrite H0 in H.
    discriminate.
  Qed.
  Proof.
    pose proof items_per_val_not_0; omega.
  Qed.
  Proof.
    pose proof items_per_val_not_0; omega.
  Qed.
  Proof.
    unfold block0, item0, val2block, blocktype, val2word.
    generalize blocksz_ok.
    rewrite blocksz_ok; intros; simpl.
    unfold eq_rec.
    rewrite <- (eq_rect_eq_dec eq_nat_dec).
    generalize dependent items_per_val.
    induction n; simpl; auto; intros.
    erewrite <- IHn; small_t.
    unfold Rec.of_word at 1 3.
    rewrite split1_zero.
    rewrite split2_zero; auto.
  Qed.
  Proof.
    unfold item0; auto.
  Qed.
  Proof.
    unfold block0, val2block; auto.
  Qed.
  Proof.
    intros; rewrite Forall_forall in *; intros.
    destruct (setlen_In _ _ _ _ H0); small_t.
  Qed.
  Proof.
    induction nr; simpl; auto.
  Qed.
  Proof.
    unfold list_chunk; intros.
    apply list_chunk'_length.
  Qed.
  Proof.
    induction nr; simpl; auto.
  Qed.
  Proof.
    unfold nopad_list_chunk; intros.
    apply nopad_list_chunk'_length.
  Qed.
  Proof.
    induction nr; small_t.
    apply Forall_cons; small_t.
  Qed.
  Proof.
    intros; eapply list_chunk'_wellformed; eauto.
  Qed.
  Proof.
    intros; apply list_chunk_length.
  Qed.
  Proof.
    unfold list_chunk; small_t.
    rewrite divup_0; small_t.
  Qed.
  Proof.
    induction nr; small_t.
    apply Forall_cons; small_t.
  Qed.
  Proof.
    intros until i0; apply Forall_forall.
    unfold list_chunk.
    apply list_chunk'_Forall_length.
  Qed.
  Proof.
    intros.
    destruct (lt_dec i (length (list_chunk l items_per_val item0))).
    eapply list_chunk_In_length; eauto.
    rewrite selN_oob by small_t.
    apply block0_wellformed.
  Qed.
  Proof.
    induction nr; small_t. inversion H.
    destruct i. small_t.
    erewrite IHnr by small_t.
    rewrite skipn_skipn; simpl.
    f_equal; f_equal; omega.
  Qed.
  Proof.
    unfold list_chunk; intros.
    destruct (lt_dec i (divup (length l) n)).
    apply list_chunk'_spec; auto.
    rewrite selN_oob by small_t.
    rewrite skipn_oob; small_t.
  Qed.
  Proof.
    intros; apply list_chunk_spec'; eauto.
  Qed.
  Proof.
    induction nr; cbn; intros.
    omega.
    destruct i; cbn; auto.
    rewrite IHnr by omega.
    rewrite plus_comm.
    rewrite skipn_skipn.
    reflexivity.
  Qed.
  Proof.
    unfold nopad_list_chunk.
    intros.
    rewrite nopad_list_chunk'_spec; auto.
  Qed.
  Proof.
    induction k; intros; simpl; auto; rewrite Nat.sub_0_r; auto.
  Qed.
  Proof.
    unfold list_chunk; intros.
    rewrite skipn_length.
    destruct (Nat.eq_dec n 0).
    subst; simpl; auto.
    destruct (lt_dec (length l) n).
    replace (length l - n) with 0 by omega.
    rewrite divup_0.
    apply Nat.lt_le_incl in l0; apply divup_le_1 in l0.
    destruct (Nat.eq_dec (divup (length l) n) 1).
    rewrite e.
    setoid_rewrite skipn_oob at 2; simpl; auto.
    replace (divup (length l) n) with 0 by omega.
    simpl; auto.
    rewrite divup_sub_1 by omega.
    apply list_chunk'_skipn_1.
  Qed.
  Proof.
    induction i; intros.
    simpl; auto.
    simpl (S i * n).
    rewrite <- skipn_skipn'.
    rewrite <- IHi; auto.
    rewrite list_chunk_skipn_1.
    rewrite skipn_skipn.
    replace (S i) with (i + 1) by omega; auto.
  Qed.
  Proof.
    intros.
    destruct (Nat.eq_dec n 0).
    subst; simpl; rewrite skipn_nil; auto.
    destruct (lt_dec (length l) (n * i)); autorewrite with core.
    replace (length l - i * n) with 0 by nia.
    rewrite divup_0.
    rewrite skipn_oob; autorewrite with core; simpl; auto.
    autorewrite with lists.
    apply divup_le; nia.
    rewrite divup_sub by nia.
    rewrite skipn_repeat; auto.
  Qed.
  Proof.
    induction i; intros; simpl; auto.
    repeat rewrite setlen_inbound by (autorewrite with core lists; nia).
    rewrite firstn_firstn.
    rewrite Nat.min_l by nia.
    setoid_rewrite <- IHi at 2; autorewrite with core; try nia.
    f_equal; f_equal.
    apply skipn_firstn_comm.
  Qed.
  Proof.
    intros.
    destruct (le_lt_dec (i * n) (length l)).
    apply list_chunk'_firstn'; auto.
    rewrite firstn_oob; auto.
    nia.
  Qed.
  Proof.
    induction m; destruct n; small_t.
    inversion H.
    rewrite IHm; small_t.
  Qed.
  Proof.
    unfold list_chunk; small_t.
    rewrite Nat.min_l; small_t.
    rewrite list_chunk'_firstn.
    rewrite firstn_list_chunk'; small_t.
    apply divup_mul_ge; nia.
  Qed.
  Proof.
    intros.
    destruct (Nat.eq_dec n 0); small_t. small_t.
    destruct (le_lt_dec (i * n) (length l)).
    apply list_chunk_firstn'; small_t.
    rewrite firstn_oob by nia.
    rewrite firstn_oob; small_t.
  Qed.
  Proof.
    small_t; rewrite list_chunk_spec.
    rewrite firstn_sum_split; f_equal.
    rewrite setlen_inbound; small_t.
  Qed.
  Proof.
    unfold setlen; intros.
    rewrite firstn_app_l.
    rewrite firstn_firstn; rewrite Nat.min_l; auto.
    rewrite firstn_length.
    apply Min.min_glb; auto.
  Qed.
  Proof.
    induction na; small_t.
    replace (a ++ b) with b; auto.
    rewrite length_nil with (l := a); auto; omega.
    repeat rewrite setlen_inbound by (autorewrite with lists; nia).
    rewrite firstn_app_l by nia.
    f_equal.
    rewrite skipn_app_l by nia.
    rewrite IHna; auto.
    autorewrite with core; nia.
  Qed.
  Proof.
    unfold list_chunk; intros.
    rewrite app_length; autorewrite with core lists.
    repeat (rewrite H0; rewrite Nat.mul_comm; rewrite divup_mul by auto).
    rewrite <- list_chunk'_app; auto.
    f_equal.
    replace (na * sz + length b) with (length b + sz * na) by lia.
    rewrite divup_add by auto; omega.
  Qed.
  Proof.
    intros; repeat (try split; rewrite Forall_forall in *; small_t).
    destruct (in_app_or a b x); small_t.
  Qed.
  Proof.
    unfold nils; intros.
    apply repeat_length.
  Qed.
  Proof.
    unfold ipack; intros.
    rewrite map_length.
    setoid_rewrite list_chunk_length; auto.
  Qed.
  Proof.
    unfold nopad_ipack; cbn.
    intros.
    rewrite map_length.
    rewrite nopad_list_chunk_length; auto.
  Qed.
  Proof.
    unfold ipack; intros.
    rewrite <- map_app; f_equal.
    eapply list_chunk_app; eauto.
    rewrite Nat.mul_comm; eauto.
  Qed.
  Proof.
    unfold ipack.
    rewrite list_chunk_nil; auto.
  Qed.
  Proof.
    unfold ipack, list_chunk; intros.
    rewrite H.
    rewrite divup_same by auto; simpl.
    rewrite setlen_inbound by omega.
    rewrite firstn_oob by omega; auto.
  Qed.
  Proof.
    intros; unfold iunpack.
    rewrite ipack_one by auto; simpl.
    autorewrite with core; split; auto.
  Qed.
  Proof.
    induction n; intros; simpl; auto.
    destruct (le_gt_dec k (length l)).
    repeat rewrite setlen_inbound by (auto; rewrite app_length; omega).
    rewrite firstn_app_l, skipn_app_l by auto.
    rewrite IHn; auto.

    rewrite setlen_app_r by omega.
    unfold setlen at 2; rewrite firstn_oob by omega.
    rewrite setlen_repeat.
    f_equal.
    rewrite skipn_app_r_ge by omega.
    setoid_rewrite skipn_oob at 2; try omega.
    destruct (le_gt_dec (k - length l) z).
    rewrite skipn_repeat.
    setoid_rewrite <- app_nil_l at 2.
    apply IHn.
    rewrite skipn_oob by (rewrite repeat_length; omega); auto.
  Qed.
  Proof.
    unfold ipack, list_chunk; intros.
    f_equal.
    rewrite list_chunk'_app_def, app_length.
    rewrite divup_add_small; auto.
    rewrite repeat_length; auto.
  Qed.
  Proof.
    intros.
    rewrite Forall_forall in *; intros.
    apply H; eapply in_firstn_in; eauto.
  Qed.
  Proof.
    intros.
    rewrite Forall_forall in *; intros.
    apply H; eapply in_skipn_in; eauto.
  Qed.
  Proof.
    cbn; intros.
    rewrite setlen_oob by omega.
    generalize dependent itemtype.
    induction n; cbn; intros.
    f_equal. auto using app_nil_r.
    destruct l; cbn in *;
      repeat rewrite Rec.cons_to_word;
      repeat rewrite Rec.to_of_id.
    clear IHn. clear H.
    induction n; cbn.
    unfold Rec.to_word.
    rewrite combine_wzero.
    reflexivity.
    rewrite Rec.cons_to_word, Rec.to_of_id.
    rewrite IHn.
    rewrite combine_wzero.
    reflexivity.
    f_equal.
    apply IHn. omega.
  Qed.
  Proof.
    induction nr; small_t.
    apply length_nil in H0; rewrite H0.
    rewrite ipack_nil; simpl; small_t.

    erewrite <- firstn_skipn with (n := items_per_val) (l := items).
    rewrite ipack_app with (na := 1).
    rewrite fold_left_app.
    rewrite IHnr; auto.
    rewrite app_assoc.
    f_equal.

    rewrite iunpack_ipack_one; auto.
    rewrite firstn_length_l; lia.
    rewrite skipn_length; nia.
    rewrite firstn_length; lia.
  Qed.
  Proof.
    intros; eapply iunpack_ipack'; eauto.
  Qed.
  Proof.
    induction n; intros.
    simpl; auto.

    destruct (lt_dec n (length (ipack items))).
    rewrite firstn_S_selN with (def := $0) by auto.
    rewrite fold_left_app.
    erewrite IHn; simpl; eauto.

    rewrite ipack_length in l.
    unfold iunpack, ipack; rewrite Nat.add_comm.
    erewrite firstn_list_chunk_app; [ f_equal | | apply eq_refl ].
    erewrite selN_map, val2block2val_id; eauto.
    apply Forall_selN.
    apply list_chunk_wellformed; auto.
    setoid_rewrite list_chunk_length; auto.
    setoid_rewrite list_chunk_length; auto.

    rewrite H0 in *.
    rewrite divup_mul in l by auto.
    apply lt_le_S in l; eapply mult_le_compat_r in l; eauto.

    repeat rewrite firstn_oob; try omega.
    eapply iunpack_ipack; eauto.
    rewrite ipack_length in n0.
    rewrite H0 in *.
    rewrite divup_mul in n0 by auto.
    apply Nat.nlt_ge in n0.
    apply mult_le_compat; omega.
  Qed.
  Proof.
    intros.
    unfold iunpack.
    rewrite app_nil_l.
    rewrite ipack_one, block2val2block_id; auto.
    unfold val2block, blocktype.
    rewrite Rec.array_of_word_length.
    auto.
  Qed.
  Proof.
    intros.
    unfold iunpack.
    rewrite app_length, H.
    f_equal.
    unfold val2block, blocktype, item.
    apply Rec.array_of_word_length.
  Qed.
  Proof.
    induction l; simpl; intros.
    omega.

    erewrite IHl.
    instantiate (1 := nr + items_per_val). omega.
    apply iunpack_length; auto.
  Qed.
  Proof.
    intros.
    erewrite fold_left_iunpack_length'; eauto.
    omega.

    Unshelve.
    constructor.
  Qed.
  Proof.
    induction l; intros; simpl.
    rewrite <- ipack_nil.
    auto.

    rewrite IHl at 2.
    erewrite iunpack_ipack'.
    erewrite ipack_app.
    rewrite <- ipack_iunpack_one.
    rewrite cons_app.
    f_equal; auto.
    unfold iunpack.
    rewrite app_nil_l.
    unfold val2block, blocktype.
    rewrite Rec.array_of_word_length.
    instantiate (1:=1); omega.
    auto.
    instantiate (1:=length l).
    apply fold_left_iunpack_length.
    auto.
  Qed.
  Proof.
    unfold ipack, nopad_ipack.
    intros.
    eapply selN_map_eq; cbn; intros.
    destruct (lt_dec i (divup (length x) items_per_val)).
    - rewrite list_chunk_spec.
      rewrite nopad_list_chunk_spec by auto.
      unfold block2val, blocktype in *.
      destruct (lt_dec (length x - i * items_per_val) items_per_val).
      rewrite to_word_setlen.
      rewrite firstn_oob; auto.
      all: rewrite ?skipn_length; auto.
      cbv in *; omega.
      rewrite setlen_inbound; auto.
      rewrite skipn_length; omega.
    - repeat rewrite selN_oob by (autorewrite with core; apply Nat.le_ngt; eauto).
      reflexivity.
    - autorewrite with core. auto.
  Qed.
  Proof.
    intros.
    rewrite firstn_length, skipn_length.
    apply Nat.min_glb_lt.
    apply Nat.mod_upper_bound; auto.
    rewrite Nat.mod_eq, Nat.mul_comm by auto.
    enough (ix >= ix / items_per_val * items_per_val).
    omega.
    rewrite Nat.mul_comm.
    apply Nat.mul_div_le; auto.
  Qed.
  Proof.
    unfold ipack; intros.
    rewrite val2block2val_selN_id by auto.
    rewrite list_chunk_spec.
    setoid_rewrite selN_app1.
    rewrite selN_firstn.
    rewrite skipn_selN.
    rewrite Nat.mul_comm.
    rewrite <- Nat.div_mod; auto.
    apply Nat.mod_upper_bound; auto.
    eapply mod_lt_length_firstn_skipn; auto.
  Qed.
  Proof.
    intros.
    eapply list_selN_ext; intros.
    rewrite length_updN.
    setoid_rewrite list_chunk_length; rewrite length_updN; auto.
    repeat rewrite list_chunk_spec.

    destruct (Nat.eq_dec pos (ix / items_per_val)); subst.
    rewrite selN_updN_eq; unfold setlen.
    setoid_rewrite skipn_length; rewrite length_updN.
    repeat rewrite updN_app1; [ f_equal | ].
    rewrite <- updN_firstn_comm.
    rewrite updN_skipn; repeat f_equal.
    rewrite Nat.mul_comm, Nat.add_comm, <- Nat.div_mod; auto.
    apply mod_lt_length_firstn_skipn; auto.
    setoid_rewrite list_chunk_length.
    apply div_lt_divup; auto.

    rewrite length_updN, list_chunk_length in H0.
    rewrite selN_updN_ne by auto.
    rewrite list_chunk_spec.
    rewrite setlen_skipn_updN_absorb; auto.
    apply not_eq in n; destruct n.
    right; apply lt_div_mul_add_le; auto.
    left; apply div_lt_mul_lt; auto.
  Qed.
  Proof.
    unfold ipack; intros.
    rewrite val2block2val_selN_id by auto.
    rewrite <- map_updN; f_equal.
    apply list_chunk_updN_divmod; auto.
  Qed.
  Proof.
    unfold block2val, item0.
    rewrite <- Rec.of_word_zero_list.
    rewrite Rec.to_of_id.
    unfold word2val, eq_rec_r, eq_rect, eq_rec, eq_rect.
    case_eq (eq_sym blocksz_ok); intros; auto.
  Qed.
  Proof.
    induction n; simpl; intros.
    rewrite ipack_nil; auto.
    rewrite <- repeat_app.
    erewrite ipack_app with (na := 1) by (rewrite repeat_length; omega).
    rewrite cons_app, IHn; f_equal.
    rewrite ipack_one by (rewrite repeat_length; auto); f_equal.
    rewrite block2val_repeat_item0; auto.
  Qed.
  Proof.
    intros.
    rewrite Forall_forall in *; intuition.
    apply in_updN in H1; destruct H1; subst; eauto.
  Qed.
  Proof.
    intros.
    rewrite synced_list_length, ipack_length.
    setoid_rewrite H0.
    rewrite divup_mul; auto.
  Qed.
  Proof.
    intros.
    repeat rewrite ipack_length.
    setoid_rewrite H; setoid_rewrite H0; auto.
  Qed.
  Proof.
    intros.
    apply ifind_list_ok_facts with (d := item0) in H1 as [Hm [ Hb [ Hc Hi ] ] ].
    apply list_chunk_wellformed in H.
    rewrite synced_list_selN in Hb; simpl in Hb.
    unfold ipack in *; rewrite val2block2val_selN_id in * by auto.
    rewrite list_chunk_spec, setlen_length in *.

    rewrite H2.
    eapply lt_le_trans; eauto.
    setoid_rewrite <- Nat.mul_1_l at 5.
    rewrite <- Nat.mul_add_distr_r.
    apply Nat.mul_le_mono_r; omega.
  Qed.
  Proof.
    intros.
    apply ifind_list_ok_facts with (d := item0) in H1 as [Hm [ Hb [ Hc Hi ] ] ].
    rewrite <- Hi.
    rewrite synced_list_selN; simpl.
    apply list_chunk_wellformed in H.
    rewrite synced_list_selN in Hb; simpl in Hb.
    unfold ipack in *; rewrite val2block2val_selN_id in * by auto.
    rewrite list_chunk_spec, setlen_length in *.
    unfold setlen; rewrite selN_app1.
    rewrite selN_firstn, skipn_selN, le_plus_minus_r by omega; auto.
    rewrite firstn_length, skipn_length.
    apply Nat.min_glb_lt; try omega.
    setoid_rewrite H2.
    apply lt_add_lt_sub in Hb; auto.
    eapply lt_le_trans; eauto.
    rewrite <- Nat.mul_sub_distr_r, <- Nat.mul_1_l at 1.
    apply Nat.mul_le_mono_r; omega.
  Qed.
  Proof.
    intros.
    destruct (lt_dec ix (i * items_per_val)); [ eauto | subst ].

    assert (ix < length items).
    setoid_rewrite H4.
    eapply lt_le_trans; eauto.
    setoid_rewrite Nat.mul_comm.
    rewrite Nat.add_comm, mult_n_Sm.
    apply Nat.mul_le_mono_pos_l; auto.

    rewrite <- ipack_selN_divmod; auto.
    rewrite Nat.div_mod with (x := ix) (y := items_per_val) at 3 by auto.
    apply ifind_list_none.
    replace (ix / items_per_val) with i.
    rewrite Nat.mul_comm.
    rewrite synced_list_selN in H0; simpl in H0; auto.

    destruct (lt_eq_lt_dec i (ix / items_per_val)).
    destruct s; auto.
    apply lt_div_mul_add_le in l; auto; omega.
    contradict n.
    apply div_lt_mul_lt; auto.

    unfold ipack; erewrite selN_map.
    rewrite val2block2val_id.
    rewrite list_chunk_spec, setlen_length.
    apply Nat.mod_upper_bound; auto.
    apply Forall_selN.
    apply list_chunk_wellformed; auto.
    setoid_rewrite list_chunk_length; apply div_lt_divup; auto.
    setoid_rewrite list_chunk_length; apply div_lt_divup; auto.
  Qed.
  Proof.
    unfold selN_val2block; intros.
    erewrite Rec.word_selN'_equiv by auto.
    reflexivity.
  Qed.
  Proof.
    unfold block2val_updN_val2block; intros.
    erewrite Rec.word_updN'_equiv by auto.
    reflexivity.
  Qed.