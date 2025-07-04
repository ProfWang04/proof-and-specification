  Proof.
    destruct flag, p; intros; reflexivity.
  Qed.
  Proof.
    destruct flag, p; intros; reflexivity.
  Qed.
  Proof.
    destruct flag, p; intros; reflexivity.
  Qed.
  Proof.
    unfold rep; intros.
    norm'l; unfold stars; simpl.
    rewrite INODE.rep_length_pimpl at 1.
    rewrite listmatch_length_pimpl at 1.
    cancel.
  Qed.
  Proof.
    unfold rep, rep_alt; split; destruct msalloc; simpl.
    - cancel.
    - norml; unfold stars; simpl.
      rewrite INODE.rep_bxp_switch at 1 by eauto.
      cancel.
      unfold smrep. cancel.
    - cancel.
    - norml; unfold stars; simpl.
      rewrite INODE.rep_bxp_switch at 1 by eauto.
      cancel.
      unfold smrep. cancel.
  Qed.
  Proof.
    unfold rep; intros; cancel.
    rewrite <- BALLOCC.rep_clear_mscache_ok. cancel.
    rewrite <- BALLOCC.rep_clear_mscache_ok. cancel.
  Qed.
  Proof.
    unfold rep; intros; cancel.
    unfold clear_caches.
    rewrite listmatch_map_l.
    unfold file_match, clear_cache; simpl.
    reflexivity.

    rewrite locked_eq.
    unfold cache_rep, clear_caches, clear_cache.
    rewrite map_map; simpl.
    denote smrep as Hd. clear Hd.
    denote locked as Hl. clear Hl.
    generalize 0.
    induction flist; simpl; intros.
    apply BFM.mm_init.
    specialize (IHflist (S n)).
    pred_apply; cancel.
  Unshelve.
    exact unit.
  Qed.
  Proof.
    unfold BFILE.rep. cancel.
    apply INODE.rep_clear_cache.
    cancel.
  Qed.
  Proof.
    intros n.
    generalize 0 as st.
    induction n; cbn; auto.
    intros.
    specialize (IHn (S st)).
    rewrite IHn.
    unfold smrep_single_helper, smrep_single.
    cbn.
    split; cancel.
    unfold SS.For_all. intros.
    rewrite <- SetFacts.empty_iff; eauto.
  Qed.
  Proof.
    cbn; intros.
    unfold remove_dirty_vec, smrep_single_helper.
    rewrite listpred_map.
    destruct Map.find eqn:Hfind.
    rewrite M.find_add_eq.
    unfold smrep_single.
    rewrite H.
    rewrite listpred_split with (n := n).
    unfold SS.For_all.
    - cancel.
      rewrite listpred_pimpl_replace with (l := firstn _ _).
      rewrite listpred_pimpl_replace with (l := skipn _ _).
      solve [apply pimpl_refl | apply sep_star_comm].
      cancel.
      cancel.
      denote (b = true) as Hb. apply Hb.
      intros Ha.
      denote (In _ (map _ _)) as Hi. eapply Hi in Ha as Hc.
      denote False as Hf. eapply Hf.
      eapply in_fold_right_remove_notin.
      rewrite InA_alt.
      intuition repeat deex.
      eapply in_nodup_firstn_not_skipn; eauto.
      all: rewrite ?firstn_map_comm, ?skipn_map_comm; eauto.
      eauto using in_map.
      denote SS.remove as Hr.
      eapply in_fold_right_remove in Hr.
      rewrite InA_alt in Hr.
      intuition repeat deex.
      erewrite <- firstn_map_comm.
      eapply in_nodup_not_skipn_firstn; eauto.
      denote False as Hf.
      intuition; apply Hf. eexists; intuition eauto.
      rewrite <- skipn_map_comm; auto.
    - rewrite Hfind.
      unfold smrep_single.
      rewrite H.
      cancel.
      rewrite listpred_split with (n := n).
      cancel.
      apply listpred_pimpl_replace; cancel.
      unfold SS.For_all.
      setoid_rewrite SetFacts.empty_iff.
      intuition.
  Unshelve.
    all: eauto; constructor.
  Qed.
  Proof.
    cbn; intros.
    unfold clear_dirty, smrep_single_helper.
    rewrite listpred_map.
    rewrite M.find_remove_eq.
    unfold smrep_single.
    cancel.
    apply listpred_pimpl_replace.
    cancel.
    unfold SS.For_all.
    setoid_rewrite SetFacts.empty_iff.
    intuition.
  Qed.
  Proof.
    unfold rep, block_is_unused, block_belong_to_file; intuition.
    rewrite <- locked_eq with (x := bn) in H3.
    destruct_lift H.
    rewrite listmatch_isolate with (i := inum) in H.
    unfold file_match at 2 in H.
    erewrite listmatch_isolate with (i := off) (a := (BFData files ⟦ inum ⟧)) in H by simplen.
    erewrite selN_map in H; eauto.
    unfold BALLOCC.rep in H; destruct_lift H.
    unfold BALLOCC.Alloc.rep in H; destruct_lift H.
    unfold BALLOCC.Alloc.Alloc.rep in H; destruct_lift H.
    destruct flag; simpl in *.
    - denote (locked _ = _) as Hl.
      rewrite locked_eq in Hl.
      rewrite <- Hl in H; clear Hl.
      match goal with H: context [ptsto bn ?a], Hl: _ <=p=> _ |- _ =>
        rewrite Hl, listpred_pick in H by eauto; destruct_lift H
      end.
      eapply ptsto_conflict_F with (m := m) (a := bn).
      pred_apply.
      cancel.
      rewrite <- surjective_pairing. cancel.
    - denote (locked _ = _) as Hl.
      rewrite locked_eq in Hl.
      rewrite <- Hl in H; clear Hl.
      match goal with H: context [ptsto bn ?a], Hl: _ <=p=> _ |- _ =>
        rewrite Hl, listpred_pick in H by eauto; destruct_lift H
      end.
      eapply ptsto_conflict_F with (m := m) (a := bn).
      pred_apply.
      cancel.
      rewrite <- surjective_pairing. cancel.
    - erewrite listmatch_length_r; eauto.
      destruct (lt_dec inum (length ilist)); eauto.
      rewrite selN_oob in * by omega.
      unfold INODE.inode0 in H2; simpl in *; omega.
    - destruct (lt_dec inum (length ilist)); eauto.
      rewrite selN_oob in * by omega.
      unfold INODE.inode0 in *; simpl in *; omega.
  Grab Existential Variables.
    all: eauto.
    all: solve [exact ($0, nil) | exact bfile0].
  Qed.
  Proof.
    unfold ilist_safe; intuition.
  Qed.
  Proof.
    unfold ilist_safe; intros.
    destruct H.
    destruct H0.
    split.
    - eapply incl_tran; eauto.
    - intros.
      specialize (H2 _ _ _ H3).
      destruct H2; eauto.
      right.
      unfold block_is_unused in *.
      eauto.
  Qed.
  Proof.
    intros.
    destruct (lt_dec off (length ilist)).
    - unfold ilist_safe, block_belong_to_file.
      intuition auto.
      apply incl_refl.
      destruct (addr_eq_dec off inum); subst.
      rewrite selN_updN_eq in * by auto.
      rewrite H in *; cbn in *; omega.
      rewrite selN_updN_ne in * by auto.
      intuition auto.
    - rewrite updN_oob by omega; auto.
  Qed.
  Proof.
    intros.
    destruct (lt_dec inum (length ilist)); eauto.
    unfold block_belong_to_file in *.
    rewrite selN_oob in H by omega.
    simpl in H.
    omega.
  Qed.
  Proof.
    intros.
    inversion H.
    auto.
  Qed.
  Proof.
    unfold rep; intros.
    destruct_lift H.
    rewrite listmatch_length_pimpl in H; destruct_lift H.
    rewrite listmatch_extract with (i := inum) in H.
    2: substl (length flist); eapply block_belong_to_file_inum_ok; eauto.

    assert (inum < length ilist) by ( eapply block_belong_to_file_inum_ok; eauto ).
    assert (inum < length flist) by ( substl (length flist); eauto ).

    denote block_belong_to_file as Hx; assert (Hy := Hx).
    unfold block_belong_to_file in Hy; intuition.
    unfold file_match at 2 in H.
    rewrite listmatch_length_pimpl with (a := BFData _) in H; destruct_lift H.
    denote! (length _ = _) as Heq.
    rewrite listmatch_extract with (i := off) (a := BFData _) in H.
    2: rewrite Heq; rewrite map_length; eauto.

    erewrite selN_map in H; eauto.
    eapply rep_used_block_eq_Some_helper.
    apply eq_sym.
    rewrite <- list2nmem_sel_inb.

    eapply ptsto_valid.
    pred_apply.
    eassign (natToWord addrlen O).
    cancel.

    eapply list2nmem_inbound.
    pred_apply.
    cancel.

  Grab Existential Variables.
    all: eauto.
  Qed.
  Proof.
    unfold smrep_single_helper.
    unfold put_dirty.
    intros.
    rewrite MapFacts.add_neq_o by auto.
    auto.
  Qed.
  Proof.
    unfold smrep_single_helper.
    unfold put_dirty.
    intros.
    rewrite MapFacts.remove_neq_o by auto.
    auto.
  Qed.
  Proof.
    induction ilist; cbn.
    split; cancel.
    intros.
    rewrite smrep_single_helper_add_oob by omega.
    rewrite IHilist by omega.
    auto.
  Qed.
  Proof.
    induction ilist; cbn.
    split; cancel.
    intros.
    rewrite smrep_single_helper_remove_oob by omega.
    rewrite IHilist by omega.
    auto.
  Qed.
  Proof.
    unfold arrayN_ex.
    intros.
    destruct (lt_dec inum (length ilist)).
    - rewrite arrayN_smrep_single_helper_add_oob.
      rewrite arrayN_smrep_single_helper_add_oob.
      auto.
      autorewrite with core. omega.
      rewrite firstn_length_l; omega.
    - rewrite skipn_oob by omega.
      rewrite firstn_oob by omega.
      rewrite arrayN_smrep_single_helper_add_oob by omega.
      rewrite arrayN_smrep_single_helper_add_oob by omega.
      auto.
  Qed.
  Proof.
    unfold arrayN_ex.
    intros.
    destruct (lt_dec inum (length ilist)).
    - rewrite arrayN_smrep_single_helper_remove_oob.
      rewrite arrayN_smrep_single_helper_remove_oob.
      auto.
      autorewrite with core. omega.
      rewrite firstn_length_l; omega.
    - rewrite skipn_oob by omega.
      rewrite firstn_oob by omega.
      rewrite arrayN_smrep_single_helper_remove_oob by omega.
      rewrite arrayN_smrep_single_helper_remove_oob by omega.
      auto.
  Qed.
  Proof.
    unfold put_dirty.
    auto using arrayN_ex_smrep_single_helper_add.
  Qed.
  Proof.
    unfold remove_dirty_vec.
    intros.
    destruct Map.find; auto.
    auto using arrayN_ex_smrep_single_helper_add.
  Qed.
  Proof.
    unfold clear_dirty.
    auto using arrayN_ex_smrep_single_helper_remove.
  Qed.
  Proof.
    induction l; cbn; intros.
    omega.
    subst.
    destruct i; cbn.
    auto.
    inversion H0; subst.
    intuition subst.
    eapply H3.
    eapply in_selN; omega.
    eapply IHl; eauto; omega.
  Qed.
  Proof.
    induction l; cbn; intros.
    omega.
    subst.
    inversion H0; subst.
    destruct i; cbn.
    auto.
    intuition subst.
    eapply IHl; eauto; omega.
  Qed.
  Proof.
    intros.
    unfold removeN.
    rewrite in_app_iff.
    intuition.
    eapply selN_NoDup_notin_firstn; eauto.
    eapply selN_NoDup_notin_skipn; eauto.
  Qed.
  Proof.
    unfold smrep_single.
    cancel.
    eapply in_selN_exists in H; deex.
    rewrite listpred_nodup_piff.
    2: eauto using weq.
    cancel.
    eapply listpred_pimpl_replace; cancel.
    intuition.
    destruct_lifts.
    eapply ptsto_conflict with (a := #y) (m := m').
    pred_apply; cancel.
    unfold SS.For_all in *.
    intuition.
    rewrite SS.add_spec in *.
    intuition. subst.
    eapply in_map; auto.
  Unshelve.
    all: apply wzero.
  Qed.
  Proof.
    unfold smrep_single_helper.
    unfold put_dirty.
    intros.
    rewrite MapFacts.add_eq_o by auto.
    unfold get_dirty.
    apply smrep_single_add. auto.
  Qed.
  Proof.
    unfold smrep.
    intros.
    cancel.
    rewrite arrayN_except with (i := inum) by auto.
    rewrite arrayN_except with (i := inum) by auto.
    rewrite arrayN_ex_smrep_single_helper_put_dirty.
    cancel.
    rewrite smrep_single_helper_put_dirty; eauto.
    rewrite wordToNat_natToWord_idempotent' by eauto.
    cancel.
  Qed.
  Proof.
    unfold smrep_single.
    cancel.
    rewrite H.
    rewrite listpred_app; cbn.
    cancel.
    apply listpred_pimpl_replace.
    intros.
    eapply in_selN_exists in H1; deex.
    cancel.
    rewrite H.
    unfold SS.For_all in *.
    intros x; intros.
    rewrite map_app.
    apply in_or_app.
    rewrite SS.add_spec in *.
    intuition. subst.
    right.
    cbn; auto.
  Unshelve.
    all: apply wzero.
  Qed.
  Proof.
    unfold smrep_single_helper.
    unfold put_dirty.
    intros.
    rewrite MapFacts.add_eq_o by auto.
    unfold get_dirty.
    eapply smrep_single_add_new; auto.
  Qed.
  Proof.
    unfold smrep.
    intros.
    cancel.
    rewrite arrayN_except with (i := inum) by auto.
    rewrite arrayN_except_upd.
    rewrite arrayN_ex_smrep_single_helper_put_dirty.
    cancel.
    replace bn with (# (@natToWord addrlen bn)) in *.
    rewrite natToWord_wordToNat in *.
    rewrite smrep_single_helper_add_dirty. cancel.
    all: eauto.
    rewrite wordToNat_natToWord_idempotent'; auto.
  Qed.
  Proof.
    unfold smrep.
    intros.
    cancel.
    destruct (lt_dec inum (length ilist)).
    2: rewrite updN_oob by omega; cancel.

    rewrite arrayN_except_upd by auto.
    rewrite arrayN_except with (i := inum) by auto.
    cancel.

    unfold smrep_single_helper, smrep_single.
    rewrite <- H.
    reflexivity.
  Qed.
  Proof.
    cbn; intros.
    unfold smrep_single_helper, remove_dirty.
    destruct Map.find eqn:Hfind.
    rewrite M.find_add_eq.
    unfold smrep_single.
    rewrite H.
    rewrite listpred_isolate with (i := off) by auto. cancel.
    rewrite listpred_pimpl_replace.
    solve [apply sep_star_comm | apply pimpl_refl].
    unfold SS.For_all in *.
    cancel.
    denote In as Hi.
    denote SS.remove as Hr.
    rewrite SS.remove_spec in Hr.
    denote (_ = true) as Hs. apply Hs.
    intros Ha.
    apply Hr. intuition auto.
    denote selN as Hb.
    denote NoDup as Hd.
    eapply selN_NoDup_notin_removeN in Hd; try reflexivity.
    rewrite removeN_map_comm in *.
    erewrite selN_map in Hd by eauto.
    eapply in_map in Hi.
    rewrite <- Hb in *.
    eauto.
    autorewrite with lists; auto.
    unfold SS.For_all in *.
    intros.
    rewrite SS.remove_spec in *.
    intuition.
    rewrite <- removeN_map_comm.
    eapply in_removeN_neq; eauto.
    erewrite selN_map; eauto.
    rewrite Hfind.
    unfold smrep_single, SS.For_all.
    rewrite H.
    rewrite listpred_isolate with (i := off) by auto.
    cancel.
    rewrite SetFacts.empty_iff in *.
    intuition.
  Unshelve.
    all: easy.
  Qed.
  Proof.
    cbn. intros.
    unfold smrep_single_helper, smrep_single, SS.For_all.
    unfold put_dirty, remove_dirty, get_dirty.
    rewrite M.find_add_eq.
    rewrite H.
    destruct in_dec with (a := selN (INODE.IBlocks ino) off $0) (l := INODE.IBlocks ino').
    apply weq.
    - rewrite H in *.
      rewrite listpred_pick by eauto.
      do 2 intro; destruct_lifts.
      exfalso.
      eapply ptsto_conflict_F with (m := m) (a := #(selN (INODE.IBlocks ino) off $0)).
      pred_apply. cancel.
    - rewrite H in *.
      rewrite listpred_isolate with (l := INODE.IBlocks _) (i := off) by auto.
      rewrite listpred_pimpl_replace.
      norm. cancel.
      solve [apply sep_star_comm | apply pimpl_refl].
      intuition (rewrite ?SS.add_spec in *; auto).
      intuition subst.
      eauto using in_map, in_selN.
      eapply in_removeN.
      rewrite removeN_map_comm.
      intuition.
      cancel.
  Qed.
  Proof.
    intros.
    unfold put_dirty, remove_dirty, get_dirty, smrep_single_helper, smrep_single, SS.For_all.
    repeat rewrite M.find_add_eq.
    destruct (Map.find inum dblocks) eqn:?.
    repeat rewrite M.find_add_eq.
    cancel.
    apply listpred_pimpl_replace. cancel.
    rewrite SS.add_spec in *.
    rewrite SS.remove_spec in *.
    intuition.
    apply H0.
    rewrite SS.add_spec, SS.remove_spec in *.
    destruct (addr_eq_dec x bn); intuition.
    rewrite Heqo.
    cancel.
  Qed.
  Proof.
    intros.
    unfold smrep_single_helper, smrep_single.
    norml.
    cbv [stars fold_left pred_fold_left].
    rewrite listpred_exis_listmatch.
    norml.
    cbv [stars fold_left pred_fold_left].
    erewrite listmatch_lift with (P := fun x y => (~SS.In #x (get_dirty inum dblocks)) -> y = true).
    rewrite listmatch_length_pimpl.
    cancel.
    rewrite listmatch_map_r.
    rewrite listmatch_sym. apply pimpl_refl.
    denote Forall2 as Hf.
    eapply forall2_forall in Hf.
    rewrite Forall_forall in Hf.
    rewrite <- SS.mem_spec.
    destruct SS.mem eqn:Hm; auto.
    rewrite <- SetFacts.not_mem_iff in *.
    right.
    specialize (Hf (selN (INODE.IBlocks ino) i $0, selN b i false)).
    eapply Hf; auto.
    rewrite <- selN_combine by auto.
    apply in_selN.
    rewrite combine_length_eq; omega.
    unfold incl.
    denote SS.For_all as Hs.
    intros a.
    rewrite AddrSetFacts.elements_spec1.
    auto.
    split; cancel.
  Qed.
  Proof.
    unfold rep; intros.
    destruct_lift H.
    rewrite listmatch_length_pimpl in H; destruct_lift H.
    rewrite listmatch_extract with (i := inum) in H.
    2: substl (length flist); eapply block_belong_to_file_inum_ok; eauto.

    assert (inum < length ilist) by ( eapply block_belong_to_file_inum_ok; eauto ).
    assert (inum < length flist) by ( substl (length flist); eauto ).

    denote block_belong_to_file as Hx; assert (Hy := Hx).
    unfold block_belong_to_file in Hy; intuition.
    unfold file_match at 2 in H.
    rewrite listmatch_length_pimpl with (a := BFData _) in H; destruct_lift H.
    denote! (length _ = _) as Heq.
    rewrite listmatch_extract with (i := off) (a := BFData _) in H.
    2: rewrite Heq; rewrite map_length; eauto.

    erewrite selN_map in H; eauto.

    eapply pimpl_trans; [ apply pimpl_refl | | eapply list2nmem_updN; pred_apply ].
    2: eassign (natToWord addrlen 0).
    2: cancel.

    cancel.

    eapply pimpl_trans.
    2: eapply listmatch_isolate with (i := inum); eauto.
    2: rewrite length_updN; eauto.

    rewrite removeN_updN. cancel.
    unfold file_match; cancel.
    2: rewrite selN_updN_eq by ( substl (length flist); eauto ).
    2: simpl; eauto.

    eapply pimpl_trans.
    2: eapply listmatch_isolate with (i := off).
    2: rewrite selN_updN_eq by ( substl (length flist); eauto ).
    2: simpl.
    2: rewrite length_updN.
    2: rewrite Heq; rewrite map_length; eauto.
    2: rewrite map_length; eauto.

    rewrite selN_updN_eq; eauto; simpl.
    erewrite selN_map by eauto.
    rewrite removeN_updN.
    rewrite selN_updN_eq by ( rewrite Heq; rewrite map_length; eauto ).
    cancel.

    rewrite locked_eq in *; unfold cache_rep in *.
    pred_apply.
    rewrite map_updN.
    erewrite selN_eq_updN_eq by ( erewrite selN_map; eauto; reflexivity ).
    cancel.

  Grab Existential Variables.
    all: eauto.
    all: try exact BFILE.bfile0.
    all: try exact None.
  Qed.
  Proof.
    unfold rep, pick_balloc, block_is_unused; intros.
    destruct_lift H.
    destruct flag.
    - unfold BALLOCC.rep at 1 in H.
      unfold BALLOCC.Alloc.rep in H.
      unfold BALLOCC.Alloc.Alloc.rep in H.
      destruct_lift H.

      denote listpred as Hx.
      assert (Hy := Hx).
      rewrite listpred_nodup_piff in Hy; [ | apply addr_eq_dec | ].

      2: intros; assert (~ (y |->? * y |->?)%pred m') as Hc by apply ptsto_conflict.
      2: contradict Hc; pred_apply; cancel.

      assert (Hnodup := H). rewrite Hy in Hnodup; destruct_lift Hnodup.

      rewrite listpred_remove_piff in Hy; [ | | eauto | eauto ].

      2: intros; assert (~ (y |->? * y |->?)%pred m') as Hc by apply ptsto_conflict.
      2: contradict Hc; pred_apply; cancel.

      rewrite Hy in H.
      destruct_lift H.
      eapply pimpl_trans; [ apply pimpl_refl | | eapply list2nmem_updN; pred_apply; cancel ].
      unfold BALLOCC.rep at 2. unfold BALLOCC.Alloc.rep. unfold BALLOCC.Alloc.Alloc.rep.

      norm; unfold stars; simpl.
      2: intuition eauto.
      cancel. rewrite Hy. cancel.

    - unfold BALLOCC.rep at 2 in H.
      unfold BALLOCC.Alloc.rep in H.
      unfold BALLOCC.Alloc.Alloc.rep in H.
      destruct_lift H.

      denote listpred as Hx.
      assert (Hy := Hx).
      rewrite listpred_nodup_piff in Hy; [ | apply addr_eq_dec | ].

      2: intros; assert (~ (y |->? * y |->?)%pred m') as Hc by apply ptsto_conflict.
      2: contradict Hc; pred_apply; cancel.

      assert (Hnodup := H). rewrite Hy in Hnodup; destruct_lift Hnodup.

      rewrite listpred_remove_piff in Hy; [ | | eauto | eauto ].

      2: intros; assert (~ (y |->? * y |->?)%pred m') as Hc by apply ptsto_conflict.
      2: contradict Hc; pred_apply; cancel.

      rewrite Hy in H.
      destruct_lift H.
      eapply pimpl_trans; [ apply pimpl_refl | | eapply list2nmem_updN; pred_apply; cancel ].
      unfold BALLOCC.rep at 3. unfold BALLOCC.Alloc.rep. unfold BALLOCC.Alloc.Alloc.rep.

      norm; unfold stars; simpl.
      2: intuition eauto.
      cancel. rewrite Hy. cancel.

    Unshelve.
    all: apply addr_eq_dec.
  Qed.
  Proof.
    intros.
    apply block_belong_to_file_inum_ok in H0 as H0'.
    unfold block_belong_to_file, rep in *.
    setoid_rewrite listmatch_extract with (i := inum) in H.
    unfold file_match at 2 in H.
    setoid_rewrite listmatch_length_pimpl with (a := BFData _) in H.
    destruct_lift H.
    rewrite map_length in *.
    intuition.
    denote (length (BFData _)) as Hl.
    rewrite Hl; eauto.
    simplen.
  Unshelve.
    all: try exact bfile0.
  Qed.
  Proof.
    intros.
    destruct a; auto.
    rewrite Nat.mul_succ_l in H.
    assert (0 < a * valulen + valulen + b).
    apply Nat.add_pos_l.
    apply Nat.add_pos_r.
    rewrite valulen_is; apply Nat.ltb_lt; compute; reflexivity.
    omega.
  Qed.
  Proof.
    induction n; simpl; intros.
    unfold listmatch; cancel.
    rewrite IHn.
    unfold listmatch; cancel.
    unfold file_match, listmatch; cancel.
  Qed.
  Proof.
    intros.
    destruct (ge_dec inum (length ilist)).
    rewrite selN_oob by omega.
    constructor.
    rewrite listmatch_extract with (i := inum) in H.
    unfold file_match in H.
    rewrite listmatch_map_r in H.
    eapply listmatch_nodup.
    pred_apply' H.
    cancel.
    rewrite listmatch_map_l.
    rewrite listmatch_sym.
    cancel. apply pimpl_refl.
    erewrite listmatch_length_r by (pred_apply' H; apply pimpl_refl).
    omega.
  Unshelve.
    exact bfile0.
  Qed.
  Proof.
    intros.
    rewrite listmatch_isolate in H by eauto.
    unfold file_match in H; destruct_lifts.
    symmetry.
    eapply listmatch_length_r with (m := m).
    pred_apply.
    rewrite listmatch_map_r.
    solve [apply pimpl_refl | apply sep_star_comm].
  Qed.
  Proof.
    destruct n; intros; auto.
    cbv in H; congruence.
  Qed.
  Proof.
    firstorder.
  Qed.
  Proof.
    firstorder.
  Qed.
  Proof.
    intros; subst; auto.
  Qed.
  Proof.
    intros; subst; auto.
  Qed.
  Proof.
    intros.
    unfold cache_rep.
    rewrite locked_eq.
    generalize 0.
    generalize dependent flist.
    induction flist; cbn; intros.
    eapply BFM.mm_init.
    inversion H; subst.
    eapply pimpl_apply; [|apply IHflist; eauto].
    substl (BFCache a).
    cancel.
  Qed.
  Proof.
    intros.
    auto using bfcache_emp, Forall_repeat.
  Qed.
  Proof.
    intros.
    rewrite locked_eq in *.
    unfold cache_rep in *.
    rewrite map_updN; simpl.
    eapply list2nmem_sel in H0 as H0'; rewrite H0'.
    erewrite selN_eq_updN_eq; eauto.
    erewrite selN_map; eauto.
    simplen.
  Unshelve.
    exact None.
  Qed.
  Proof.
    induction l; intros; eauto.
    simpl in H.
    eapply sep_star_none; intros; [ | | exact H ].
    destruct a; simpl in *.
    eapply ptsto_none; [ | eauto ]; omega.
    eauto.
    eapply IHl; eauto.
  Qed.
  Proof.
    induction l; intros; eauto.
    simpl in H.
    eapply sep_star_none; eauto; intros.
    destruct a; simpl in *.
    eapply ptsto_none; [ | eauto ].
    destruct idx; try omega; try congruence.
    eauto.
    destruct idx.
    eapply cache_ptsto_none''; eauto; omega.
    replace (start + S idx) with (S start + idx) by omega.
    eapply IHl; eauto.
    simpl in *; omega.
  Qed.
  Proof.
    intros.
    replace (idx) with (0 + idx) by omega.
    eapply cache_ptsto_none'; eauto.
  Qed.
  Proof.
    intros.
    assert (BFM.mm _ c idx = None).
    eapply cache_ptsto_none; eauto.
    eauto.
  Qed.
  Proof.
    intros.
    rewrite locked_eq in *.
    unfold cache_rep in *.
    eapply list2nmem_sel in H0 as H0'.
    case_eq (BFCache f); intros.
    - eapply arrayN_isolate with (i := inum) in H; [ | simplen ].
      unfold cache_ptsto at 2 in H. simpl in H.
      erewrite selN_map in H by simplen. rewrite <- H0' in H. rewrite H1 in H.
      eapply BFM.mm_find; pred_apply; cancel.
    - eapply cache_ptsto_none_find; eauto.
      simplen.
      erewrite selN_map by simplen.
      rewrite <- H0'.
      eauto.
  Unshelve.
    all: exact None.
  Qed.
  Proof.
    intros.
    rewrite locked_eq in *.
    unfold cache_rep in *.
    eapply list2nmem_sel in H0 as H0'.
    case_eq (BFCache f); intros.
    - eapply pimpl_apply.
      2: eapply BFM.mm_replace.
      rewrite arrayN_isolate with (i := inum) by simplen.
      unfold cache_ptsto at 2; simpl.
      erewrite selN_map by simplen. rewrite selN_updN_eq by simplen. cancel.
      rewrite map_updN. rewrite firstn_updN_oob by omega.
      rewrite skipn_updN by omega.
      pred_apply.
      rewrite arrayN_isolate with (i := inum) by simplen.
      unfold cache_ptsto at 2.
      erewrite selN_map by simplen. rewrite <- H0'. rewrite H1. cancel.
    - eapply pimpl_apply.
      2: eapply BFM.mm_add; eauto.
      rewrite arrayN_isolate with (i := inum) by simplen.
      rewrite arrayN_isolate with (i := inum) (vs := map _ _) by simplen.
      rewrite map_updN. rewrite firstn_updN_oob by omega.
      simpl; rewrite skipn_updN by omega.
      cancel.
      unfold cache_ptsto.
      erewrite selN_map by simplen. rewrite H1.
      rewrite selN_updN_eq by simplen.
      cancel.
      eapply cache_ptsto_none_find; eauto.
      simplen.
      erewrite selN_map by simplen.
      rewrite <- H0'; eauto.
  Unshelve.
    all: try exact None.
    all: eauto.
  Qed.
  Proof.
    intros.
    rewrite locked_eq in *.
    unfold cache_rep in *.
    eapply list2nmem_sel in H0 as H0'.
    case_eq (BFCache f); intros.
    - eapply pimpl_apply.
      2: eapply BFM.mm_remove.
      rewrite arrayN_isolate with (i := inum) by simplen.
      unfold cache_ptsto at 2; simpl.
      erewrite selN_map by simplen. rewrite selN_updN_eq by simplen. cancel.
      rewrite map_updN. rewrite firstn_updN_oob by omega.
      rewrite skipn_updN by omega.
      pred_apply.
      rewrite arrayN_isolate with (i := inum) by simplen.
      unfold cache_ptsto at 2.
      erewrite selN_map by simplen. rewrite <- H0'. rewrite H1. cancel.
      cancel.
    - eapply pimpl_apply.
      2: eapply BFM.mm_remove_none; eauto.
      rewrite arrayN_isolate with (i := inum) by simplen.
      rewrite arrayN_isolate with (i := inum) (vs := map _ _) by simplen.
      rewrite map_updN. rewrite firstn_updN_oob by omega.
      simpl; rewrite skipn_updN by omega.
      cancel.
      unfold cache_ptsto.
      erewrite selN_map by simplen. rewrite H1.
      rewrite selN_updN_eq by simplen.
      cancel.
      eapply cache_ptsto_none_find; eauto.
      simplen.
      erewrite selN_map by simplen.
      rewrite <- H0'; eauto.
  Unshelve.
    all: try exact None.
    all: eauto.
  Qed.
  Proof.
    intros.
    eapply bfcache_remove' in H; eauto.
  Qed.
  Proof.
    unfold rep; intros.
    norml. unfold stars; cbn.
    rewrite listmatch_length_pimpl.
    cancel.
    seprewrite.
    erewrite <- updN_selN_eq with (l := ilist) (ix := inum) at 2.
    rewrite listmatch_length_pimpl; cancel.
    eapply listmatch_updN_selN; try simplen.
    unfold file_match; cancel.
    eapply bfcache_remove'.
    eauto.
    sepauto.
  Unshelve.
    all: eauto using INODE.inode0.
  Qed.
  Proof.
    unfold shuffle_allocs.
    intros.
    eapply pimpl_ok2.
    ProgMonad.monad_simpl.
    eapply forN_ok'.
    cancel.
    step.
    unfold BALLOCC.bn_valid; split; auto. omega.
    denote (lt m1) as Hm.
    rewrite Nat.sub_add in Hm by omega.
    apply Rounding.lt_div_mul_lt in Hm; omega.
    denote In as Hb.
    eapply Hb.
    unfold BALLOCC.bn_valid; split; auto.
    denote (lt m1) as Hm.
    rewrite Nat.sub_add in Hm by omega.
    apply Rounding.lt_div_mul_lt in Hm; omega.
    step.
    unfold BALLOCC.bn_valid; split; auto. omega.
    substl (BmapNBlocks bxps_2); auto.
    denote (lt m1) as Hm.
    rewrite Nat.sub_add in Hm by omega.
    apply Rounding.lt_div_mul_lt in Hm; omega.
    step.
    apply remove_other_In.
    omega.
    intuition.
    step.
    cancel.
    eapply LOG.intact_hashmap_subset.
    eauto.
    Unshelve. exact tt.
  Qed.
  Proof.
    unfold init, rep, smrep.

    (* BALLOC.init_nofree *)
    prestep. norm. cancel.
    intuition simpl. pred_apply.

    (* now we need to split the LHS several times to get the correct layout *)
    erewrite arrayN_split at 1; repeat rewrite Nat.add_0_l.
    (* data alloc2 is the last chunk *)
    apply sep_star_assoc.
    eauto.
    omega. omega.
    rewrite skipn_length; omega.

    (* BALLOC.init *)
    prestep. norm. cancel.
    intuition simpl. pred_apply.
    erewrite arrayN_split at 1; repeat rewrite Nat.add_0_l.
    erewrite arrayN_split with (i := (BmapNBlocks bxps_1) * valulen) at 1; repeat rewrite Nat.add_0_l.
    (* data region is the first chunk, and data alloc1 is the last chunk *)
    eassign(BmapStart bxps_1); cancel.
    pred_apply.
    erewrite arrayN_split with (i := BmapStart bxps_2). repeat rewrite Nat.add_0_l.
    erewrite arrayN_split with (i := BmapStart bxps_1) (a := firstn _ _). repeat rewrite Nat.add_0_l.
    erewrite arrayN_split with (i := (BmapNBlocks bxps_1) * valulen) at 1; repeat rewrite Nat.add_0_l.
    rewrite arrayN_listpred_seq by eauto.
    repeat rewrite firstn_length.
    substl (length sl).
    cancel.
    omega.
    rewrite skipn_length.
    rewrite firstn_length_l; omega.
    repeat rewrite firstn_firstn.
    repeat rewrite Nat.min_l; try omega.
    rewrite firstn_length_l; omega.

    (* IAlloc.init *)
    prestep. norm. cancel.
    intuition simpl. pred_apply.
    erewrite arrayN_split at 1.
    (* inode region is the first chunk, and inode alloc is the second chunk *)
    substl (IAlloc.Sig.BMPStart ibxp).
    eassign (IAlloc.Sig.BMPLen ibxp * valulen / INODE.IRecSig.items_per_val).
    cancel.

    denote (IAlloc.Sig.BMPStart) as Hx; contradict Hx.
    substl (IAlloc.Sig.BMPStart ibxp); intro.
    eapply add_nonzero_exfalso_helper2; eauto.
    rewrite skipn_skipn, firstn_firstn.
    rewrite Nat.min_l, skipn_length by omega.
    rewrite firstn_length_l by omega.
    omega.

    (* Inode.init *)
    prestep. norm. cancel.
    intuition simpl. pred_apply.
    substl (IXStart ixp); cancel.
    denote BALLOCC.smrep as Hs. exact Hs.

    rewrite firstn_firstn, firstn_length, skipn_length, firstn_length.
    repeat rewrite Nat.min_l with (n := (BmapStart bxps_1)) by omega.
    rewrite Nat.min_l; omega.
    denote (IXStart ixp) as Hx; contradict Hx.
    substl (IXStart ixp); intro.
    eapply add_nonzero_exfalso_helper2 with (b := 0).
    rewrite Nat.add_0_r; eauto.
    auto.

    (* shuffle_allocs *)
    step.

    (* post condition *)
    prestep; unfold IAlloc.rep; cancel.
    apply file_match_init_ok.
    rewrite <- smrep_init. cancel.

    substl (IXLen ixp).
    apply Rounding.div_lt_mul_lt; auto.
    rewrite Nat.div_small.
    apply Nat.div_str_pos; split.
    apply INODE.IRec.Defs.items_per_val_gt_0.
    rewrite Nat.mul_comm.
    apply Rounding.div_le_mul; try omega.
    cbv; omega.
    unfold INODE.IRecSig.items_per_val.
    rewrite valulen_is.
    vm_compute; omega.

    denote (_ =p=> freepred0) as Hx; apply Hx.
    substl (length dl); substl (IXLen ixp).
    apply Rounding.mul_div; auto.
    apply Nat.mod_divide; auto.
    apply Nat.divide_mul_r.
    unfold INODE.IRecSig.items_per_val.
    apply Nat.mod_divide; auto.
    rewrite valulen_is.
    vm_compute; auto.

    all: auto; cancel.
    Unshelve. eauto.
  Qed.
  Proof.
    unfold getlen, rep.
    safestep.
    sepauto.

    safestep.
    extract; seprewrite; subst.
    denote (_ (list2nmem m)) as Hx.
    setoid_rewrite listmatch_length_pimpl in Hx at 2.
    destruct_lift Hx; eauto.
    simplen.

    cancel.
    eauto.
    Unshelve. all: eauto.
  Qed.
  Proof.
    unfold getattrs, rep.
    safestep.
    sepauto.

    safestep.
    extract; seprewrite.
    subst; eauto.

    cancel.
    eauto.
  Qed.
  Proof.
    unfold treeseq_ilist_safe; intuition.
  Qed.
  Proof.
    unfold treeseq_ilist_safe; intuition.
    erewrite H2 by eauto.
    erewrite H3 by eauto.
    eauto.
  Qed.
  Proof.
    unfold setattrs, rep.
    safestep.
    sepauto.
    safestep.
    repeat extract. seprewrite.
    5: reflexivity.
    4: sepauto.
    2: eauto.
    eapply listmatch_updN_selN; try omega.
    unfold file_match; cancel.
    seprewrite.
    rewrite <- smrep_upd_keep_blocks.
    cancel.
    reflexivity.

    denote (list2nmem m') as Hm'.
    rewrite listmatch_length_pimpl in Hm'; destruct_lift Hm'.
    denote (list2nmem ilist') as Hilist'.
    assert (inum < length ilist) by simplen'.
    apply arrayN_except_upd in Hilist'; eauto.
    apply list2nmem_array_eq in Hilist'; subst.
    unfold ilist_safe; intuition. left.
    destruct (addr_eq_dec inum inum0); subst.
    - unfold block_belong_to_file in *; intuition.
      all: erewrite selN_updN_eq in * by eauto; simpl; eauto.
    - unfold block_belong_to_file in *; intuition.
      all: erewrite selN_updN_ne in * by eauto; simpl; eauto.
    - unfold treeseq_ilist_safe.
      split.
      intros.
      seprewrite.
      unfold block_belong_to_file in *.
      intuition simplen.

      intuition.
      assert (inum < length ilist) by simplen'.
      denote arrayN_ex as Ha.
      apply arrayN_except_upd in Ha; auto.
      apply list2nmem_array_eq in Ha; subst.
      rewrite selN_updN_ne; auto.
  Qed.
  Proof.
    unfold updattr, rep.
    step.
    sepauto.

    safestep.
    repeat extract. seprewrite.
    5: reflexivity.
    4: sepauto.
    2: eauto.
    eapply listmatch_updN_selN; try omega.
    unfold file_match; cancel.
    seprewrite.
    rewrite <- smrep_upd_keep_blocks.
    cancel.
    reflexivity.

    denote (list2nmem m') as Hm'.
    rewrite listmatch_length_pimpl in Hm'; destruct_lift Hm'.
    denote (list2nmem ilist') as Hilist'.
    assert (inum < length ilist) by simplen'.
    apply arrayN_except_upd in Hilist'; eauto.
    apply list2nmem_array_eq in Hilist'; subst.
    unfold ilist_safe; intuition. left.
    destruct (addr_eq_dec inum inum0); subst.
    - unfold block_belong_to_file in *; intuition.
      all: erewrite selN_updN_eq in * by eauto; simpl; eauto.
    - unfold block_belong_to_file in *; intuition.
      all: erewrite selN_updN_ne in * by eauto; simpl; eauto.
  Unshelve.
    all: eauto.
  Qed.
  Proof.
    unfold read, rep.
    prestep; norml.
    extract; seprewrite; subst.
    denote (_ (list2nmem m)) as Hx.
    setoid_rewrite listmatch_length_pimpl in Hx at 2.
    rewrite map_length in *.
    destruct_lift Hx.
    safecancel.
    match goal with H: _ = length (INODE.IBlocks _) |- _ => rewrite <-H end.
    now eauto.

    sepauto.
    denote (_ (list2nmem m)) as Hx.
    setoid_rewrite listmatch_extract with (i := off) in Hx at 2; try omega.
    destruct_lift Hx; filldef.
    safestep.
    rewrite listmatch_extract with (i := off) (b := map _ _) by omega.
    erewrite selN_map by omega; filldef.
    rewrite <- surjective_pairing.
    cancel.
    step.
    rewrite listmatch_isolate with (a := flist) (i := inum) by omega.
    unfold file_match. cancel.
    cancel; eauto.
    cancel; eauto.
    Unshelve. all: eauto.
  Qed.
  Proof.
    unfold write, rep.
    prestep; norml.
    extract; seprewrite; subst.
    denote (_ (list2nmem m)) as Hx.
    setoid_rewrite listmatch_length_pimpl in Hx at 2.
    rewrite map_length in *.
    destruct_lift Hx; safecancel.
    match goal with H: _ = length _ |- _ => rewrite <-H end.
    now eauto.
    sepauto.

    denote (_ (list2nmem m)) as Hx.
    setoid_rewrite listmatch_extract with (i := off) in Hx at 2; try omega.
    destruct_lift Hx; filldef.
    step.

    setoid_rewrite INODE.inode_rep_bn_nonzero_pimpl in H.
    destruct_lift H; denote (_ <> 0) as Hx; subst.
    eapply Hx; try eassumption; omega.
    rewrite listmatch_extract with (b := map _ _) (i := off) by omega.
    erewrite selN_map by omega; filldef.
    rewrite <- surjective_pairing.
    cancel.
    prestep. norm. cancel.
    intuition cbn.
    2: sepauto.
    2: cbn; sepauto.
    pred_apply. cancel.
    rewrite listmatch_isolate with (a := updN _ _ _).
    rewrite removeN_updN, selN_updN_eq by simplen.
    unfold file_match.
    cancel; eauto.
    rewrite listmatch_isolate with (a := updN _ _ _).
    rewrite removeN_updN, selN_updN_eq by simplen.
    erewrite selN_map by simplen.
    cancel.

    simplen.
    simplen.
    simplen.
    simplen.

    eauto.
    eauto.

    pimpl_crash; cancel; auto.
  Grab Existential Variables.
    all: try exact unit.
    all: intros; eauto.
    all: try solve [exact bfile0 | exact INODE.inode0].
    all: try split; auto using nil, tt.
  Qed.
  Proof.
    intros.
    unfold treeseq_ilist_safe, block_belong_to_file.
    apply arrayN_except_upd in H0 as Hselupd; auto.
    apply list2nmem_array_eq in Hselupd; subst.
    split.
    intros.
    split.
    erewrite selN_updN_eq; simpl.
    erewrite app_length.
    omega.
    simplen'.
    intuition.
    erewrite selN_updN_eq; simpl.
    erewrite selN_app; eauto.
    simplen'.
    intros.
    erewrite selN_updN_ne; eauto.
  Qed.
  Proof.
    unfold grow.
    prestep; norml; unfold stars; simpl.
    denote rep as Hr.
    rewrite rep_alt_equiv with (msalloc := MSAlloc ms) in Hr.
    unfold rep_alt, smrep in Hr; destruct_lift Hr.
    extract. seprewrite; subst.
    denote removeN as Hx.
    setoid_rewrite listmatch_length_pimpl in Hx at 2.
    rewrite map_length in *.
    destruct_lift Hx. safecancel.
    sepauto.

    step.

    (* file size ok, do allocation *)
    {
      step.
      safestep.
      sepauto.
      step.

      eapply BALLOCC.bn_valid_facts; eauto.
      step.

      or_r; safecancel.

      rewrite rep_alt_equiv with (msalloc := MSAlloc ms); unfold rep_alt.
      erewrite pick_upd_balloc_lift with (new := freelist') (flag := MSAlloc ms) (p := (frees_1, frees_2)) at 1.
      rewrite pick_negb_upd_balloc with (new := freelist') (flag := MSAlloc ms) at 1.
      unfold upd_balloc.

      match goal with a : BALLOCC.Alloc.memstate |- _ =>
        progress replace a with (BALLOCC.mk_memstate (BALLOCC.MSLog a) (BALLOCC.MSCache a)) at 1 by (destruct a; reflexivity);
        setoid_rewrite pick_upd_balloc_lift with (new := (BALLOCC.MSCache a) ) (flag := MSAlloc ms) at 1;
        rewrite pick_negb_upd_balloc with (new := (BALLOCC.MSCache a)) (flag := MSAlloc ms) at 1
      end.
      unfold upd_balloc.

      cancel.

      4: sepauto.
      5: eauto.
      seprewrite.
      rewrite listmatch_updN_removeN by simplen.
      unfold file_match; cancel.
      rewrite map_app; simpl.
      rewrite <- listmatch_app_tail.
      cancel.

      rewrite map_length; omega.
      rewrite wordToNat_natToWord_idempotent'; auto.
      eapply BALLOCC.bn_valid_goodSize; eauto.
      seprewrite.
      eapply bfcache_upd; eauto.
      rewrite <- smrep_upd_add; eauto.
      cancel.
      unfold smrep. destruct MSAlloc; cancel.
      eapply BALLOCC.bn_valid_goodSize; eauto. omega.
      sepauto.
      cbn; auto.
      apply list2nmem_app; eauto.

      2: { eapply grow_treeseq_ilist_safe. omega. eauto. }
      2: cancel.
      2: or_l; cancel.

      denote (list2nmem ilist') as Hilist'.
      assert (inum < length ilist) by simplen'.
      apply arrayN_except_upd in Hilist'; eauto.
      apply list2nmem_array_eq in Hilist'; subst.
      unfold ilist_safe; intuition.

      destruct (MSAlloc ms); simpl in *; eapply incl_tran; eauto; eapply incl_remove.

      destruct (addr_eq_dec inum inum0); subst.
      + unfold block_belong_to_file in *; intuition.
        all: erewrite selN_updN_eq in * by eauto; simpl in *; eauto.
        destruct (addr_eq_dec off (length (INODE.IBlocks (selN ilist inum0 INODE.inode0)))).
        * right.
          rewrite selN_last in * by auto.
          subst. rewrite wordToNat_natToWord_idempotent'. eauto.
          eapply BALLOCC.bn_valid_goodSize; eauto.
        * left.
          rewrite app_length in *; simpl in *.
          split. omega.
          subst. rewrite selN_app1 by omega. auto.
      + unfold block_belong_to_file in *; intuition.
        all: erewrite selN_updN_ne in * by eauto; simpl; eauto.
    }

    step.
    cancel; eauto.

    Unshelve. all: easy.
  Qed.
  Proof.
    unfold shrink.
    prestep; norml; unfold stars; simpl.
    denote rep as Hr.
    rewrite rep_alt_equiv with (msalloc := MSAlloc ms) in Hr.
    unfold rep_alt, smrep in Hr; destruct_lift Hr.
    cancel.
    sepauto.
    extract; seprewrite; subst; denote removeN as Hx.
    setoid_rewrite listmatch_length_pimpl in Hx at 2.
    rewrite map_length in *.

    {
      step.
      erewrite INODE.rep_bxp_switch in Hx by eassumption.
      rewrite INODE.inode_rep_bn_valid_piff in Hx; destruct_lift Hx.
      denote Forall as Hv; specialize (Hv inum); subst.
      rewrite <- Forall_map.
      apply forall_skipn; apply Hv; eauto. omega.
      erewrite <- listmatch_ptsto_listpred.
      rewrite listmatch_extract with (i := inum) (a := flist) by omega.
      unfold file_match at 2.
      setoid_rewrite listmatch_split at 2.
      rewrite skipn_map_comm; cancel.
      rewrite arrayN_except with (i := inum) by omega.
      rewrite smrep_single_helper_split_tail. cancel.
      instantiate (1 := INODE.mk_inode _ _). cbn; eauto.
      eapply file_match_no_dup.
      pred_apply' H. cancel.

      destruct_lift Hx; denote (length (BFData _)) as Heq.
      prestep.
      norm.
      cancel.
      intuition.

      pred_apply.
      erewrite INODE.rep_bxp_switch by eassumption. cancel.
      sepauto.
      pred_apply. cancel.

      denote listmatch as Hx.
      setoid_rewrite listmatch_length_pimpl in Hx at 2.
      prestep; norm. cancel. eassign (ilist'). intuition simpl.
      2: sepauto.

      rewrite rep_alt_equiv with (msalloc := MSAlloc ms); unfold rep_alt.
      pred_apply.
      erewrite pick_upd_balloc_lift with (new := freelist') (flag := negb (MSAlloc ms)) (p := (frees_1, frees_2)) at 1.
      rewrite pick_upd_balloc_negb with (new := freelist') (flag := MSAlloc ms) at 1.
      unfold upd_balloc.

      match goal with a : BALLOCC.Alloc.memstate |- _ =>
        progress replace a with (BALLOCC.mk_memstate (BALLOCC.MSLog a) (BALLOCC.MSCache a)) at 1 by (destruct a; reflexivity);
        setoid_rewrite pick_upd_balloc_lift with (new := (BALLOCC.MSCache a) ) (flag := negb (MSAlloc ms)) at 1;
        rewrite pick_upd_balloc_negb with (new := (BALLOCC.MSCache a)) (flag := MSAlloc ms) at 1
      end.
      unfold upd_balloc.

      erewrite INODE.rep_bxp_switch by ( apply eq_sym; eassumption ).
      cancel.

      seprewrite.
      rewrite listmatch_updN_removeN by omega.
      rewrite Heq.
      unfold file_match, cuttail; cancel; eauto.
      seprewrite.
      unfold cuttail.
      rewrite firstn_map_comm.
      cancel.
      eapply bfcache_upd; eauto.
      unfold smrep.
      seprewrite.
      rewrite arrayN_except_upd.
      rewrite arrayN_ex_smrep_single_helper_remove_dirty_vec.
      cancel.
      destruct MSAlloc; cancel.
      omega.
      3: eauto.

      denote (list2nmem ilist') as Hilist'.
      assert (inum < length ilist) by simplen.
      apply arrayN_except_upd in Hilist'; eauto.
      apply list2nmem_array_eq in Hilist'; subst.
      unfold ilist_safe; intuition.
      destruct (MSAlloc ms); simpl in *; eapply incl_refl.
      left.
      destruct (addr_eq_dec inum inum0); subst.
      + unfold block_belong_to_file in *; intuition simpl.
        all: erewrite selN_updN_eq in * by eauto; simpl in *; eauto.
        rewrite cuttail_length in *. omega.
        rewrite selN_cuttail in *; auto.
      + unfold block_belong_to_file in *; intuition simpl.
        all: erewrite selN_updN_ne in * by eauto; simpl; eauto.
      + erewrite list2nmem_array_updN with (nl := ilist') (i := inum).
        erewrite selN_updN_ne; eauto.
        pred_apply; cancel.
        omega.
      + pimpl_crash.
        cancel.
    }

    pimpl_crash; cancel; eauto.

  Unshelve.
    all : try easy.
    all : solve [ exact bfile0 | intros; exact emp | exact nil].
  Qed.
  Proof.
    unfold sync, rep.
    step.
    step.
  Qed.
  Proof.
    unfold sync_noop, rep.
    step.
    step.
  Qed.
  Proof.
    unfold block_belong_to_file; intros; split; auto.
    unfold rep, INODE.rep in H; destruct_lift H.
    rewrite listmatch_extract with (i := inum) in H.
    unfold file_match in H; destruct_lift H.
    setoid_rewrite listmatch_extract with (i := inum) (b := ilist) in H.
    destruct_lift H.
    erewrite listmatch_length_pimpl with (a := BFData _) in H.
    destruct_lift H.
    rewrite map_length in *.
    simplen.
    simplen.
    rewrite combine_length_eq by omega.
    erewrite listmatch_length_pimpl with (b := ilist) in *.
    destruct_lift H. simplen.
    Unshelve. split; eauto. exact INODE.inode0.
  Qed.
  Proof.
    intros.
    eapply list2nmem_inbound in H1.
    eapply block_belong_to_file_off_ok; eauto.
  Qed.
  Proof.
    intros.
    inversion H0; subst; eauto.
    inversion H; simpl in *; intuition; subst.
    apply latest_in_ds.
  Qed.
  Proof.
    unfold dwrite.
    prestep; norml.
    denote  (list2nmem ds !!) as Hz.
    eapply block_belong_to_file_ok in Hz as Hb; eauto.
    unfold rep, smrep in *; destruct_lift Hz.
    assert (NoDup (map (wordToNat (sz:=addrlen)) (INODE.IBlocks (selN ilist inum INODE.inode0)))).
    eapply file_match_no_dup. pred_apply' H. cancel.
    extract; seprewrite; subst.
    denote removeN as Hx.
    setoid_rewrite listmatch_length_pimpl in Hx at 2.
    rewrite map_length in *.
    destruct_lift Hx; cancel; eauto.
    match goal with H: length _ = length _ |- _ => rewrite <-H end. now eauto.

    sepauto.
    denote removeN as Hx.
    setoid_rewrite listmatch_extract with (i := off) (bd := 0) in Hx; try omega.
    destruct_lift Hx.
    rewrite arrayN_except with (i := inum) in * by omega.
    erewrite smrep_single_helper_split_dirty with (off := off) (ino' := INODE.mk_inode _ _) in *.
    2: now eauto.
    2: { match goal with H1: length _ = length (INODE.IBlocks _), H2: _ < length (BFData _) |- _ =>
                           rewrite H1 in H2 end. eauto. }
    2: now eauto.
    step.
    rewrite listmatch_extract with (i := off) (b := map _ _) by omega.
    erewrite selN_map by omega; filldef.
    rewrite <- surjective_pairing. cancel.

    prestep. norm. cancel.
    intuition simpl.
    2: sepauto. 2: sepauto.
    pred_apply; cancel.
    setoid_rewrite <- updN_selN_eq with (l := ilist) (ix := inum) at 4.
    rewrite listmatch_updN_removeN by omega.
    unfold file_match at 3; cancel; eauto.
    setoid_rewrite <- updN_selN_eq with (l := INODE.IBlocks _) (ix := off) at 3.
    erewrite map_updN by omega; filldef.
    rewrite listmatch_updN_removeN by omega.
    cancel.
    eauto.

    erewrite arrayN_except by (substl (length ilist); eauto).
    rewrite arrayN_ex_smrep_single_helper_put_dirty.
    eapply pimpl_trans.
    eapply pimpl_trans.
    2: eapply pimpl_sep_star; [reflexivity | eapply smrep_single_helper_return_dirty].
    cancel; solve [apply pimpl_refl | apply sep_star_comm].
    auto.
    sepauto.
    rewrite smrep_single_helper_put_remove_dirty. cancel.
    eauto.

    repeat xcrash_rewrite.
    xform_norm; xform_normr.
    cancel.

    or_r; cancel.
    xform_norm; cancel.

    cancel.
    xcrash.
    or_l; rewrite LOG.active_intact, LOG.intact_any; auto.

    Unshelve.
      all: try easy.
      exact INODE.iattr0.
  Qed.
  Proof.
    unfold datasync, synced_file, rep.
    (* use the spec that "syncs" additional blocks not given as arguments *)
    intros.
    ProgMonad.monad_simpl.
    eapply pimpl_ok2.
    apply LOG.dsync_vecs_additional_ok.
    unfold smrep. intros. norml.
    rewrite arrayN_except with (i := inum) in *|- by sepauto.
    denote arrayN_ex as Ha.
    pose proof Ha as Ha'.
    rewrite <- locked_eq with (x := _ sm) in Ha'.
    rewrite smrep_single_helper_to_listmatch in *.
    destruct_lifts.
    extract.
    safecancel.
    cancel; solve [apply pimpl_refl].
    cancel.
    rewrite map_length in *.
    erewrite selN_map by auto.
    rewrite AddrSetFacts.elements_spec1.
    denote SS.In as Hs. eapply Hs; auto.
    auto.
    apply AddrSetFacts.nodup_elements.

    prestep. norm. cancel.
    intuition auto.
    2: sepauto.
    pred_apply. cancel.
    seprewrite.
    rewrite listmatch_isolate with (b := ilist) by sepauto.
    rewrite removeN_updN, selN_updN_eq by sepauto.
    rewrite synced_list_map_fst_map.
    unfold file_match. cancel.
    rewrite listmatch_map_l.
    cancel.
    auto.
    eauto using bfcache_upd.
    rewrite arrayN_except with (vs := ilist) by sepauto.
    rewrite arrayN_ex_smrep_single_helper_clear_dirty.
    cancel.
    unfold smrep_single_helper, clear_dirty, smrep_single.
    rewrite M.find_remove_eq.
    cancel.
    rewrite listpred_map.
    rewrite listpred_pimpl_replace.
    cancel; solve [apply pimpl_refl | apply sep_star_comm].
    cancel.
    unfold SS.For_all.
    setoid_rewrite SetFacts.empty_iff.
    intuition.
    seprewrite.
    symmetry.
    eapply listmatch_length_r with (m := list2nmem ds !!).
    pred_apply; cancel.

    erewrite selN_map by simplen.
    eapply block_belong_to_file_ok with (m := list2nmem ds!!); eauto.
    eassign (bxp_1, bxp_2); pred_apply; unfold rep. cancel; eauto.
    repeat erewrite fst_pair by eauto.
    cancel.
    rewrite listmatch_isolate with (a := flist) by sepauto.
    unfold file_match.
    cancel.
    rewrite locked_eq in Ha'.
    pred_apply' Ha'.
    unfold smrep.
    rewrite arrayN_except by sepauto.
    solve [do 2 cancel].
    seprewrite.
    apply list2nmem_ptsto_cancel.
    erewrite listmatch_length_l with (m := list2nmem ds !!); eauto.
    pred_apply; cancel.
  Unshelve.
    all: solve [eauto | exact BFILE.bfile0 | exact ($0, nil)].
  Qed.
  Proof.
    unfold read_array.
    hoare.

    denote (arrayN _ a vsl) as Hx.
    destruct (list2nmem_arrayN_bound vsl _ Hx); subst; simpl in *; omega.
    rewrite isolateN_fwd with (i:=i) by auto.
    cancel.
  Unshelve.
    eauto.
    intros; exact emp.
  Qed.
  Proof.
    unfold write_array.
    prestep. cancel.
    denote (arrayN _ a vsl) as Hx.
    destruct (list2nmem_arrayN_bound vsl _ Hx); subst; simpl in *; try omega.
    rewrite isolateN_fwd with (i:=i) by auto; filldef; cancel.

    step.
    rewrite <- isolateN_bwd_upd by auto; cancel.
  Unshelve.
    eauto.
    intros; exact emp.
  Qed.
  Proof.
    unfold read_range.
    safestep. eauto. eauto.
    safestep.

    assert (m1 < length vsl).
    denote (arrayN _ a vsl) as Hx.
    destruct (list2nmem_arrayN_bound vsl _ Hx); subst; simpl in *; omega.
    safestep.

    rewrite firstn_S_selN_expand with (def := $0) by (rewrite map_length; auto).
    rewrite fold_left_app; simpl.
    erewrite selN_map; subst; auto.
    cancel.

    safestep.
    cancel.
    erewrite <- LOG.rep_hashmap_subset; eauto.
  Unshelve.
    all: eauto; try exact tt; intros; try exact emp.
  Qed.
  Proof.
    unfold read_cond.
    prestep. cancel.
    safestep. eauto. eauto.

    msalloc_eq.
    step.
    step.
    step.

    eapply list2nmem_array_pick; eauto.
    step.
    step.
    step.

    rewrite firstn_S_selN_expand with (def := $0) by (rewrite map_length; auto).
    rewrite fold_left_app; simpl.
    erewrite selN_map; subst; auto.
    apply not_true_is_false; auto.

    destruct a2.
    step.
    step.
    or_r; cancel.
    denote cond as Hx; rewrite firstn_oob in Hx; auto.
    rewrite map_length; auto.
    cancel.

  Unshelve.
    all: try easy.
    try exact ($0, nil).
  Qed.
  Proof.
    unfold grown; intros.
    safestep.
    unfold synced_list; simpl; rewrite app_nil_r.
    eassign f; destruct f.
    eassign F_; cancel. or_r; cancel. eapply treeseq_ilist_safe_refl.
    eauto. eauto.

    safestep.
    apply list2nmem_arrayN_app; eauto.
    safestep.
    cancel.
    or_r; cancel.
    erewrite firstn_S_selN_expand by omega.
    rewrite synced_list_app, <- app_assoc.
    unfold synced_list at 3; simpl; eauto.
    msalloc_eq.
    eapply ilist_safe_trans; eauto.
    eapply treeseq_ilist_safe_trans; eauto.

    cancel.
    cancel.

    safestep.
    cancel.
    or_r; cancel.
    rewrite firstn_oob; auto.
    apply list2nmem_arrayN_app; auto.
    rewrite firstn_oob; auto.

    cancel.
    Unshelve. all: easy.
  Qed.
  Proof.
    unfold truncate; intros.
    step.
    step.

    - safestep.
      msalloc_eq; cancel.
      eauto.
      step.
      or_r; safecancel.
      rewrite setlen_inbound, Rounding.sub_sub_assoc by omega; auto.
      exfalso; omega.
      cancel.

    - safestep.
      msalloc_eq; cancel.
      eauto.
      apply list2nmem_array.
      step.

      or_r; safecancel.
      rewrite setlen_oob by omega.
      unfold synced_list.
      rewrite repeat_length, combine_repeat; auto.
      cancel.
  Qed.
  Proof.
    unfold reset; intros.
    step.
    prestep. norml.
    rewrite rep_alt_equiv with (msalloc := MSAlloc ms) in *.
    match goal with H: context [rep_alt] |- _ =>
      unfold rep_alt, smrep in H; destruct_lift H end.
    cancel; msalloc_eq.
    sepauto.

    rewrite INODE.rep_bxp_switch in *|- by eassumption.
    step.
    rewrite <- Forall_map.
    match goal with H: context [INODE.rep] |- context [pick_balloc ?a ?b] =>
      rewrite INODE.inode_rep_bn_valid_piff with (bxp := pick_balloc a b) in H; destruct_lift H
    end.
    intuition sepauto.
    rewrite listmatch_isolate by sepauto.
    unfold file_match at 2.
    erewrite <- listmatch_ptsto_listpred.
    cancel.
    rewrite arrayN_except by sepauto.
    rewrite smrep_single_helper_clear_dirty.
    cancel.

    prestep; norm. cancel.
    intuition auto.
    pred_apply.
    erewrite INODE.rep_bxp_switch by eassumption.
    cancel.
    apply list2nmem_array_pick. sepauto.
    pred_apply. cancel.

    seprewrite.
    safestep.
    2: sepauto.
    rewrite rep_alt_equiv with (msalloc := MSAlloc a).
    cbv [rep_alt].
    erewrite <- INODE.rep_bxp_switch by eassumption.
    unfold cuttail.
    match goal with H: context [listmatch file_match flist ilist] |- _ =>
      erewrite file_match_length by solve [pred_apply' H; cancel | sepauto]
    end.
    rewrite Nat.sub_diag.
    cancel.
    rewrite listmatch_updN_removeN by sepauto.
    unfold file_match, listmatch. cancel.
    4: erewrite <- surjective_pairing, <- pick_upd_balloc_lift;
      auto using ilist_safe_upd_nil.
    (* There might be a better way to do this *)
    repeat rewrite <- surjective_pairing.
    repeat rewrite <- pick_upd_balloc_negb.
    rewrite <- pick_negb_upd_balloc.
    repeat rewrite <- pick_upd_balloc_lift.
    cancel.
    eapply bfcache_remove'; sepauto.
    unfold smrep. cancel.
    rewrite arrayN_except_upd by sepauto.
    rewrite arrayN_ex_smrep_single_helper_clear_dirty.
    cancel.
    destruct MSAlloc; cancel.
    rewrite selN_updN_ne; auto.
    cancel.
    cancel.
    eauto.
  Grab Existential Variables.
    all : try easy.
    all : solve [ exact bfile0 | intros; exact emp | exact nil].
  Qed.
  Proof.
    unfold recover; intros.
    step.
    step.
    unfold MSinitial; intuition.
  Qed.
  Proof.
    unfold cache_get, rep; intros.
    step.
    step.
    destruct ms; reflexivity.
    eapply bfcache_find; eauto.
  Qed.
  Proof.
    unfold cache_put, rep; intros.
    step.
    seprewrite.
    prestep. norm. cancel.
    intuition idtac.
    2: sepauto.
    pred_apply; cancel.
    erewrite <- updN_selN_eq with (l := ilist) at 2.
    rewrite listmatch_updN_removeN by sepauto.
    rewrite listmatch_isolate by sepauto.
    unfold file_match.
    cancel.
    eauto using bfcache_put.
    eauto.
  Unshelve.
    all: exact INODE.inode0.
  Qed.
  Proof.
    unfold flist_crash; intros.
    eapply forall2_length; eauto.
  Qed.
  Proof.
    unfold FSynced, synced_file, synced_list; simpl; intros.
    setoid_rewrite selN_combine; simpl.
    destruct (lt_dec n (length (BFData f))).
    rewrite repeat_selN; auto.
    rewrite map_length; auto.
    rewrite selN_oob; auto.
    rewrite repeat_length, map_length.
    apply not_lt; auto.
    rewrite repeat_length, map_length; auto.
  Qed.
  Proof.
    unfold FSynced; intros.
    erewrite list2nmem_array_eq with (l' := (BFData f)) by eauto.
    rewrite synced_list_selN; simpl; auto.
  Qed.
  Proof.
    unfold file_crash; intros.
    destruct H; intuition; subst; auto.
  Qed.
  Proof.
    unfold file_crash; intros; destruct H; intuition subst.
    unfold synced_list; simpl.
    rewrite map_fst_combine; auto.
    rewrite repeat_length; auto.
  Qed.
  Proof.
    unfold file_crash; intros.
    destruct H; intuition subst; simpl.
    rewrite synced_list_length.
    apply possible_crash_list_length; auto.
  Qed.
  Proof.
    unfold FSynced, file_crash; intros.
    destruct H; intuition subst; simpl; eauto.
    destruct f; simpl in *.
    f_equal.
    eapply list_selN_ext.
    rewrite synced_list_length.
    apply possible_crash_list_length; auto.
    intros.
    setoid_rewrite synced_list_selN.
    rewrite surjective_pairing at 1.
    rewrite H0.
    f_equal.
    erewrite possible_crash_list_unique with (b := x); eauto.
    erewrite selN_map; eauto.
  Qed.
  Proof.
    unfold FSynced, file_crash; intuition.
    destruct H; intuition subst; simpl.
    rewrite synced_list_selN; auto.
  Qed.
  Proof.
    unfold file_crash; intros.
    repeat deex.
    eapply list2nmem_crash_xform in H0; eauto.
    pred_apply.
    xform_norm.
    rewrite crash_xform_ptsto.
    cancel.
  Qed.
  Proof.
    unfold file_match, file_crash; intros.
    xform_norm.
    rewrite xform_listmatch_ptsto.
    cancel; eauto; simpl; auto.
  Qed.
  Proof.
    unfold listmatch, pprd.
    induction fs; destruct inos; xform_norm.
    cancel. instantiate(1 := nil); simpl; auto.
    apply Forall2_nil. simpl; auto.
    inversion H0.
    inversion H0.

    specialize (IHfs inos).
    rewrite crash_xform_sep_star_dist, crash_xform_lift_empty in IHfs.
    setoid_rewrite lift_impl with (Q := length fs = length inos) at 4; intros; eauto.
    rewrite IHfs; simpl.

    rewrite xform_file_match.
    cancel.
    eassign (f' :: fs'); cancel.
    apply Forall2_cons; auto.
    simpl; omega.
  Qed.
  Proof.
    unfold flist_crash.
    induction flist; cbn; intros; inversion H; constructor.
    unfold file_crash in *.
    deex.
    auto.
    auto.
  Qed.
  Proof.
    unfold smrep_single_helper, smrep_single, SS.For_all.
    intros.
    rewrite MapFacts.empty_o.
    eapply sm_sync_all_sep_star_swap; eauto.
    unfold lift_empty, sm_sync_all.
    setoid_rewrite SetFacts.empty_iff.
    intuition.
    denote None as Hm. rewrite Hm. auto.
    intros.
    eapply sm_sync_all_listpred_swap; eauto.
    cbn. intros.
    destruct_lifts.
    destruct_lift H2.
    setoid_rewrite SetFacts.empty_iff.
    eexists.
    eapply sm_sync_all_sep_star_swap; eauto.
    pred_apply. cancel.
    intros.
    apply sm_sync_invariant_lift_empty.
    pred_apply. cancel.
  Unshelve.
    all: exact unit.
  Qed.
  Proof.
  induction ilist; cbn; intros; auto.
  eapply sm_sync_all_sep_star_swap; eauto.
  intros.
  eauto using smrep_single_helper_sm_sync_all.
  Qed.
  Proof.
    unfold smrep, BALLOCC.smrep.
    intros.
    eapply sm_sync_all_sep_star_swap_r; eauto.
    intros.
    eapply sm_sync_all_arrayN_swap; eauto.
    cbn; intros.
    eauto using smrep_single_helper_sm_sync_all.
  Unshelve.
    exact INODE.inode0.
  Qed.
  Proof.
    intros.
    apply sep_star_assoc_2.
    eapply sm_synced_sep_star_l with (p := any).
    apply sep_star_assoc_1.
    eapply sm_sync_all_sep_star_swap; eauto.
    intros.
    eapply sm_sync_all_sep_star_swap_l; eauto.
    firstorder.
    eauto using smrep_sm_sync_all.
  Qed.
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite INODE.xform_rep, BALLOCC.xform_rep, BALLOCC.xform_rep.
    rewrite xform_file_list.
    do 2 intro. destruct_lifts.
    pred_apply.
    cancel.

    apply bfcache_emp.
    eauto using flist_crash_caches_cleared.
    eapply sep_star_smrep_sm_synced; eauto.
  Qed.
  Proof.
    unfold file_crash, file_match; intros.
    xform_norm.
    rewrite xform_listmatch_ptsto.
    xform_norm.
    pose proof (list2nmem_crash_xform _ H1 H) as Hx.
    apply crash_xform_sep_star_dist in Hx.
    rewrite crash_xform_ptsto in Hx; destruct_lift Hx.

    norm.
    eassign (mk_bfile (synced_list l) (BFAttr f) (BFCache f)); cancel.
    eassign (dummy).
    intuition subst; eauto.
  Qed.
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite INODE.xform_rep, BALLOCC.xform_rep, BALLOCC.xform_rep.
    rewrite xform_file_list.
    cancel.
    erewrite list2nmem_sel with (x := f) by eauto.
    apply forall2_selN; eauto.
    eapply list2nmem_inbound; eauto.

    rewrite locked_eq; unfold cache_rep.
    denote cache_rep as Hc; clear Hc.
    denote list2nmem as Hc; clear Hc.
    generalize dependent fs. generalize 0.
    induction fs'; simpl in *; intros.
    eapply BFM.mm_init.
    denote! (flist_crash _ _) as Hx; inversion Hx; subst.
    denote! (file_crash _ _) as Hy; inversion Hy; intuition subst.
    simpl.
    eapply pimpl_trans. apply pimpl_refl. 2: eapply IHfs'. cancel.
    eauto.

    eapply sep_star_smrep_sm_synced; eauto.

    apply list2nmem_ptsto_cancel.
    erewrite <- flist_crash_length; eauto.
    eapply list2nmem_inbound; eauto.
    Unshelve. all: eauto.
  Qed.
  Proof.
    intros.
    rewrite xform_rep_file by eauto.
    cancel. eauto.
    unfold file_crash in *.
    repeat deex; simpl.
    eapply list2nmem_crash_xform; eauto.
  Qed.
  Proof.
    Opaque vsmerge.
    intros.
    rewrite xform_rep_file by eauto.
    xform_norm.
    eapply file_crash_ptsto in H0; eauto.
    destruct_lift H0.
    cancel; eauto.
    Transparent vsmerge.
  Qed.
  Proof.
    unfold flist_crash, clear_caches, clear_cache.
    induction f; simpl; intros.
    - inversion H; subst; eauto.
    - inversion H; subst; eauto.
      simpl.
      rewrite IHf by eauto; f_equal.
      inversion H2; intuition subst; simpl; eauto.
  Qed.
  Proof.
    unfold file_crash, freepred, bfile0; intros.
    deex.
    f_equal.
    simpl in *.
    eapply possible_crash_list_length in H1.
    destruct vs; simpl in *; eauto.
    omega.
  Qed.
  Proof.
    unfold freepred; eauto.
  Qed.