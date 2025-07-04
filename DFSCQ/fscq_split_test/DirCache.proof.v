  Proof.
    unfold rep.
    intuition eauto using SDIR.rep_mem_eq.
  Qed.
  Proof.
    unfold rep; intuition.
    apply SDIR.bfile0_empty.
    cbn in *. congruence.
  Qed.
  Proof.
    unfold rep; intuition.
    eapply SDIR.crash_rep; eauto.
    inversion H; intuition subst; cbn in *.
    congruence.
  Qed.
  Proof.
    unfold_sep_star.
    unfold SDIR.readmatch, ptsto.
    destruct a, b; cbn.
    intros. repeat deex.
    apply mem_disjoint_union in H.
    contradiction H.
    eauto.
  Qed.
  Proof.
    unfold Dcache.Equal; simpl.
    induction entries; intros; simpl.
    cancel.
    do 2 intro; pred_apply; cancel.
    enough (fst a <> fst a0).
    all : repeat match goal with
    | _ => reflexivity
    | [ H: _ |- _ ] => rewrite H; clear H
    | [ |- context [Dcache.find ?k1 (Dcache.add ?k2 _ _)] ] =>
      progress (rewrite ?DcacheDefs.MapFacts.add_eq_o,
                       ?DcacheDefs.MapFacts.add_neq_o by auto)
      || destruct (string_dec k1 k2); subst
    | [ |- context [Dcache.find _ (fill_cache' _ (Dcache.add (fst ?a) _ _))] ] =>
      eapply pimpl_trans in H as ?; [ | | apply (IHentries a)]; try cancel; destruct_lifts
    end.
    eapply readmatch_neq with (m := m).
    pred_apply; cancel.
  Qed.
  Proof.
    unfold fill_cache.
    induction entries; cbn; intros.
    intuition congruence.
    eapply pimpl_trans in H; [ | | apply fill_cache'_add_comm with (F := emp)]; try cancel.
    destruct_lifts.
    revert H.
    unfold_sep_star. unfold SDIR.readmatch at 1, ptsto.
    intros. repeat deex; cbn in *.
    rewrite H2.
    rewrite DcacheDefs.MapFacts.add_o.
    destruct string_dec; subst.
    erewrite mem_union_addr; eauto.
    rewrite mem_union_sel_r; eauto.
  Qed.
  Proof.
    unfold init_cache, rep_macro.
    hoare.
    msalloc_eq. cancel.
    cbn in *. subst_cache.
    eauto using fill_cache_correct.
  Qed.
  Proof.
    unfold get_dcache, rep_macro.
    hoare.
    Unshelve. all: eauto.
  Qed.
  Proof.
    unfold lookup.
    hoare.

    subst_cache.
    denote (Dcache.find) as Hf.
    denote (BFILE.BFCache _ = _) as Hb.
    erewrite Hf in * by eauto.
    destruct (dmap name) eqn:?; [ or_r | or_l ].
    assert (fst p <> 0).
      destruct p; cbn in *.
      intro; subst; eauto using SDIR.rep_no_0_inum.
    repeat ( denote! (SDIR.rep _ _) as Hx; clear Hx ).
    cancel.
    eauto using any_sep_star_ptsto.
    cancel.
  Unshelve.
    all: repeat (solve [eauto] || constructor).
  Qed.
  Proof.
    unfold readdir, rep_macro, rep.
    intros. ProgMonad.monad_simpl_one.
    eapply pimpl_ok2. eauto with prog.
    unfold SDIR.rep_macro.
    cancel; eauto.
    step.
  Qed.
  Proof.
    unfold unlink.
    hoare; msalloc_eq; cbn in *; subst_cache.
    - cancel.
    - unfold mem_except; cbn [fst snd].
      rewrite DcacheDefs.MapFacts.remove_o.
      denote (Dcache.find) as Hf.
      repeat destruct string_dec; (congruence || eauto).
    - cbn in *.
      rewrite mem_except_none; eauto.
      denote (Dcache.find) as Hf.
      erewrite Hf in *; eauto.
    - intros m' ?.
      replace m' with dmap in * by (eauto using SDIR.rep_mem_eq).
      denote (Dcache.find) as Hf.
      erewrite Hf in *; eauto.
  Unshelve.
    all: eauto.
  Qed.
  Proof.
    unfold SDIR.rep, DIR.rep, DIR.Dent.rep, DIR.Dent.items_valid, DIR.Dent.RA.RALen; eauto.
  Qed.
  Proof.
    unfold link'.
    hoare.

    msalloc_eq. subst_cache.
    or_r. cancel; eauto.
    cbn in *; subst_cache.
    cbv [fst snd upd].
    rewrite DcacheDefs.MapFacts.add_o.
    repeat destruct string_dec; (congruence || eauto).
  Unshelve.
    all : try exact Balloc.BALLOCC.Alloc.freelist0.
    all : eauto.
  Qed.
  Proof.
    unfold link.
    hoare.
  Unshelve.
    all: eauto.
  Qed.