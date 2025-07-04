    Proof.
      unfold items_per_val; simpl.
      rewrite valulen_is. apply Nat.eqb_eq.
      compute; reflexivity.
    Qed.
  Proof.
    intros; subst; auto.
  Qed.
  Proof.
    unfold bit2bool; destruct (bit_dec $0); auto.
    contradict e; apply natToWord_discriminate; auto.
  Qed.
  Proof.
    unfold bit2bool; destruct (bit_dec $1); auto.
    apply eq_sym in e; contradict e.
    apply natToWord_discriminate; auto.
  Qed.
  Proof. rewrite bit2bool_1; congruence. Qed.

  Fact bit2bool_0_ne : bit2bool $0 <> true.
  Proof. rewrite bit2bool_0; congruence. Qed.

  Local Hint Resolve bit2bool_0 bit2bool_1 bit2bool_0_ne bit2bool_1_ne.

  Lemma bit2bool2bit : forall b, bit2bool (bool2bit b) = b.
  Proof.
    destruct b; cbn; auto.
  Qed.
  Proof.
    unfold bit2bool; intros.
    destruct (bit_dec b); subst; auto.
  Qed.
  Proof.
    unfold lookup_f, name_is; intuition.
    apply andb_true_iff in H; tauto.
    destruct (weq name (DEName de)); auto.
    contradict H.
    rewrite andb_true_iff; easy.
  Qed.
  Proof.
    unfold lookup_f, name_is; intuition.
    apply andb_false_iff in H; intuition.
    destruct (weq name (DEName de)); intuition.
  Qed.
  Proof.
    induction l; unfold pimpl; simpl; intros.
    apply emp_notindomain; auto.
    inversion H; subst.

    destruct (Sumbool.sumbool_of_bool (is_valid a)).
    destruct (lookup_f_nf name a ix); try congruence.
    eapply notindomain_mem_except; eauto.
    eapply ptsto_mem_except.
    pred_apply; unfold dmatch at 1.
    rewrite e, IHl by eauto; simpl; cancel.

    pred_apply; rewrite IHl by eauto; cancel.
    unfold dmatch; rewrite e; simpl; auto.
  Qed.
  Proof.
    intros.
    eapply lookup_notindomain' with (ix := 0).
    eapply selN_Forall; eauto.
  Qed.
  Proof.
    unfold dmatch_ex, name_is; intros.
    destruct (weq (DEName de) (DEName de)); congruence.
  Qed.
  Proof.
    unfold dmatch_ex, name_is; intros.
    destruct (weq name (DEName de)); congruence.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    unfold dmatch_ex at 1, dmatch at 1, dmatch at 2, name_is.
    destruct (bool_dec (is_valid a) false).
    destruct (weq name (DEName a));
    rewrite sep_star_comm, sep_star_assoc;
    setoid_rewrite sep_star_comm at 2; rewrite IHl; cancel.

    destruct (weq name (DEName a)); subst.
    unfold pimpl; intros; exfalso.
    eapply ptsto_conflict_F with (m := m) (a := DEName a).
    pred_apply; cancel.
    eapply pimpl_trans with (b := (name |-> v * listpred dmatch l * [[DEInum a <> 0 ]] * _)%pred).
    cancel. rewrite IHl. cancel.
  Qed.
  Proof.
    induction l; intros.
    simpl; inversion H.
    pose proof (lookup_f_ok _ _ _ H0) as [Hx Hy].
    destruct ix; subst; simpl in *.
    unfold dmatch at 1; rewrite Hx, dmatch_ex_same; simpl.
    eapply pimpl_trans with (b := (DEName a |-> _ * listpred dmatch l * _)%pred).
    cancel. rewrite dmatch_ex_ptsto; cancel.

    assert (ix < length l) by omega.
    rewrite IHl; eauto; try solve [ cancel ].
    unfold dmatch_ex at 2, dmatch, name_is.
    destruct (bool_dec (is_valid _) false);
    destruct (weq (DEName _) _); try solve [ cancel ].
    rewrite e; repeat destruct_prod.
    unfold pimpl; intros; exfalso.
    eapply ptsto_conflict_F with (m := m) (a := DEName (w, (w0, (w1, (w2, (w3, u)))))).
    pred_apply; cancel.
  Qed.
  Proof.
    induction l; simpl; auto.
    unfold dmatch at 1; destruct (is_valid a); simpl.
    rewrite IHl; cancel.
    cancel.
  Qed.
  Proof.
    unfold dmatch, dent0.
    destruct (bool_dec (is_valid _) false); auto.
    contradict n.
    compute; auto.
  Qed.
  Proof.
    intros.
    apply listpred_updN; auto.
    rewrite dmatch_dent0_emp.
    eapply ptsto_mem_except; pred_apply.
    rewrite listpred_isolate by eauto.
    unfold dmatch at 2; rewrite H0; simpl.
    repeat cancel.
  Qed.
  Proof.
    unfold dmatch, mk_dent, is_valid, is_dir; intros; cbn.
    rewrite bit2bool_1, wordToNat_natToWord_idempotent', bit2bool2bit; auto.
  Qed.
  Proof.
    intros.
    apply listpred_updN; auto.
    rewrite dmatch_mk_dent by auto.
    eapply pimpl_apply. cancel.
    apply ptsto_upd_disjoint.
    apply negb_true_iff in H0.
    pred_apply.
    setoid_rewrite listpred_isolate with (def := dent0) at 1; eauto.
    unfold dmatch at 2; rewrite H0; cancel.
    eauto.
  Qed.
  Proof.
    induction n; intros; simpl; eauto.
    split; rewrite dmatch_dent0_emp, IHn; cancel.
  Qed.
  Proof.
    intros.
    pose proof (Dent.Defs.items_per_val_gt_0).
    erewrite <- Nat.sub_diag, <- updN_app2, Dent.Defs.block0_repeat by auto.
    apply listpred_updN; auto.
    rewrite app_length, repeat_length; omega.

    replace (length l) with (length l + 0) by omega.
    rewrite removeN_app_r, removeN_repeat, listpred_app by auto.
    rewrite listpred_dmatch_repeat_dent0.
    rewrite dmatch_mk_dent by auto.
    eapply pimpl_apply. cancel.
    apply ptsto_upd_disjoint; auto.
  Qed.
  Proof.
    induction l; cbn; intros m m' H H'.
    - apply emp_empty_mem_only in H.
      apply emp_empty_mem_only in H'.
      congruence.
    - unfold dmatch at 1 in H.
      unfold dmatch at 1 in H'.
      destruct bool_dec.
      apply IHl; pred_apply; cancel.
      eapply pimpl_trans in H; [| cancel..].
      eapply pimpl_trans in H'; [| cancel..].
      revert H. revert H'.
      unfold_sep_star.
      intros. repeat deex.
      match goal with H1 : (ptsto _ _ ?m), H2 : (ptsto _ _ ?m') |- _ =>
        assert (m = m') by (eapply ptsto_complete; eauto); subst
      end.
      f_equal.
      eauto.
  Qed.
  Proof.
    intros. intros m ?.
    replace m with (upd dmap name x) in * by (eauto using listpred_dmatch_eq_mem).
    apply ptsto_upd_disjoint; auto.
  Qed.
  Proof.
    unfold dmatch.
    intros; destruct bool_dec; destruct_lifts.
    congruence.
    unfold ptsto in *. intuition.
    destruct (weq name (DEName f)); subst.
    congruence.
    denote (m name = Some _) as Hm.
    denote (m _ = None) as Ha.
    rewrite Ha in Hm by auto.
    congruence.
  Unshelve.
    all: auto; repeat constructor.
  Qed.
  Proof.
    induction dmap; cbn; intros.
    congruence.
    revert H.
    unfold_sep_star.
    intros. repeat deex.
    unfold mem_union in *.
    destruct (m1 name) eqn:?.
    denote (Some _ = Some _) as Hs; inversion Hs; subst; clear Hs.
    eauto using dmatch_no_0_inum.
    eauto.
  Unshelve.
    all: eauto.
  Qed.
  Proof.
    unfold lookup, ifind_lookup_f, rep_macro, rep.
    safestep.
    safestep.
    or_r; cancel.
    eapply listpred_dmatch_no_0_inum; eauto.
    eapply ptsto_valid'.
    denote DEInum as Hd.
    erewrite selN_inb in Hd by auto.
    rewrite <- Hd.
    eapply lookup_ptsto; eauto.
    eapply lookup_ptsto; eauto.
    or_l; cancel.
    apply lookup_notindomain; auto.
  Unshelve.
    all: try (exact false || exact emp).
    all: eauto.
  Qed.
  Proof.
    unfold readdir, rep_macro, rep.
    safestep.
    step.
    apply readmatch_ok.
  Qed.
  Proof.
    unfold unlink, ifind_lookup_f, rep_macro, rep.
    step.
    step.

    apply Dent.Defs.item0_wellformed.
    msalloc_eq.

    denote (lookup_f) as HH.
    pose proof (lookup_f_ok _ _ _ HH) as [Hx Hy].

    step.

    eexists; split; eauto.
    apply listpred_dmatch_dent0_emp; auto.

    rewrite lookup_ptsto by eauto.
    unfold pimpl; intros.
    eapply sep_star_ptsto_indomain.
    pred_apply; cancel.

    rewrite <- notindomain_mem_eq; auto.
    eapply lookup_notindomain; eauto.
    eapply lookup_notindomain; eauto.

  Unshelve.
    all: easy.
  Qed.
  Proof.
    unfold link', ifind_lookup_f, ifind_invalid, rep_macro, rep.
    step.
    step; msalloc_eq.

    (* case 1: use avail entry *)
    cbv; tauto.
    step; msalloc_eq.
    or_r; cancel.
    eexists; split; eauto.
    apply listpred_dmatch_mem_upd; auto.
    eapply ptsto_upd_disjoint; eauto.
    apply BFILE.ilist_safe_refl.
    apply BFILE.treeseq_ilist_safe_refl.

    (* case 2: extend new entry *)
    cbv; tauto.

    step; msalloc_eq.
    or_r; cancel; eauto.
    eexists; split; eauto.
    eapply listpred_dmatch_ext_mem_upd; eauto.
    eapply ptsto_upd_disjoint; eauto.
  Unshelve.
    all: eauto.
  Qed.
  Proof.
    unfold link, rep_macro, rep.
    step.
    step; msalloc_eq.

    (* case 1: try entry hint *)
    step.
    erewrite Dent.items_length_ok with (xp := f) (m := (list2nmem (BFILE.BFData f))).
    unfold Dent.RA.RALen. auto.
    pred_apply; cancel.
    destruct is_valid eqn:?.
    (* working around a 'not found' Coq bug, probably #4202 in simpl *)
    prestep. unfold rep_macro, rep. norm. cancel.
    intuition ((pred_apply; cancel) || eauto).
    step.
    or_r. cancel.
    eauto.
    eapply listpred_dmatch_notindomain; eauto.
    eauto.
    cancel.

    (* case 2: use hinted entry *)
    step; msalloc_eq.
    erewrite Dent.items_length_ok with (xp := f) (m := (list2nmem (BFILE.BFData f))).
    unfold Dent.RA.RALen. auto.
    pred_apply; cancel.
    cbv; tauto.
    step.
    or_r; cancel.
    eexists; split; eauto.
    apply listpred_dmatch_mem_upd; auto.
    rewrite Bool.negb_true_iff; auto.
    erewrite Dent.items_length_ok with (xp := f) (m := (list2nmem (BFILE.BFData f))).
    unfold Dent.RA.RALen. auto.
    pred_apply; cancel.
    eapply ptsto_upd_disjoint; auto.
    apply BFILE.ilist_safe_refl.
    apply BFILE.treeseq_ilist_safe_refl.

    (* case 3: hint was out of bounds, so ignore it *)
    (* working around a 'not found' Coq bug, probably #4202 in simpl *)
    prestep. unfold rep_macro, rep. norm. cancel.
    intuition ((pred_apply; cancel) || eauto).
    step.
    or_r. cancel.
    eauto.
    eapply listpred_dmatch_notindomain; eauto.
    eauto.
    cancel.
  Unshelve.
    all: eauto.
  Qed.
  Proof.
    unfold dmatch, is_dir; intros.
    destruct (bool_dec (is_valid de) false).
    apply emp_complete; eauto.
    eapply ptsto_complete; pred_apply; cancel.
  Qed.
  Proof.
    induction l; simpl; auto.
    apply emp_complete; auto.
    intros m1 m2.
    unfold_sep_star; intuition.
    repeat deex; f_equal.
    eapply dmatch_complete; eauto.
    eapply IHl; eauto.
  Qed.
  Proof.
    unfold rep; intros.
    repeat deex.
    pose proof (Dent.rep_items_eq H0 H1); subst.
    eapply listpred_dmatch_eq; eauto.
  Qed.
  Proof.
    unfold rep, Dent.rep, Dent.items_valid.
    exists nil; firstorder.
    exists nil; simpl.
    setoid_rewrite Dent.Defs.ipack_nil.
    assert (emp (list2nmem (@nil valuset))) by firstorder.
    pred_apply; cancel.
    apply Forall_nil.
  Qed.
  Proof.
    unfold rep. intros. repeat deex.
    eauto using listpred_dmatch_no_0_inum.
  Qed.
  Proof.
    intros.
    apply eq_sym.
    eapply rep_mem_eq; eauto.

    unfold rep in *.
    repeat deex.
    eexists; intuition eauto.
    assert (delist0 = delist).
    eapply Dent.file_crash_rep_eq; eauto.
    subst; eauto.
  Qed.
  Proof.
    unfold rep; intros.
    repeat deex.
    eexists; intuition eauto.
    eapply Dent.file_crash_rep; eauto.
  Qed.