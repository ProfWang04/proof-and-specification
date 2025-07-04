  Proof.
    intros; subst; auto.
  Qed.
  Proof.
    split; cancel.
  Qed.
  Proof.
    induction vs; simpl; intuition.

    inversion H.

    destruct i; simpl.

    replace (a0 + 0) with (a0) by omega.
    replace (a0 + 1) with (S a0) by omega.
    cancel.

    eapply pimpl_trans; [ apply pimpl_sep_star; [ apply pimpl_refl | apply IHvs ] | ]; clear IHvs.
    instantiate (1 := i); omega.
    simpl.
    replace (S (a0 + i)) with (a0 + S i) by omega.
    replace (S (a0 + i + 1)) with (a0 + S i + 1) by omega.
    cancel.
  Qed.
  Proof.
    intros.
    eapply pimpl_trans; [ apply isolateN_fwd' | ].
    eassumption.
    apply pimpl_refl.
  Qed.
  Proof.
    induction vs; simpl; intuition.

    inversion H.

    destruct i; simpl.

    replace (a0 + 0) with (a0) by omega.
    replace (a0 + 1) with (S a0) by omega.
    cancel.

    eapply pimpl_trans; [ | apply pimpl_sep_star; [ apply pimpl_refl | apply IHvs ] ]; clear IHvs.
    2: instantiate (1 := i); omega.
    simpl.
    replace (a0 + S i) with (S (a0 + i)) by omega.
    cancel.
  Qed.
  Proof.
    intros.
    eapply pimpl_trans; [ | apply isolateN_bwd' ].
    2: eassumption.
    apply pimpl_refl.
  Qed.
  Proof.
    unfold piff; split.
    apply isolateN_fwd; auto.
    apply isolateN_bwd; auto.
  Qed.
  Proof.
    intros.
    erewrite arrayN_isolate with (vs:=updN vs i v) (i:=i) (default:=v);
      autorewrite with lists; auto.
    unfold piff; split.
    cancel; autorewrite with lists; cancel.
    cancel; autorewrite with lists; cancel.
  Qed.
  Proof.
    intros.
    erewrite <- isolateN_bwd with (vs:=updN vs i v) (i:=i) (default:=v).
    rewrite selN_updN_eq by auto.
    rewrite firstn_updN_oob by auto.
    rewrite skipN_updN' by auto.
    cancel.
    rewrite length_updN.
    auto.
  Qed.
  Proof.
    induction a; split; simpl; auto.
    rewrite Nat.add_0_r; cancel.
    rewrite Nat.add_0_r; cancel.
    rewrite IHa.
    replace (S st + length a0) with (st + S (length a0)) by omega.
    cancel.
    rewrite IHa.
    replace (S st + length a0) with (st + S (length a0)) by omega.
    cancel.
  Qed.
  Proof.
    intros.
    destruct (lt_dec i (length a)).
    erewrite arrayN_isolate; eauto.
    setoid_rewrite arrayN_isolate with (i := 0) at 4.
    rewrite skipn_skipn, skipn_selN.
    replace (st + i + 0) with (st+i) by omega.
    replace (1 + i) with (S i) by omega.
    replace (i + 0) with i by omega.
    split; cancel.
    rewrite skipn_length.
    omega.
    rewrite firstn_oob, skipn_oob by omega.
    split; cancel.
    Grab Existential Variables.
    destruct a.
    contradict l; simpl; omega.
    exact v.
  Qed.
  Proof.
    destruct l; simpl; intros; try congruence.
    assert (length l = 0) by omega.
    apply length_nil in H0; subst; simpl; split; cancel.
  Qed.
  Proof.
    destruct l; simpl; intros; try omega.
    replace (a + 1) with (S a) by omega; auto.
  Qed.
  Proof.
    induction l; intros; auto; simpl in *.
    destruct (eq_nat_dec i 0); auto.
    subst; simpl in *; omega.

    unfold sep_star in H0; rewrite sep_star_is in H0; unfold sep_star_impl in H0.
    repeat deex.
    unfold mem_union.
    unfold ptsto in H2; destruct H2; rewrite H2.
    pose proof (IHl (S a0) (i - 1)).
    replace (S a0 + (i - 1)) with (a0 + i) in H3 by omega.
    apply H3; try omega.

    auto.
    omega.
  Qed.
  Proof.
    intros.
    replace i with (0 + i) by omega.
    eapply arrayN_oob'; eauto.
  Qed.
  Proof.
    induction l; intros; auto; simpl in *.
    unfold sep_star in H; rewrite sep_star_is in H; unfold sep_star_impl in H.
    repeat deex.
    unfold mem_union.
    unfold ptsto in H2; destruct H2; rewrite H2.
    eapply IHl; eauto.
    omega.
  Qed.
  Proof.
    intros.
    rewrite arrayN_isolate with (i := i).
    eapply pimpl_trans; [ apply pimpl_refl | | eapply ptsto_upd ].
    rewrite selN_updN_eq by auto.
    cancel.
    rewrite firstn_updN_oob by auto.
    rewrite skipn_updN by auto.
    pred_apply.
    rewrite arrayN_isolate by eauto.
    cancel.
    rewrite length_updN; auto.
    Grab Existential Variables. all: eauto.
  Qed.
  Proof.
    intros.

    eapply isolateN_bwd with (i := (length l)) (default := v).
    rewrite app_length; simpl; omega.

    rewrite firstn_app2; auto.
    rewrite selN_last; auto.
    rewrite skipn_oob; [ | rewrite app_length; simpl; omega ].
    unfold arrayN at 2; auto; apply emp_star_r.
    simpl.

    apply ptsto_upd_disjoint; auto.
    eapply arrayN_oob; eauto.
  Qed.
  Proof.
    induction vs1; destruct vs2; simpl; intros; auto.
    apply ptsto_valid in H0; congruence.
    apply ptsto_valid in H; congruence.
    apply ptsto_valid in H as Hx.
    apply ptsto_valid in H0 as Hy.
    rewrite Hx in Hy; inversion Hy; subst; clear Hx Hy; f_equal.
    apply ptsto_mem_except in H.
    apply ptsto_mem_except in H0.
    eapply IHvs1; eauto.
  Qed.
  Proof.
    induction vs; simpl; intros.
    apply emp_strictly_exact.
    apply sep_star_strictly_exact.
    apply ptsto_strictly_exact.
    eauto.
  Qed.
  Proof.
    intros.
    eapply ptsto_valid; pred_apply.
    rewrite arrayN_isolate with (i := a - st) by omega.
    replace (st + (a - st)) with a by omega.
    clear H; cancel.
  Qed.
  Proof.
    intros; destruct l.
    simpl in *; try omega.
    eexists; eapply arrayN_selN with (def := v); eauto; try omega.
  Qed.
  Proof.
    induction a as [|x a']; intros.
    simpl in *.
    rewrite length_nil; auto.
    destruct b as [|y b']; simpl in *.
    inversion H.
    inversion H.
    erewrite IHa' with (s := S s); eauto.
    f_equal.
    assert (m s = Some x /\ m s = Some y); intuition.
    all : try match goal with
      | [ H : (_ * (pts ?s ?x * _))%pred ?m |- ?m ?s = Some ?x] =>
        eapply ptsto_valid;
        eapply pimpl_apply; [> | exact H]; cancel
      | [ H : (_ * (_ * arrayN _ _ ?a))%pred ?m |- (_ * arrayN _ _ ?a)%pred _] =>
        eapply pimpl_apply; [> | exact H]; cancel
    end.
    remember (m s) as r; clear Heqr; subst.
    match goal with [H: Some _ = Some _ |- _] => inversion H end; auto.
  Qed.
Proof.
  induction l; cbn; intros; auto.
  rewrite H with (i := 0) by (auto; omega).
  rewrite IHl.
  split; cancel.
  intros.
  rewrite <- plus_Snm_nSm.
  rewrite H; (eauto; omega).
Qed.
Proof.
  induction l; cbn; intros; auto.
  rewrite IHl.
  auto.
Qed.
Proof.
  unfold vsupd; intros.
  rewrite length_updN; auto.
Qed.
Proof.
  unfold vsupd_range; intros.
  rewrite app_length.
  rewrite combine_length.
  rewrite Nat.min_l.
  rewrite skipn_length.
  omega.
  rewrite map_length.
  rewrite firstn_length_l; auto.
Qed.
Proof.
  unfold vsupd_range; intros.
  autorewrite with lists; simpl; auto.
Qed.
Proof.
  unfold vsupd, vsmerge; intros.
  unfold vsupd_range.
  autorewrite with lists; simpl.
  repeat replace (length (firstn i l)) with i
    by (rewrite firstn_length_l by omega; auto).
  rewrite updN_app2.
  erewrite firstn_plusone_selN by omega.
  rewrite map_app.
  rewrite combine_app
    by (rewrite map_length; repeat rewrite firstn_length_l; omega).
  rewrite <- app_assoc; f_equal; simpl.
  rewrite combine_length; autorewrite with lists.
  rewrite Nat.min_l; repeat rewrite firstn_length_l; try omega.
  replace (i - i) with 0 by omega.
  rewrite updN_0_skip_1 by (rewrite skipn_length; omega).
  rewrite skipn_skipn'; f_equal; f_equal.
  rewrite selN_app2.
  rewrite combine_length; rewrite Nat.min_l;
     autorewrite with lists; repeat rewrite firstn_length_l; try omega.
  replace (i + (i - i)) with i by omega.
  unfold vsmerge; auto.
  all: rewrite combine_length_eq2; autorewrite with lists;
    repeat rewrite firstn_length_l; omega.
Qed.
Proof.
  induction vs; auto.
  constructor; auto.
  apply incl_refl.
Qed.
Proof.
  induction l; intros; simpl.
  rewrite vsupd_range_nil.
  apply forall_incl_refl.

  destruct vs.
  inversion H.
  cbn.
  constructor.
  apply incl_tl; apply incl_refl.
  apply IHl.
  simpl in *; omega.
Qed.
Proof.
  unfold vsupd_range; intros.
  rewrite selN_app2.
  rewrite combine_length_eq.
  rewrite skipn_selN.
  f_equal; omega.
  rewrite map_length, firstn_length_l; omega.
  rewrite combine_length_eq; auto.
  rewrite map_length, firstn_length_l; omega.
Qed.
Proof.
  unfold vsupd_range; intros.
  rewrite selN_app1.
  rewrite selN_combine.
  erewrite selN_map.
  rewrite selN_firstn; auto.
  rewrite firstn_length_l; omega.
  rewrite map_length, firstn_length_l; omega.
  rewrite combine_length_eq; auto.
  rewrite map_length, firstn_length_l; omega.
Qed.
Proof.
  induction n; intros.
  apply vsupd_range_incl; auto.
  destruct (lt_dec n (length l)).

  erewrite firstn_S_selN by auto.
  rewrite <- vsupd_range_progress by omega.
  erewrite <- updN_selN_eq with (l := (vsupd_range vs l)) (ix := n).
  apply forall2_updN; eauto.
  rewrite vsupd_range_selN_oob.
  rewrite vsupd_range_selN_inb; auto; try omega.
  apply incl_refl.
  rewrite firstn_length_l; omega.
  rewrite firstn_length_l; omega.

  rewrite firstn_oob by omega.
  apply forall_incl_refl.
Qed.
Proof.
  unfold vssync_range; intros.
  autorewrite with lists.
  rewrite combine_length.
  rewrite Nat.min_l.
  rewrite skipn_length.
  autorewrite with lists.
  rewrite firstn_length_l; omega.
  autorewrite with lists.
  rewrite firstn_length_l; omega.
Qed.
Proof.
  unfold vssync, vssync_range; intros.
  rewrite updN_app2.
  erewrite firstn_S_selN by auto.
  rewrite map_app.
  rewrite repeat_app_tail.
  rewrite combine_app
    by (autorewrite with lists; rewrite firstn_length_l; omega).
  rewrite <- app_assoc; f_equal.
  rewrite combine_length; autorewrite with lists.
  rewrite Nat.min_l; repeat rewrite firstn_length_l; try omega.
  replace (m - m) with 0 by omega.
  rewrite updN_0_skip_1 by (rewrite skipn_length; omega).
  rewrite skipn_skipn; simpl.
  f_equal; f_equal.
  rewrite selN_app2.
  rewrite combine_length; rewrite Nat.min_l;
     autorewrite with lists; repeat rewrite firstn_length_l; try omega.
  replace (m + (m - m)) with m by omega.
  unfold vsmerge; auto.
  all: rewrite combine_length_eq2; autorewrite with lists;
    repeat rewrite firstn_length_l; omega.
Qed.
Proof.
  induction n; simpl; intros.
  cbn.
  apply forall_incl_refl.
  rewrite <- vssync_range_progress by omega.
  rewrite <- updN_selN_eq with (ix := n) (l := vs) (default := ($0, nil)) at 2.
  apply forall2_updN.
  apply IHn; omega.

  unfold vsmerge; simpl.
  unfold vssync_range.
  rewrite selN_app2, skipn_selN.
  rewrite combine_length_eq, map_length, firstn_length_l.
  rewrite Nat.sub_diag, Nat.add_0_r.
  apply incl_cons2; apply incl_nil.
  omega.
  rewrite map_length, firstn_length_l, repeat_length; omega.
  rewrite combine_length_eq, map_length, firstn_length_l; try omega.
  rewrite map_length, firstn_length_l, repeat_length; omega.
Qed.
Proof.
  unfold vsupsyn_range; intros.
  rewrite app_length.
  rewrite combine_length.
  rewrite Nat.min_l.
  rewrite skipn_length.
  omega.
  rewrite repeat_length; auto.
Qed.
Proof.
  unfold vsupsyn_range; intros.
  rewrite selN_app1.
  rewrite selN_combine, repeat_selN; auto.
  rewrite repeat_length; auto.
  rewrite combine_length_eq; auto.
  rewrite repeat_length; auto.
Qed.
Proof.
  unfold vsupsyn_range; intros.
  rewrite selN_app2.
  rewrite skipn_selN.
  rewrite combine_length_eq.
  rewrite le_plus_minus_r; auto.
  rewrite repeat_length; auto.
  rewrite combine_length_eq; auto.
  rewrite repeat_length; auto.
Qed.
Proof.
  unfold vsupd_range, vsupd; intros.
  rewrite updN_app2, selN_app2; rewrite combine_length, map_length, firstn_length, Nat.min_l; auto;
  try apply Nat.min_case_strong; intros; try omega.
  rewrite Nat.sub_diag, app_length; simpl.
  erewrite firstn_plusone_selN, map_app by omega.
  rewrite combine_app by (rewrite map_length, firstn_length_l by omega; auto); simpl.
  rewrite app_assoc_reverse, updN_0_skip_1, <- cons_app by (rewrite skipn_length; omega).
  rewrite skipn_skipn', skipn_selN, Nat.add_0_r.
  reflexivity.
Qed.
Proof.
  induction l; intros; simpl; auto.
  rewrite IHl.
  unfold vsupd.
  rewrite length_updN; auto.
Qed.
Proof.
  intros.
  rewrite vsupd_vecs_length.
  rewrite Forall_forall in H.
  apply H.
  apply in_selN; auto.
Qed.
Proof.
  induction l; intros.
  inversion H.
  destruct m; auto.
  simpl.
  rewrite IHl; auto.
  simpl in H.
  omega.
Qed.
Proof.
  unfold vsupd; intros.
  rewrite updN_comm by auto.
  repeat rewrite selN_updN_ne; auto.
Qed.
Proof.
  induction av; simpl; intros; auto.
  destruct a; simpl in *; intuition.
  rewrite <- IHav by auto.
  rewrite vsupd_comm; auto.
Qed.
Proof.
  induction l; intros; destruct a; simpl in *; auto; intuition.
  rewrite IHl by auto.
  unfold vsupd.
  rewrite selN_updN_ne; auto.
Qed.
Proof.
  unfold vsupd_vecs; intros.
  rewrite fold_left_app; auto.
Qed.
Proof.
  auto.
Qed.
Proof.
  intros.
  destruct (In_dec addr_eq_dec a (map fst avl)).
  - revert H H0 i; revert avl l a v.
    induction avl; auto; intros; destruct a.
    destruct i; simpl in H0; subst.

    destruct (In_dec addr_eq_dec n (map fst avl)).
    apply IHavl; auto.
    right; unfold vsupd; simpl.
    rewrite selN_updN_eq; auto.
    unfold vsupd; rewrite length_updN; simpl in *; auto.

    rewrite vsupd_vecs_cons, vsupd_vecs_vsupd_notin by auto.
    unfold vsupd; rewrite selN_updN_eq.
    rewrite vsupd_vecs_selN_not_in; auto.
    right; auto.
    rewrite vsupd_vecs_length; auto.

    rewrite vsupd_vecs_cons.
    apply IHavl; auto; unfold vsupd.
    destruct (addr_eq_dec a0 n); subst.
    rewrite selN_updN_eq; auto.
    right; auto.
    rewrite selN_updN_ne; auto.
    rewrite length_updN; auto.
  - rewrite vsupd_vecs_selN_not_in; auto.
Qed.
Proof.
  intros.
  destruct (lt_dec a (length l)).
  apply vsupd_vecs_selN_vsmerge_in'; auto.
  rewrite selN_oob in *; auto; try omega.
  rewrite vsupd_vecs_length; omega.
Qed.
Proof.
  intros.
  eapply selN_Forall2.
  rewrite vsupd_vecs_length; auto.
  intros.
  unfold incl; intros.
  apply vsupd_vecs_selN_vsmerge_in; eauto.
Qed.
Proof.
  intros.
  eapply selN_Forall2 with (da := ($0, nil)) (db := ($0, nil)).
  repeat rewrite vsupd_vecs_length; auto.
  repeat rewrite vsupd_vecs_length; auto.
  intros.

  generalize dependent vs.
  generalize dependent n.
  induction l; intros.
  rewrite firstn_nil; cbn.
  apply incl_refl.
  destruct n; simpl.
  unfold incl; intros.
  apply vsupd_vecs_selN_vsmerge_in; eauto.
  cbn.
  unfold vsupd; destruct a; simpl.
  destruct (addr_eq_dec n i); subst.
  rewrite selN_updN_eq; eauto.
  rewrite selN_updN_ne; eauto.

  apply IHl.
  rewrite vsupd_length.
  eapply Forall_cons2; eauto.
  rewrite vsupd_length; auto.
Qed.
Proof.
  intros; unfold vssync_vecs, vssync_vecs_rev.
  rewrite fold_left_rev_right; auto.
Qed.
Proof.
  intros.
  repeat rewrite vssync_vecs_rev_eq.
  unfold vssync_vecs_rev.
  rewrite rev_unit; reflexivity.
Qed.
Proof.
  induction l; intros; simpl; auto.
  rewrite IHl.
  unfold vssync.
  rewrite length_updN; auto.
Qed.
Proof.
  intros.
  rewrite vssync_vecs_length.
  rewrite Forall_forall in H.
  apply H.
  apply in_selN; auto.
Qed.
Proof.
  induction l; intros.
  inversion H.
  destruct m; auto.
  simpl.
  rewrite IHl; auto.
  simpl in H.
  omega.
Qed.
Proof.
  auto.
Qed.
Proof.
  induction l; intros; simpl; auto.
  destruct (addr_eq_dec a a0); subst; auto.
  repeat rewrite IHl.
  unfold vssync.
  repeat rewrite selN_updN_ne by auto.
  rewrite updN_comm; auto.
Qed.
Proof.
  induction l; intros.
  auto.
  rewrite vssync_vecs_cons.
  rewrite IHl.
  rewrite vssync_vecs_vssync_comm.
  rewrite vssync_vecs_cons.
  auto.
Qed.
Proof.
  induction l; intros.
  rewrite app_nil_r.
  auto.
  rewrite <- app_comm_cons.
  rewrite vssync_vecs_cons.
  change (a :: l) with ([a] ++ l).
  rewrite app_assoc.
  rewrite <- IHl.
  rewrite app_assoc.
  rewrite vssync_vecs_app.
  rewrite vssync_vecs_vssync_comm.
  auto.
Qed.
Proof.
  induction l; intros.
  auto.
  rewrite <- app_comm_cons.
  repeat rewrite vssync_vecs_cons.
  repeat rewrite vssync_vecs_vssync_comm.
  rewrite IHl; auto.
Qed.
Proof.
  unfold vs_synced, vssync.
  intros.
  rewrite <- H.
  destruct (lt_dec a (length l)).
  erewrite selN_inb, <- surjective_pairing by auto.
  rewrite updN_selN_eq; auto.
  rewrite updN_oob by omega.
  auto.
Qed.
Proof.
  unfold vs_synced, vssync.
  intuition.
  eapply selN_eq_updN_eq.
  destruct selN eqn:H'; cbn in *.
  rewrite H'; congruence.
Qed.
Proof.
  induction l; intros.
  auto.
  inversion H; subst.
  rewrite vssync_vecs_cons.
  rewrite vssync_vecs_vssync_comm.
  rewrite IHl; auto.
  eapply vs_synced_vssync_nop; auto.
Qed.
Proof.
  intros.
  apply vssync_vecs_nop; constructor.
Qed.
Proof.
  intros.
  unfold vssync.
  destruct (addr_eq_dec a b); subst; auto.
  repeat rewrite selN_updN_ne by auto.
  rewrite updN_comm; auto.
Qed.
Proof.
  unfold vsupd, vssync, vsmerge; intros.
  rewrite updN_twice.
  destruct (lt_dec a (length l)).
  rewrite selN_updN_eq; simpl; auto.
  rewrite selN_oob.
  repeat rewrite updN_oob by omega; auto.
  autorewrite with lists; omega.
Qed.
Proof.
  induction av; simpl; intros; auto.
  destruct a; simpl in *; intuition.
  rewrite IHav by auto.
  unfold vsupd, vsmerge.
  rewrite updN_comm by auto.
  rewrite selN_updN_ne; auto.
Qed.
Proof.
  induction l; simpl; auto; intuition.
  rewrite IHl; auto.
  unfold vssync.
  rewrite selN_updN_ne; simpl; auto.
Qed.
Proof.
  induction l; intros; auto.
  inversion H.
  destruct (addr_eq_dec a i); subst; simpl.
  destruct (in_dec addr_eq_dec i l).
  rewrite IHl; unfold vssync; auto.
  rewrite selN_updN_eq; simpl; auto.
  rewrite length_updN; auto.

  rewrite vssync_selN_not_in by auto.
  unfold vssync; rewrite selN_updN_eq; simpl; auto.

  inversion H; subst; try congruence.
  rewrite IHl; unfold vssync; auto.
  rewrite selN_updN_ne; auto.
  rewrite length_updN; auto.
Qed.
Proof.
  induction l; simpl; intros.
  apply forall_incl_refl.
  rewrite vssync_vecs_vssync_comm.
  rewrite <- updN_selN_eq with (ix := a) (l := vs) (default := ($0, nil)) at 2.
  apply forall2_updN.
  apply IHl; auto.
  eapply Forall_cons2; eauto.

  destruct (In_dec addr_eq_dec a l).
  rewrite vssync_vecs_selN_In; auto.
  unfold vsmerge; simpl.
  apply incl_cons2; apply incl_nil.
  inversion H; eauto.

  rewrite vssync_selN_not_in; auto.
  unfold vsmerge; simpl.
  apply incl_cons2; apply incl_nil.
Qed.
Proof.
  unfold synced_list; intros.
  rewrite selN_combine.
  destruct (lt_dec i (length l)).
  rewrite repeat_selN; auto.
  setoid_rewrite selN_oob; auto.
  omega. rewrite repeat_length; omega. omega.
  rewrite repeat_length; omega.
Qed.
Proof.
  unfold synced_list; intros.
  rewrite map_fst_combine; auto.
  rewrite repeat_length; auto.
Qed.
Proof.
  unfold synced_list; induction vsl; simpl; auto.
  f_equal; auto.
Qed.
Proof.
  unfold vsupsyn_range, synced_list; intros.
  rewrite skipn_oob by omega.
  rewrite app_nil_r; auto.
Qed.
Proof.
  unfold possible_crash_list; firstorder.
Qed.
Proof.
  unfold synced_list; intros.
  rewrite combine_length_eq; auto.
  rewrite repeat_length; auto.
Qed.
Proof.
  unfold synced_list; induction l; simpl; intros; auto.
  destruct a0; simpl; auto.
  rewrite IHl; auto.
Qed.
Proof.
  induction a; simpl; auto; intros.
  unfold synced_list at 1; simpl.
  f_equal.
  apply IHa.
Qed.
Proof.
  intros.
  eapply f_equal in H as HH.
  repeat rewrite synced_list_length in HH.
  generalize dependent b.
  induction a; intros; simpl in *.
  rewrite length_nil; auto.
  destruct b; simpl in *.
  inversion HH.
  unfold synced_list in *.
  simpl in *.
  inversion H; f_equal; auto.
Qed.
Proof.
  unfold synced_list; intros.
  repeat rewrite map_snd_combine; autorewrite with lists; auto.
Qed.
Proof.
  induction l; simpl; intros.
  erewrite map_snd_synced_list_eq; eauto.
  autorewrite with lists; auto.

  destruct a; intuition; simpl in *.
  inversion H0; subst.
  setoid_rewrite vsupd_vecs_vsupd_notin; auto.
  unfold vsupd.
  repeat rewrite map_snd_updN.
  f_equal.
  apply IHl; auto.
  f_equal; f_equal; f_equal.
  rewrite <- synced_list_updN.
  rewrite <- updN_vsupd_vecs_notin by auto.
  rewrite selN_updN_ne; auto.
Qed.
Proof.
  unfold possible_crash_list; simpl; intuition;
  autorewrite with lists in *; auto.
  destruct (Nat.eq_dec a i); subst.
  repeat rewrite selN_updN_eq; auto; omega.
  repeat rewrite selN_updN_ne; eauto.
Qed.
Proof.
  unfold possible_crash_list; intuition.
  eapply list_selN_ext; auto; intros.
  rewrite map_length; auto.
  rewrite <- H1 in H0.
  specialize (H2 _ H0).
  inversion H2.

  erewrite selN_map; eauto.
  rewrite H in H3.
  inversion H3.
Qed.
Proof.
  unfold possible_crash_list; intuition.
  rewrite synced_list_length in *.
  eapply list_selN_ext; auto; intros.
  specialize (H1 _ H).
  inversion H1.

  generalize H2.
  unfold synced_list; rewrite selN_combine; eauto.
  rewrite repeat_length; auto.

  generalize H2.
  unfold synced_list; rewrite selN_combine; simpl.
  rewrite repeat_selN by auto.
  intro Hx; inversion Hx.
  rewrite repeat_length; auto.
Qed.
Proof.
  unfold possible_crash_list; intuition.
  rewrite synced_list_length; auto.
  unfold synced_list; constructor.
  rewrite selN_combine; auto.
  rewrite repeat_length; auto.
Qed.
Proof.
  unfold possible_crash_list; intuition.
  simpl; omega.
  destruct i, vs, vsl; try now firstorder; eauto with arith.
Qed.
Proof.
  unfold possible_crash_list, vssync; intuition; rewrite length_updN in *; auto.
  specialize (H1 _ H).
  destruct (addr_eq_dec i a); subst.
  erewrite selN_updN_eq in H1 by auto; simpl in *. intuition.
  erewrite selN_updN_ne in H1 by auto; eauto.
Qed.
  Proof.
    unfold possible_crash_list.
    induction l; simpl; intros.
    cancel.
    instantiate (1 := nil).
    simpl; auto. auto.

    xform.
    rewrite IHl.
    cancel; [ instantiate (1 := v' :: l') | .. ]; simpl; auto; try cancel;
    destruct i; simpl; auto;
    destruct (H4 i); try omega; simpl; auto.
  Qed.
  Proof.
    unfold possible_crash_list.
    induction l; simpl; intros; auto.
    - intuition; destruct l'; simpl in *; try congruence.
      apply crash_invariant_emp_r.
    - intuition; destruct l'; simpl in *; try congruence.
      pose proof (H1 0) as H1'. simpl in H1'.
      rewrite IHl.
      rewrite crash_xform_sep_star_dist.
      rewrite <- crash_xform_ptsto_r with (v := a) by (apply H1'; omega).
      apply pimpl_refl.
      intuition.
      specialize (H1 (S i)). simpl in H1. apply H1. omega.
  Qed.
  Proof.
    induction l; simpl; auto; intros.
    xform.
    rewrite IHl.
    cancel; subst.
    inversion H; simpl in *; subst; auto.
    inversion H; simpl in *; subst.
    inversion H1.
    eapply Forall_cons2; eauto.
  Qed.
  Proof.
    intros.
    apply crash_xform_synced_arrayN.
    rewrite Forall_forall; intros.
    induction l; simpl in *.
    inversion H.
    inversion H; subst; simpl; auto.
  Qed.
  Proof.
    intros.
    apply crash_xform_synced_arrayN.
    rewrite Forall_forall; intros.
    induction l; simpl in *.
    inversion H.
    inversion H; subst; simpl; auto.
  Qed.
  Proof.
    induction vs; simpl; auto.
  Qed.
  Proof.
    induction l; intros; auto; simpl in *.
    destruct (eq_nat_dec i 0); auto.
    subst; simpl in *; omega.

    unfold sep_star in H0; rewrite sep_star_is in H0; unfold sep_star_impl in H0.
    repeat deex.
    unfold mem_union.
    unfold ptsto_subset in H2.
    destruct_lift H2.
    unfold ptsto in H1; destruct H1.
    pose proof (IHl (S a0) (i - 1)).
    replace (S a0 + (i - 1)) with (a0 + i) in H3 by omega.
    destruct (m1 (a0 + i)) eqn:?.
    contradict Heqo.
    rewrite H2; try congruence.
    omega.
    apply H3.
    omega.
    auto.
  Qed.
  Proof.
    intros.
    replace i with (0 + i) by omega.
    eapply arrayN_subset_oob'; eauto.
  Qed.
  Proof.
    cbn; intros.
    rewrite arrayN_isolate with (i := a - st) in H by omega.
    unfold ptsto_subset at 2 in H; destruct_lift H; simpl in *.
    eexists; split; try split.
    eapply ptsto_valid.
    pred_apply; replace (st + (a - st)) with a by omega; cancel.
    simpl; auto.
    auto.
  Qed.
  Proof.
    intros.
    rewrite arrayN_isolate with (i := i) in H by auto.
    unfold ptsto_subset at 2 in H; destruct_lift H.
    setoid_rewrite sep_star_comm in H.
    apply sep_star_assoc in H.
    apply ptsto_upd with (v := (v, vs')) in H.
    pred_apply.
    setoid_rewrite arrayN_isolate with (i := i) at 3.
    unfold ptsto_subset at 4.
    rewrite selN_updN_eq by auto.
    cancel.
    rewrite firstn_updN_oob by auto.
    rewrite skipn_updN by auto.
    cancel.
    rewrite length_updN; auto.
    Grab Existential Variables. all: eauto.
  Qed.
  Proof.
    unfold possible_crash_list.
    induction l; simpl; intros.
    cancel.
    instantiate (1 := nil).
    simpl; auto. auto.

    xform.
    rewrite IHl.
    rewrite crash_xform_ptsto_subset; unfold ptsto_subset, synced_list.
    cancel; [ instantiate (1 := v' :: l') | .. ]; simpl; auto; try cancel;
    destruct i; simpl; auto;
    destruct (H4 i); try omega; simpl; auto.
  Qed.
  Proof.
    unfold possible_crash_list.
    induction l; simpl; intros; auto.
    - intuition; destruct l'; simpl in *; try congruence.
      apply crash_invariant_emp_r.
    - intuition; destruct l'; simpl in *; try congruence.
      pose proof (H1 0) as H1'. simpl in H1'.
      rewrite IHl.
      rewrite crash_xform_sep_star_dist.
      rewrite <- crash_xform_ptsto_subset_r with (v := a) by (apply H1'; omega).
      rewrite ptsto_subset_pimpl_ptsto.
      apply pimpl_refl.
      intuition.
      specialize (H1 (S i)). simpl in H1. apply H1. omega.
  Qed.
  Proof.
    induction l; simpl; auto; intros.
    xform.
    rewrite IHl.
    cancel; subst.
    rewrite crash_xform_ptsto_subset; unfold ptsto_subset.
    cancel.
    inversion H; simpl in *; subst; auto.
    inversion H; simpl in *; subst.
    inversion H0.
    eapply Forall_cons2; eauto.
  Qed.
  Proof.
    intros.
    apply crash_xform_synced_arrayN_subset.
    rewrite Forall_forall; intros.
    induction l; simpl in *.
    inversion H.
    inversion H; subst; simpl; auto.
  Qed.
  Proof.
    intros.
    apply crash_xform_synced_arrayN_subset.
    rewrite Forall_forall; intros.
    induction l; simpl in *.
    inversion H.
    inversion H; subst; simpl; auto.
  Qed.
  Proof.
    induction l; intros; destruct l0; simpl in *; auto; try omega.
    apply sep_star_assoc.
    eapply IHl with (l0 := l0); eauto.
    setoid_rewrite sep_star_comm at 1.
    apply sep_star_assoc.
    eapply ptsto_upd.
    pred_apply; cancel.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    erewrite <- IHl.
    rewrite upd_nop; auto.
    eapply ptsto_valid.
    pred_apply; cancel.
    rewrite upd_nop; auto.
    pred_apply; cancel.
    eapply ptsto_valid.
    pred_apply; cancel.
  Qed.
  Proof.
    induction l; simpl; intros; auto.
    rewrite IHl by (intuition omega).
    destruct (addr_eq_dec off a0); subst.
    exfalso; intuition.
    rewrite Mem.upd_ne; auto.
  Qed.
  Proof.
    induction l; simpl; intros; try omega.
    case_eq (a0 - off); intros.
    replace off with a0 in * by omega.
    rewrite listupd_sel_oob; intuition.
    apply Mem.upd_eq; auto.

    erewrite IHl; try omega.
    replace (a0 - S off) with n by omega; auto.
  Qed.
  Proof.
    intros.
    destruct (lt_dec a off);
    destruct (ge_dec a (off + (length l)));
    try ( left; intuition; apply listupd_sel_oob; auto ).
    right; intuition.
    apply listupd_sel_inb; omega.
  Qed.
  Proof.
    induction l; intros; destruct l0; simpl in *; auto; try omega.
    apply sep_star_assoc.
    eapply IHl with (l0 := l0); eauto.
    setoid_rewrite sep_star_comm at 1.
    apply sep_star_assoc.
    apply sep_star_comm; destruct a, p.
    eapply ptsto_subset_upd.
    pred_apply; cancel.
    apply incl_refl.
  Qed.