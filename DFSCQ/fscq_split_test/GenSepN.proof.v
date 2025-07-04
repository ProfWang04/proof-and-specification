Proof.
  unfold list2nmem; intros.
  rewrite selN_oob; auto.
  rewrite map_length; auto.
Qed.
Proof.
  intros.
  destruct (lt_dec i (length l)); auto; exfalso.
  apply not_lt in n.
  apply list2nmem_oob in n.
  apply ptsto_valid' in H.
  rewrite H in n.
  inversion n.
Qed.
Proof.
  intros.
  assert (i < length l).
  eapply list2nmem_inbound; eauto.
  unfold list2nmem in H.
  apply ptsto_valid' in H.
  erewrite selN_map in H by auto.
  inversion H; eauto.
Qed.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold list2nmem, Mem.upd.
  autorewrite with core lists.

  destruct (eq_nat_dec x i).
  subst; erewrite selN_updN_eq; auto.
  rewrite map_length; auto.

  erewrite selN_updN_ne; auto.
Qed.
Proof.
  intros.
  rewrite listupd_memupd; auto.
  apply sep_star_comm.
  apply sep_star_comm in H.
  eapply ptsto_upd; eauto.
  eapply list2nmem_inbound; eauto.
Qed.
Proof.

  intros.
  destruct (lt_dec a (length l)).

  eapply list2nmem_updN with (y := selN l a def) in H.
  rewrite updN_twice in H.
  rewrite updN_selN_eq in H; auto.
  apply list2nmem_inbound in H.
  rewrite length_updN in H.
  congruence.
Qed.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold list2nmem, Mem.upd.

  destruct (lt_dec x (length l)).
  - subst; rewrite selN_map with (default' := a).
    destruct (eq_nat_dec x (length l)); subst.
    + rewrite selN_last; auto.
    + rewrite selN_map with (default' := a); auto.
      rewrite selN_app; auto.
    + rewrite app_length; simpl; omega.
  - destruct (eq_nat_dec x (length l)).
    + subst; erewrite selN_map with (default' := a).
      rewrite selN_last; auto.
      rewrite app_length; simpl; omega.
    + repeat erewrite selN_oob with (def := None); try rewrite map_length; auto.
      omega.
      rewrite app_length; simpl; intuition.
Qed.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold list2nmem, Mem.insert.

  destruct (lt_dec x (length l)).
  - subst; rewrite selN_map with (default' := a) by ( rewrite app_length; omega ).
    destruct (eq_nat_dec x (length l)); subst.
    + rewrite selN_last; auto.
      rewrite selN_oob by ( rewrite map_length; omega ); auto.
    + rewrite selN_map with (default' := a); auto.
      rewrite selN_app; auto.
  - destruct (eq_nat_dec x (length l)).
    + subst; erewrite selN_map with (default' := a) by ( rewrite app_length; simpl; omega ).
      rewrite selN_last; auto.
      rewrite selN_oob by ( rewrite map_length; omega ); auto.
    + repeat erewrite selN_oob with (def := None); try rewrite map_length; auto.
      omega.
      rewrite app_length; simpl; intuition.
Qed.
Proof.
  intros.
  erewrite listapp_memupd; eauto.
  apply ptsto_upd_disjoint; auto.
  unfold list2nmem, selN.
  rewrite selN_oob; auto.
  rewrite map_length.
  omega.
Qed.
Proof.
  intros.
  generalize dependent F.
  generalize dependent l.
  induction l'; intros; simpl.
  - rewrite app_nil_r.
    apply emp_star_r.
    apply H.
  - apply sep_star_assoc.
    assert (Happ := list2nmem_app F l a H).
    assert (IHla := IHl' (l ++ a :: nil) (sep_star F (ptsto (length l) a)) Happ).
    replace (length (l ++ a :: nil)) with (S (length l)) in IHla.
    replace ((l ++ a :: nil) ++ l') with (l ++ a :: l') in IHla.
    apply IHla.
    rewrite <- app_assoc; reflexivity.
    rewrite app_length; simpl.
    symmetry; apply Nat.add_1_r.
Qed.
Proof.
  intros; apply functional_extensionality; intros.
  destruct (lt_dec x (length l - 1)); unfold list2nmem.
  - rewrite selN_map with (default' := def).
    rewrite selN_removelast by omega; auto.
    rewrite length_removelast by auto; omega.
  - rewrite selN_oob; auto.
    rewrite map_length.
    rewrite length_removelast by auto.
    omega.
Qed.
Proof.
  intros; apply functional_extensionality; intros.
  erewrite list2nmem_removelast_is with (def := def) by eauto.
  unfold list2nmem.
  destruct (lt_dec x (length l - 1));
  destruct (eq_nat_dec x (length l - 1)); subst; intuition.
  omega.
  erewrite selN_map with (default' := def); auto.
  omega.
  erewrite selN_oob; auto.
  rewrite map_length.
  omega.
Qed.
Proof.
  unfold mem_disjoint; intros; firstorder.
  pose proof (H a); firstorder.
  pose proof (H1 v); firstorder.
  destruct (m2 a); auto.
  pose proof (H2 v0); firstorder.
Qed.
Proof.
  unfold_sep_star; unfold ptsto; intuition; repeat deex.
  assert (m1 = list2nmem (removelast l)); subst; auto.
  apply functional_extensionality; intros.
  rewrite list2nmem_removelast_list2nmem; auto.

  destruct (eq_nat_dec x (length l - 1)); subst.
  apply mem_disjoint_comm in H0. 
  eapply mem_disjoint_either; eauto.

  rewrite H1; unfold mem_union.
  destruct (m1 x); subst; simpl; auto.
  apply eq_sym; apply H5; auto.
Qed.
Proof.
  unfold mem_except, list2nmem.
  intros.
  eapply functional_extensionality; cbn; intros a.
  destruct Nat.eq_dec.
  rewrite selN_oob; auto.
  autorewrite with lists. omega.
  rewrite map_app; cbn.
  destruct (lt_dec a (length l)).
  rewrite selN_app; eauto.
  autorewrite with lists; eauto.
  repeat rewrite selN_oob; auto.
  all: autorewrite with lists; cbn; omega.
Qed.
Proof.
  induction l using rev_ind; intros; firstorder; simpl.
  erewrite listapp_memupd; try omega.
  eapply arrayN_app_memupd; try omega.
  eauto.
Qed.
Proof.
  intros; subst; apply list2nmem_array.
Qed.
Proof.
  intros.
  case_eq (lt_dec n (length l)); intros.
  - rewrite <- firstn_skipn with (l := l) (n := n) at 3.
    replace n with (length (firstn n l)) at 2.
    apply list2nmem_arrayN_app.
    apply list2nmem_array.
    apply firstn_length_l; omega.
  - rewrite firstn_oob by omega.
    rewrite skipn_oob by omega.
    eapply pimpl_apply.
    cancel.
    apply list2nmem_array.
Qed.
Proof.
  unfold list2nmem.
  intros.
  eapply Permutation.NoDup_Permutation.
  eapply listpred_nodup; eauto.
  decide equality.
  intuition.
  eapply ptsto_conflict; eauto.
  apply seq_NoDup.
  split; intros.
  eapply listpred_remove in H; eauto.
  destruct_lift H.
  eapply ptsto_valid in H.
  eapply in_seq.
  destruct (lt_dec x (length l)); try omega.
  rewrite selN_oob in H by (autorewrite with lists; omega).
  congruence.
  intros.
  eauto using ptsto_conflict.
  destruct (In_dec Nat.eq_dec x t).
  eapply listpred_remove in H; eauto.
  eauto using ptsto_conflict.
  eapply listpred_ptsto_notindomain in H; eauto.
  cbv [notindomain list2nmem] in *.
  denote seq as Hs.
  eapply in_seq in Hs.
  erewrite selN_map in * by omega.
  congruence.
Unshelve.
  all: try exact Nat.eq_dec.
  destruct l; cbn in *; eauto; omega.
Qed.
Proof.
  intros.
  pose proof list2nmem_array as Hp.
  eapply H in Hp.
  eapply listpred_permutation.
  eapply listpred_ptsto_list2nmem; auto.
Qed.
Proof.
  unfold list2nmem, list2nmem_off; intros.
  apply functional_extensionality; intros.
  rewrite <- minus_n_O.
  reflexivity.
Qed.
Proof.
  induction l; auto; simpl; intros.
  destruct (eq_nat_dec a0 start); [omega |].
  apply IHl; omega.
Qed.
Proof.
  induction l; intros; apply functional_extensionality; intros.
  unfold list2nmem_off; destruct (lt_dec x n); auto.

  unfold list2nmem_off; simpl in *.

  destruct (lt_dec x n).
  destruct (eq_nat_dec x n); [omega |].
  rewrite list2nmem_fix_below by omega.
  auto.

  destruct (eq_nat_dec x n).
  rewrite e; replace (n-n) with (0) by omega; auto.

  assert (x - n <> 0) by omega.
  destruct (x - n) eqn:Hxn; try congruence.

  rewrite <- IHl.
  unfold list2nmem_off.

  destruct (lt_dec x (S n)); [omega |].
  f_equal; omega.
Qed.
Proof.
  intros.
  rewrite list2nmem_off_eq.
  eapply list2nmem_fix_off_eq.
Qed.
Proof.
  intros.
  repeat rewrite list2nmem_fix_off_eq.
  generalize dependent b.
  generalize dependent start.
  induction a; simpl; intros; apply functional_extensionality; intros.
  - unfold mem_union. rewrite <- plus_n_O. auto.
  - unfold mem_union in *.
    destruct (eq_nat_dec x start); eauto.
    rewrite IHa.
    replace (S start + length a0) with (start + S (length a0)) by omega.
    auto.
Qed.
Proof.
  unfold mem_disjoint, list2nmem_off, not; intros; repeat deex;
    destruct (lt_dec a0 sa); destruct (lt_dec a0 sb); try congruence;
    apply selN_map_some_range in H0;
    apply selN_map_some_range in H2;
    omega.
Qed.
Proof.
  destruct l; simpl; auto.
  unfold_sep_star; unfold ptsto, list2nmem; simpl; intros.
  repeat deex.
  unfold mem_union in H0.
  apply equal_f with (start) in H0.
  rewrite H2 in H0.
  congruence.
Qed.
Proof.
  destruct l; simpl; auto.
  unfold list2nmem, emp; intros.
  pose proof (H start).
  destruct (eq_nat_dec start start); simpl in *; congruence.
Qed.
Proof.
  induction l'; simpl; intros.
  - erewrite list2nmem_nil_array; eauto.
  - destruct l.
    + eapply list2nmem_array_nil with (start:=start).
      auto.
    + simpl in *.
      unfold sep_star in H; rewrite sep_star_is in H; unfold sep_star_impl in H.
      repeat deex.
      unfold ptsto in H1; destruct H1.
      f_equal.
      * eapply equal_f with (start) in H0 as H0'.
        unfold mem_union in H0'.
        rewrite H1 in H0'.
        destruct (eq_nat_dec start start); congruence.
      * apply IHl' with (start:=S start); eauto; try omega.
        assert (m2 = list2nmem_fix (S start) l'); subst; auto.

        apply functional_extensionality; intros.
        unfold mem_union in H0.
        apply equal_f with x in H0.
        destruct (eq_nat_dec x start).

        rewrite list2nmem_fix_below by omega.
        eapply mem_disjoint_either.
        eauto.
        rewrite <- e in H1.
        eauto.

        rewrite H0.
        rewrite H2; auto.
Qed.
Proof.
  intros; eapply list2nmem_array_eq' with (start:=0); try rewrite <- plus_n_O; eauto.
  erewrite <- list2nmem_fix_eq; eauto.
Qed.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  destruct (lt_dec x (length l)).
  - destruct l; [ simpl in *; omega | ].
    eapply isolateN_fwd with (i := x) in H; auto.

    assert (m x = Some (selN (v :: l) x v)).
    eapply ptsto_valid.
    pred_apply. cancel.

    assert (list2nmem (v :: l) x = Some (selN (v :: l) x v)).
    eapply ptsto_valid.
    pose proof (list2nmem_array (v :: l)).
    pred_apply. rewrite arrayN_isolate with (i := x) by auto. cancel.

    congruence.
  - eapply arrayN_oob with (i := x) in H; try omega.
    rewrite list2nmem_oob with (i := x); try omega.
    auto.
Qed.
Proof.
  intros.
  rewrite list2nmem_array_eq with (l':=l') (l:=l++a::nil); eauto.
  pred_apply.
  rewrite <- isolateN_bwd with (vs:=l++a::nil) (i:=length l) by
    ( rewrite app_length; simpl; omega ).
  rewrite firstn_app2 by auto.
  replace (S (length l)) with (length (l ++ a :: nil)) by (rewrite app_length; simpl; omega).
  rewrite skipn_oob by omega; simpl.
  instantiate (1:=a).
  rewrite selN_last by auto.
  cancel.
Qed.
Proof.
  induction m; simpl; intros.
  congruence.
  destruct (Nat.eq_dec off start).
  omega.
  replace (start + S (length m)) with (S start + length m) by omega.
  eapply IHm.
  eauto.
Qed.
Proof.
  intros.
  rewrite list2nmem_fix_eq in H.
  apply list2nmem_some_bound' in H.
  omega.
Qed.
Proof.
  induction l; simpl; intros.
  intuition.
  right.
  apply sep_star_assoc in H as H'.
  apply IHl in H'.
  intuition.
  subst. simpl.
  apply sep_star_comm in H.
  apply sep_star_assoc in H.
  apply ptsto_valid in H.
  apply list2nmem_some_bound in H.
  omega.
Qed.
Proof.
  intros.
  apply list2nmem_arrayN_bound in H; destruct H; auto.
  rewrite H; simpl; omega.
Qed.
Proof.
  intros.
  assert ((F * arrayN (@ptsto _ eq_nat_dec A) off (v :: nil))%pred (list2nmem l)).
  pred_apply; cancel.
  apply list2nmem_arrayN_bound in H0. intuition; try congruence.
  simpl in *; omega.
Qed.
Proof.
  destruct l.
  simpl; intros.
  congruence.
  destruct l.
  simpl. intros.
  unfold arrayN_ex.
  simpl.
  split; cancel.
  simpl. intros.
  congruence.
Qed.
Proof.
  intros; unfold arrayN_ex.
  erewrite arrayN_isolate with (default := def); eauto.
  simpl.
  unfold piff; split; cancel.
Qed.
Proof.
  intros; unfold arrayN_ex.
  erewrite isolate_fwd_upd; eauto.
  simpl.
  unfold piff; split; cancel.
Qed.
Proof.
  unfold arrayN_ex; intros; autorewrite with core lists;
  split; simpl; rewrite skipn_updN; eauto.
Qed.
Proof.
  intros.
  edestruct arrayN_except as [_ H']; eauto; apply H'; clear H'.
  unfold_sep_star.
  repeat eexists; eauto.
  cbv [Mem.upd mem_union].
  apply functional_extensionality.
  intros x. destruct eq_nat_dec; subst.
  destruct m; congruence.
  destruct (m x); congruence.
  intro; repeat deex.
  destruct eq_nat_dec; congruence.
Qed.
Proof.
  intros.
  eapply arrayN_except; eauto.
  eapply list2nmem_array; eauto.
Qed.
Proof.
  intros.
  eapply list2nmem_array_eq; autorewrite with core lists; auto.
  pred_apply.
  rewrite isolate_fwd_upd; auto.
  cancel.
Qed.
Proof.
  unfold arrayN_ex; intros.
  destruct ol.
  inversion H0.

  eapply list2nmem_array_eq with (l' := nl); eauto.
  pred_apply.
  rewrite firstn_removelast_eq; auto.
  rewrite skipn_oob by omega.
  unfold arrayN at 2.
  clear H; cancel.
Qed.
Proof.
  intros; pred_apply; cancel.
Qed.
Proof.
  intros.
  assert (arrayN (@ptsto _ eq_nat_dec V) 0 l (list2nmem l)) as Hx by eapply list2nmem_array.
  pred_apply; erewrite arrayN_except; eauto.
Qed.
Proof.
  intros.
  assert (arrayN (@ptsto _ eq_nat_dec (A * B)) 0 l (list2nmem l)) as Hx by eapply list2nmem_array.
  pred_apply; erewrite arrayN_except; eauto.
  rewrite <- surjective_pairing.
  cancel.
Qed.
Proof.
  intros.
  apply list2nmem_sel with (def:=def) in H.
  congruence.
Qed.
Proof.
  induction a; simpl; intros.
  - replace (start + 0) with start by omega.
    split; cancel.
  - rewrite sep_star_assoc.
    apply piff_star_l.
    replace (start + S (length a0)) with (S start + length a0) by omega.
    apply IHa.
Qed.
Proof.
  intros; subst.
  apply arrayN_combine'.
Qed.
Proof.
  induction a; simpl; intros; auto.
  rewrite skipn_selN_skipn with (def:=def).
  f_equal.
  eapply list2nmem_sel.
  pred_apply. cancel.
  eapply IHa.
  pred_apply. cancel.
  eapply list2nmem_ptsto_bound.
  pred_apply. cancel.
Qed.
Proof.
  intros.
  apply list2nmem_sel with (def:=a) in H.
  rewrite selN_last in H; auto.
Qed.
Proof.
  intros.
  apply arrayN_list2nmem in H0.
  rewrite skipn_app in H0.
  rewrite firstn_oob in H0.
  auto.
  omega.
  exact def.
Qed.
Proof.
  intros; rewrite list2nmem_fix_off_eq.
  generalize dependent off; induction l; simpl; intros.
  - firstorder.
  - apply sep_star_comm. eapply ptsto_upd_disjoint; eauto.
    apply list2nmem_fix_below.
    omega.
Qed.
Proof.
  intros.
  rewrite list2nmem_off_eq in *.
  rewrite list2nmem_off_app_union in H.
  eapply septract_sep_star.
  2: unfold septract; eexists; intuition.
  4: pred_apply' H; cancel.
  apply strictly_exact_to_exact_domain.
  apply arrayN_strictly_exact.
  apply list2nmem_off_disjoint; intuition.
  apply list2nmem_off_arrayN.
Qed.
Proof.
  unfold mem_except, list2nmem; intros.
  apply functional_extensionality; intro.
  destruct (Nat.eq_dec x a); subst; simpl; auto.
  erewrite selN_oob; auto.
  autorewrite with lists in *; omega.
Qed.
Proof.
  induction l using rev_ind; intros.
  inversion H.
  rewrite listapp_memupd.

  destruct (Nat.eq_dec a (length l)); subst.
  rewrite upd_eq; auto.
  rewrite selN_last; auto.
  rewrite upd_ne; auto.
  rewrite app_length in H; simpl in H.
  erewrite IHl by omega.
  rewrite selN_app1 by omega; auto.
Qed.
Proof.
  intros; split; cancel.
Qed.
Proof.
  intros.
  rewrite arrayN_isolate with (i:=i) (default := v) by (rewrite length_updN; auto).
  rewrite selN_updN_eq by auto.
  rewrite firstn_updN_oob by auto.
  rewrite skipN_updN' by auto.
  apply sep_star_reorder_helper1.
  eapply list2nmem_updN with (x := selN vl i v).
  apply sep_star_reorder_helper1.
  rewrite <- arrayN_isolate; auto.
Qed.
Proof.
  induction al; intros.
  apply Forall_nil.
  unfold listmatch in H; destruct vl; destruct_lift H.
  inversion H1.
  apply Forall_cons.
  eapply list2nmem_ptsto_bound.
  pred_apply; cancel.
  eapply IHal with (vl := vl).
  pred_apply.
  unfold listmatch; cancel.
Qed.
Proof.
  intros.
  repeat rewrite list2nmem_fix_off_eq in H.
  revert H. revert a b n.
  induction a; destruct b; simpl; firstorder.
  eapply equal_f with (x := n) in H; simpl in H.
  destruct (Nat.eq_dec n n); congruence.
  eapply equal_f with (x := n) in H.
  destruct (Nat.eq_dec n n); congruence.
  erewrite IHa with (b := b) (n := S n).
  eapply equal_f with (x := n) in H.
  destruct (Nat.eq_dec n n); try congruence.

  apply functional_extensionality; intros.
  destruct (Nat.eq_dec x n); subst.
  repeat rewrite list2nmem_fix_below; auto.
  eapply equal_f with (x0 := x) in H.
  destruct (Nat.eq_dec x n); try congruence.
Qed.
Proof.
  intros.
  apply list2nmem_inj' with (n := 0).
  repeat rewrite <- list2nmem_off_eq; auto.
Qed.
Proof.
  induction vl using rev_ind; simpl; intuition.
  unfold crash_xform, possible_crash; eexists; intuition.
  setoid_rewrite length_nil in H0; auto.
  apply possible_crash_list_length in H; auto.

  unfold crash_xform, possible_crash.
  eexists; intuition. eauto.
  destruct H as [H Hx].
  destruct (lt_eq_lt_dec a (length vl)).
  destruct s.
  assert (a < length vsl).
  rewrite H; autorewrite with lists; simpl; omega.

  right.
  exists (selN vsl a ($0, nil)).
  exists (selN vl a $0); intuition.
  apply selN_map; auto.
  unfold list2nmem, synced_list.
  erewrite selN_map.
  rewrite selN_combine, selN_app1, repeat_selN; auto.
  autorewrite with lists; simpl; omega.
  autorewrite with lists; auto.
  rewrite combine_length_eq; autorewrite with lists; simpl; omega.
  specialize (Hx a H1).
  rewrite selN_app1 in Hx; auto.

  right; subst.
  eexists; exists x; intuition.
  autorewrite with lists in H; simpl in H.
  unfold list2nmem; erewrite selN_map by omega; eauto.
  unfold list2nmem; rewrite synced_list_app.
  erewrite selN_map, selN_app2.
  rewrite synced_list_length, Nat.sub_diag; auto.
  rewrite synced_list_length; auto.
  rewrite app_length, synced_list_length; simpl; omega.
  rewrite app_length in H; simpl in H.
  assert (length vl < length vsl) as Hy by omega.
  specialize (Hx (length vl) Hy).
  rewrite selN_app2, Nat.sub_diag in Hx by omega; simpl in Hx.
  unfold vsmerge; eauto.

  left; split.
  rewrite app_length in H; simpl in H.
  unfold list2nmem; erewrite selN_oob; auto.
  rewrite map_length; omega.
  unfold list2nmem; erewrite selN_oob; auto.
  rewrite map_length, synced_list_length, app_length; simpl; omega.
  Unshelve. all: eauto.
Qed.
Proof.
  unfold crash_xform.
  induction vl using rev_ind; intros; auto.
  exists nil; deex.
  replace (list2nmem nil) with m'; auto.
  apply functional_extensionality; intro.
  specialize (H1 x).
  destruct H1; destruct H.
  rewrite H; auto.
  deex; unfold list2nmem in H; simpl in *; congruence.
  unfold possible_crash_list; intuition.
  inversion H.

  deex.

  (* Figure out [m' (length vl)] *)
  case_eq (m' (length vl)); [ intro p | ]; intro Hp.
  specialize (IHvl (pred_except F (length vl) p)).
  rewrite listapp_memupd in H1.

  pose proof (possible_crash_upd_mem_except H1) as Hx.
  rewrite mem_except_list2nmem_oob in Hx by auto.
  specialize (H1 (length vl)); destruct H1.
  contradict H; rewrite upd_eq by auto.
  intuition congruence.
  repeat deex.

  eapply pred_except_mem_except in H0 as Hy.
  destruct IHvl as [ ? Hz ].
  eexists; eauto.
  destruct Hz as [ Hz [ Heq HP ] ].
  rewrite map_length in Heq.

  unfold pred_except in Hz.
  rewrite <- Heq in Hz.
  rewrite <- listapp_meminsert in Hz; intuition.
  eexists; split; eauto.

  split; autorewrite with lists; simpl; intros.
  repeat rewrite app_length; omega.
  destruct (lt_dec i (length x0)); repeat rewrite map_app.
  setoid_rewrite selN_app1; try rewrite map_length; try omega.
  apply HP; auto.
  setoid_rewrite selN_app2; try rewrite map_length; try omega.
  rewrite <- Heq; replace (i - length x0) with 0 by omega; simpl.
  rewrite upd_eq in H by auto.
  destruct x; inversion H; subst; simpl.
  rewrite Hp in H1; inversion H1; subst.
  eauto.
  eauto.

  specialize (H1 (length vl)); destruct H1.
  destruct H; contradict H1.
  rewrite listapp_memupd, upd_eq; auto; congruence.
  repeat deex; congruence.
Qed.
Proof.
  unfold crash_xform.
  induction vl using rev_ind; intros; auto.
  deex; rewrite map_app.

  pose proof (H1 (length vl)) as Hx; destruct Hx.
  destruct H as [ H Hx ]; contradict Hx.
  rewrite listapp_memupd, upd_eq by auto; congruence.
  repeat deex; auto.
  rewrite listapp_memupd, upd_eq in H by auto; inversion H; subst.

  erewrite IHvl; simpl.
  rewrite app_length; simpl.
  rewrite <- repeat_app_tail.
  f_equal; omega.
  exists (mem_except m' (length vl)).
  intuition.

  apply pred_except_mem_except; eauto.
  replace (list2nmem vl) with (mem_except (list2nmem (vl ++ [(v', nil)])) (length vl)).
  apply possible_crash_mem_except; eauto.
  rewrite listapp_memupd.
  rewrite <- mem_except_upd.
  rewrite mem_except_list2nmem_oob; auto.
Qed.
Proof.
  intros.
  destruct H0 as [Heq Hx].
  apply crash_xform_list2nmem_synced in H.
  apply list_selN_ext with (default := ($0, nil)); intros.
  rewrite synced_list_length; auto.
  rewrite synced_list_selN.
  specialize (Hx _ H0); unfold vsmerge in Hx.
  rewrite surjective_pairing at 1.
  erewrite <- selN_map with (f := snd) in * by auto.
  rewrite H in *.
  rewrite repeat_selN in * by auto.
  simpl in *; intuition.
  rewrite <- H1; simpl; auto.
  Unshelve. all: eauto.
Qed.
Proof.
  intros.
  unfold possible_crash; intros.
  destruct (le_dec (length l) a);
  destruct (le_dec (length l') a).
  left.
  split;
  apply list2nmem_oob; omega.

  unfold possible_crash in H;
  specialize (H (S a)); intuition.
  unfold possible_crash in H;
  specialize (H (S a)); intuition.

  unfold possible_crash in H;
  specialize (H (S a)); intuition.
Qed.
Proof.
  induction l; destruct l'; intros; simpl; auto.

  unfold possible_crash in H.
  specialize (H 0); intuition.
  inversion H1.
  repeat deex.
  inversion H0.

  unfold possible_crash in H.
  specialize (H 0); intuition.
  inversion H.
  repeat deex.
  inversion H.

  erewrite IHl; eauto.
  eapply possible_crash_list2nmem_cons; eauto.
Qed.
Proof.
  unfold vssync; intros.
  destruct (lt_dec a (length d)).
  rewrite listupd_memupd in H by auto.
  eapply possible_crash_upd_nil; eauto.
  apply list2nmem_sel_inb; auto.
  rewrite updN_oob in H; auto; omega.
Qed.
Proof.
  induction al using rev_ind; simpl; auto; intros.
  rewrite vssync_vecs_app in H.
  apply IHal.
  eapply possible_crash_list2nmem_vssync; eauto.
Qed.
Proof.
  intros.
  rewrite crash_xform_diskIs; cancel.
  rewrite <- crash_xform_diskIs_r; eauto.
  eapply possible_crash_list2nmem_vssync_vecs; eauto.
Qed.
Proof.
  unfold setlen.
  destruct l; simpl in *; congruence.
Qed.
Proof.
  intros; subst l'.
  eapply arrayN_one.
  rewrite <- setlen_singleton.
  apply list2nmem_array.
Qed.
Proof.
  intros.
  apply list2nmem_inj.
  eapply ptsto_complete. eauto.
  unfold ptsto, list2nmem; simpl; intuition.
  destruct a'; try congruence.
Qed.
Proof.
  destruct a; eauto.
  intros; exfalso.
  unfold list2nmem, ptsto in *; intuition.
  destruct d.
  {
    simpl in *.
    congruence.
  }
  {
    assert (S a = 0 -> False) by omega.
    specialize (H1 0 H); simpl in *.
    congruence.
  }
Qed.
Proof.
  intros.
  eapply ptsto_a_list2nmem_a0 in H as H'; subst.
  eapply ptsto_0_list2nmem_mem_eq; eauto.
Qed.
Proof.
  unfold pimpl; intros.
  eapply list2nmem_array_mem_eq in H0.
  eapply list2nmem_array_mem_eq in H1.
  congruence.
Qed.
Proof.
  unfold pimpl; intros.
  apply pred_except_ptsto_pimpl in H.
  apply H.
  pred_apply.
  apply pred_except_pimpl_proper; auto.
  unfold pimpl; intros.
  apply list2nmem_array_mem_eq in H1; subst.
  firstorder.
Qed.
Proof.
  induction l; simpl; intros.
  apply emp_pimpl_notindomain.
  eapply sep_star_notindomain.
  eapply ptsto_notindomain; omega.
  eauto.
Qed.
Proof.
  induction l; simpl; intros.
  apply emp_pimpl_notindomain.
  eapply sep_star_notindomain.
  eapply ptsto_notindomain; omega.
  eapply IHl; omega.
Qed.
Proof.
  unfold arrayN_ex; intros.
  apply sep_star_notindomain.
  apply arrayN_notindomain_after.
  rewrite firstn_length. simpl. apply Min.le_min_l.
  apply arrayN_notindomain_before.
  omega.
Qed.
Proof.
  intros.
  rewrite arrayN_except with (i := off) by omega.
  rewrite <- pred_except_sep_star_ptsto_notindomain; auto.
  apply arrayN_ex_notindomain.
Qed.
Proof.
  intros.
  eapply pimpl_trans; [ | eapply pred_except_ptsto_pimpl; eauto ].
  eapply list2nmem_sel with (def := v) in H as H'; rewrite H'.
  apply arrayN_ex_pred_except.
  eapply list2nmem_ptsto_bound; eauto.
Qed.