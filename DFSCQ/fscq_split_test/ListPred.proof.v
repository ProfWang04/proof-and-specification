  Proof.
    unfold listpred; intros; auto.
  Qed.
  Proof.
    induction l; simpl; intros; [omega |].
    destruct i; simpl; cancel.
    apply IHl; omega.
  Qed.
  Proof.
    induction l; simpl; intros; [omega |].
    destruct i; [cancel | simpl].
    destruct l; simpl in H; [omega |].
    cancel.
    eapply pimpl_trans; [| apply IHl ].
    cancel.
    apply pimpl_refl.
    omega.
  Qed.
  Proof.
    intros; rewrite listpred_fwd with (def:=def) by eauto; cancel.
  Qed.
  Proof.
    induction l; intro Hi.
    inversion Hi.
    simpl.
    destruct Hi.
    cancel.
    rewrite IHl by assumption.
    cancel.
  Qed.
  Proof.
     intros; subst; auto.
  Qed.
  Proof.
    induction l; unfold listpred, listpred', sep_star_fold, fold_right; auto.
  Qed.
  Proof.
    unfold listpred'.
    induction l1; destruct l2; unfold sep_star_fold; try cancel;
    rewrite IHl1; unfold sep_star_fold; cancel.
  Qed.
  Proof.
    unfold listpred'.
    induction l1; destruct l2; unfold sep_star_fold; try cancel;
    rewrite <- IHl1; unfold sep_star_fold; cancel.
  Qed.
  Proof.
    intros; replace listpred with listpred'.
    unfold piff; split.
    apply listpred'_app_fwd.
    apply listpred'_app_bwd.
    apply functional_extensionality.
    apply listpred_listpred'.
  Qed.
  Proof.
    intros.
    unfold removeN.
    rewrite listpred_app.
    unfold piff; split.
    rewrite listpred_fwd by eauto; cancel.
    eapply pimpl_trans2.
    apply listpred_bwd; eauto.
    cancel.
  Qed.
  Proof.
    intros.
    setoid_rewrite <- firstn_skipn with (n := n) at 1.
    rewrite listpred_app.
    split; cancel.
  Qed.
  Proof.
    intros.
    apply listpred_isolate; auto.
  Qed.
  Proof.
    intros; rewrite listpred_isolate with (def:=v);
       [ | rewrite length_updN; eauto].
    rewrite removeN_updN.
    rewrite selN_updN_eq; auto.
  Qed.
  Proof.
    intros.
    rewrite listpred_updN by auto.
    rewrite listpred_isolate with (def:=def) at 1 by eauto.
    cancel; auto.
  Qed.
  Proof.
    induction l; intuition; constructor; simpl in H0.
    intro Hin.
    revert H0.
    erewrite listpred_pick by (apply Hin).
    (* XXX should be possible not to bash this *)
    unfold_sep_star; intuition.
    do 2 destruct H0. intuition. destruct H4. do 2 destruct H3. intuition.
    eapply H.
    unfold_sep_star.
    exists x. exists x2.
    repeat split; intuition; eauto.
    subst. apply mem_disjoint_comm. apply mem_disjoint_comm in H0. rewrite mem_union_comm in H0.
    eapply mem_disjoint_union. eauto. eauto.

    revert H0.
    unfold_sep_star.
    intuition. do 2 destruct H0. intuition.
    eapply IHl; eauto.
  Qed.
  Proof.
    intros. split. apply lift_impl. intros. eapply listpred_nodup; eauto.
    cancel.
  Qed.
  Proof.
    intros.
    destruct_lift H0.
    rewrite listpred_nodup_piff in H0 by eauto.
    destruct_lift H0.
    eauto.
  Qed.
  Proof.
    intros.
    induction H; cbn; auto.
    rewrite IHPermutation. auto.
    split; cancel.
    rewrite IHPermutation1.
    rewrite IHPermutation2.
    auto.
  Qed.
  Proof.
    intros.
    induction l.
    cancel.
    rewrite listpred_nodup_piff; eauto.
    simpl; destruct (dec x a).
    cancel; inversion H2; rewrite remove_not_In; eauto.
    rewrite IHl; [ cancel | destruct H0; subst; tauto ].
  Qed.
  Proof.
    intros.
    induction l.
    cancel.
    simpl; destruct (dec x a); subst.
    - inversion H0. rewrite remove_not_In; eauto.
    - simpl; cancel.
      rewrite <- IHl. cancel. inversion H0. eauto. eauto.
  Qed.
  Proof.
    split.
    eapply listpred_remove; eauto.
    eapply listpred_remove'; eauto.
  Qed.
  Proof.
    induction l; simpl; intros.
    - apply emp_complete; eauto.
    - unfold sep_star in *; rewrite sep_star_is in *; unfold sep_star_impl in *.
      repeat deex.
      assert (m2 = m0) by eauto; subst.
      assert (m4 = m3) by eauto; subst.
      reflexivity.
  Qed.
  Proof.
    induction l; intros.
    rewrite listpred_nil; auto.
    simpl.
    rewrite H; intuition.
    rewrite IHl. cancel.
    intros.
    rewrite H; intuition.
  Qed.
  Proof.
    induction l; intros.
    rewrite listpred_nil; auto.
    simpl.
    rewrite H; intuition.
    rewrite IHl.
    split; cancel.
    intros.
    rewrite H; intuition.
  Qed.
  Proof.
    cbn; induction l; cbn.
    split; cancel.
    destruct partition eqn:?; cbn in *; intros.
    rewrite IHl.
    destruct f; split; cancel.
  Qed.
  Proof.
    induction l; cbn; intros.
    split; cancel.
    rewrite listpred_app.
    rewrite IHl.
    split; cancel.
  Qed.
Proof.
  intros; induction l.
  split; cancel.
  simpl; rewrite H; intuition.
  rewrite IHl.
  split; cancel; inversion H1; auto.
  intros.
  apply H; intuition.
Qed.
Proof.
  induction l1; intros; destruct l2; simpl in *; auto; inversion H2.
  f_equal.
  eapply H; auto; match goal with [H : _ |- _] => solve [eapply pimpl_apply; [> | exact H]; cancel] end.
  eapply IHl1; intros;
  repeat match goal with
    | [a : T, b : T |- ?a = ?b ] => eapply H
    | [H : _ |- _] => solve [intuition | apply H | eapply pimpl_apply; [> | exact H]; cancel]
  end.
Qed.
Proof.
  induction l; cbn; intros; auto.
  rewrite H; auto.
  cancel.
  eauto.
Qed.
Proof.
  induction l; intros; split; cancel.
  rewrite IHl, H by auto; cancel.
  rewrite IHl, H by (intuition; symmetry; auto); cancel.
Qed.
Proof.
  induction t; cbn; intros; unfold notindomain.
  cbv [emp] in *; auto.
  intuition.
  revert H.
  unfold_sep_star.
  intuition repeat deex.
  eapply mem_union_sel_none.
  unfold exis in *. deex.
  eapply ptsto_ne; eauto.
  eapply IHt; eauto.
Qed.
  Proof.
    unfold listmatch; intros.
    destruct_lift H; auto.
  Qed.
  Proof.
    unfold listmatch; intros.
    destruct_lift H; auto.
  Qed.
  Proof.
    unfold listmatch; intros.
    destruct_lift H; auto.
  Qed.
  Proof.
    unfold listmatch; cancel.
  Qed.
  Proof.
    unfold listmatch.
    split; cancel.
  Qed.
  Proof.
    intros; unfold listmatch.
    unfold piff; split.

    cancel.
    rewrite listpred_isolate with (i := i) (def := (ad, bd)) at 1.
    rewrite removeN_combine.
    rewrite selN_combine; auto.
    rewrite combine_length; rewrite <- H2; rewrite Nat.min_id; auto.
    repeat rewrite removeN_length by omega.
    omega.

    cancel.
    eapply removeN_length_eq with (a:=a) (b:=b) in H0; eauto.
    eapply pimpl_trans2.
    rewrite listpred_isolate with (i := i) (def := (ad, bd)).
    rewrite removeN_combine.
    rewrite selN_combine; auto.
    apply pimpl_refl.
    rewrite combine_length; rewrite <- H0; rewrite Nat.min_id; auto.
    repeat rewrite removeN_length by omega.
    cancel.
    eapply removeN_length_eq with (a:=a) (b:=b) in H1; eauto.
  Qed.
  Proof.
    intros; unfold listmatch.
    cancel.
    rewrite listpred_isolate with (i := i) (def := (ad, bd)) at 1.
    rewrite removeN_combine.
    rewrite selN_combine; auto.
    rewrite combine_length; rewrite <- H1; rewrite Nat.min_id; auto.
    repeat rewrite removeN_length by omega.
    omega.
  Qed.
  Proof.
    intros; unfold piff; split.
    rewrite listmatch_isolate with (ad := av) (bd := bv);
      [ | rewrite length_updN; eauto ..].
    repeat rewrite selN_updN_eq by auto.
    repeat rewrite removeN_updN; auto.

    eapply pimpl_trans2.
    rewrite listmatch_isolate with (i := i) (ad := av) (bd := bv);
      [ | rewrite length_updN; eauto ..].
    apply pimpl_refl.
    repeat rewrite selN_updN_eq by auto.
    repeat rewrite removeN_updN; auto.
  Qed.
  Proof.
    intros.
    rewrite listmatch_updN_removeN by auto.
    rewrite listmatch_isolate with (ad := ad) (bd := bd) by eauto.
    cancel; auto.
  Qed.
  Proof.
    intros.
    rewrite listmatch_updN_removeN by auto.
    rewrite listmatch_isolate with (ad := ad) (bd := bd) by eauto.
    cancel; rewrite sep_star_comm; auto.
  Qed.
  Proof.
    intros.
    eapply pimpl_trans2.
    eapply listmatch_isolate with (i := length a);
    try rewrite app_length; simpl; omega.
    rewrite removeN_tail.
    rewrite selN_last with (def := av); auto.
    rewrite H.
    rewrite removeN_tail.
    rewrite selN_last with (def := bv); auto.
    cancel; auto.
  Qed.
  Proof.
    unfold listmatch; intros; cancel.
    repeat rewrite combine_app by auto.
    rewrite listpred_app; cancel.
    repeat rewrite app_length; omega.
  Qed.
  Proof.
    unfold listmatch; cancel;
    repeat rewrite app_length in *;
    repeat (omega || rewrite combine_app || apply listpred_app).
  Qed.
  Proof.
    unfold listmatch; intros.
    rewrite listpred_split with (n := n).
    rewrite firstn_combine_comm.
    split; cancel.
    rewrite skipn_combine; eauto; cancel.
    repeat rewrite firstn_length; auto.
    repeat rewrite skipn_length; auto.
    rewrite skipn_combine; auto.
    eapply skipn_firstn_length_eq; eauto.
    eapply skipn_firstn_length_eq; eauto.
  Qed.
  Proof.
    intros.
    unfold listmatch.
    rewrite listpred_emp.
    cancel.
    intros; destruct x; simpl.
    apply H; solve [eapply in_combine_l; eauto |eapply in_combine_r; eauto].
  Qed.
  Proof.
    split.
    rewrite listmatch_length_pimpl; cancel.
    apply listmatch_emp; intuition.
    rewrite H; auto.
    unfold listmatch; rewrite listpred_emp_piff.
    cancel.
    intros; destruct x; simpl.
    apply H; solve [eapply in_combine_l; eauto |eapply in_combine_r; eauto].
  Qed.
  Proof.
    unfold listmatch. intros.
    rewrite repeat_length.
    destruct (Nat.eq_dec n (length l2)); [> | split; cancel].
    apply piff_star_l; subst.
    induction l2; intros.
    - rewrite combine_l_nil. split; cancel.
    - simpl. rewrite IHl2. auto.
  Qed.
  Proof.
    unfold listmatch. intros.
    rewrite repeat_length.
    destruct (Nat.eq_dec n (length l1)); [> | split; cancel].
    apply piff_star_l; subst.
    induction l1; intros.
    - rewrite combine_l_nil. split; cancel.
    - simpl. rewrite IHl1. auto.
  Qed.
  Proof.
    induction a; cbn; intros.
    exists nil.
    unfold listmatch. pred_apply; cancel.
    rewrite IHa.
    cancel.
    rewrite listmatch_cons with (b := b0).
    cancel.
  Qed.
  Proof.
    unfold listmatch.
    intros.
    rewrite listpred_rev.
    repeat rewrite rev_length.
    split; cancel; rewrite ?combine_rev by auto; cancel.
  Qed.
Proof.
  intros.
  unfold listmatch.
  rewrite listpred_lift.
  split; cancel.
  apply forall_forall2; eauto.
  apply forall2_forall; eauto.
  intros; simpl.
  destruct x; simpl; auto.
  apply H.
  eapply in_combine_l; eauto.
  eapply in_combine_r; eauto.
Qed.
Proof.
  intros.
  rewrite listmatch_lift with (P := fun x y => P x); eauto.
  split; intros m HH; rewrite listmatch_length_pimpl in HH; pred_apply; cancel.
  - erewrite <- map_fst_combine, <- Forall_map; eauto.
    match goal with [H : Forall2 _ _ _ |- _] => apply forall2_forall in H end.
    auto.
  - apply forall_forall2; auto.
    rewrite Forall_map.
    rewrite map_fst_combine; auto.
Qed.
Proof.
  unfold listmatch.
  intros.
  rewrite listpred_pimpl_replace; cancel.
  eauto using in_combine_l, in_combine_r.
Qed.
Proof.
  unfold listmatch; intros.
  rewrite listpred_piff_replace.
  split; cancel.
  intros a; destruct a; intros HH; simpl; auto.
  apply H; solve [eapply in_combine_l; eauto | eapply in_combine_r; eauto].
Qed.
Proof.
  induction a; cbn; intros.
  constructor.
  destruct b; cbn in *.
  unfold listmatch in *. destruct_lifts. congruence.
  rewrite listmatch_cons in H.
  constructor.
  unfold listmatch in H.
  intro H'.
  eapply in_selN_exists in H'.
  destruct H' as [? [? Hs] ].
  destruct_lifts.
  rewrite listpred_pick in H.
  unfold pprd, prod_curry in *.
  2: eapply in_selN.
  erewrite selN_combine in H by auto.
  2: rewrite combine_length_eq; eauto.
  rewrite Hs in H.
  destruct_lifts.
  eapply ptsto_conflict_F with (a := a) (m := m).
  pred_apply. cancel.
  eapply IHa with (b := b) (m := m). pred_apply. cancel.
Unshelve.
  all: eauto.
Qed.
Proof.
  induction l; destruct n; simpl; intros; try omega; auto.
  rewrite IHl.
  cancel.
  omega.
Qed.
Proof.
  induction l; destruct n; simpl; intros; try omega; auto.
  inversion H0; subst.
  rewrite IHl; auto.
  cancel.
  replace (length l) with n by omega.
  cancel.
Qed.
Proof.
  unfold listmatch; intros.
  split; cancel;
  generalize dependent bl;
  generalize dependent al;
  induction al; destruct bl; cancel; auto.
Qed.
Proof.
  unfold listmatch; intros.
  split; cancel; autorewrite with lists in *; auto;
  generalize dependent bl;
  generalize dependent al;
  induction al; destruct bl; cancel; auto.
Qed.
Proof.
  intros.
  rewrite listmatch_sym.
  rewrite listmatch_map_l.
  rewrite listmatch_sym; auto.
Qed.
Proof.
  intros; rewrite listmatch_map_l, listmatch_map_r; auto.
Qed.
Proof.
  induction l; simpl; intros; auto.
  split; cancel; rewrite IHl; auto.
Qed.
Proof.
  unfold listmatch; induction al; destruct vl.
  cancel. cancel.
  norml; inversion H0.
  cancel; inversion H0.
  unfold pimpl in *; intros.
  eapply IHal; eauto.
  pred_apply; cancel.
Qed.
Proof.
  intros.
  rewrite listmatch_sym.
  rewrite listmatch_lift_l.
  split; cancel; eauto; try apply listmatch_sym.
  simpl; auto.
Qed.
Proof.
  intros.
  unfold listmatch in *.
  repeat match goal with [H: context [lift_empty] |- _] => destruct_lift H end.
  split.
  1 : rewrite <- map_fst_combine with (a := la) (b := l1); auto.
  1 : rewrite <- map_fst_combine with (a := lb) (b := l2); auto.
  2 : rewrite <- map_snd_combine with (a := la) (b := l1); auto.
  2 : rewrite <- map_snd_combine with (a := lb) (b := l2); auto.
  all : f_equal; eapply listpred_unify; eauto.
  all : repeat rewrite combine_length_eq2; try omega.
  all : intros; destruct a, b; simpl in *.
  all : edestruct H;
        solve [eauto | subst; eauto |
               eapply in_combine_l; eauto |
               eapply in_combine_r; eauto ].
Qed.
Proof.
  induction l; intros; destruct l1, l2; auto.
  all : unfold listmatch in *;
        destruct_lift H0; destruct_lift H1;
        match goal with
        | [ H : 0 = S _ |- _] => inversion H
        | [ H : S _ = 0 |- _] => inversion H
        | [ |- _] => idtac
        end.
  f_equal; [> eapply H | eapply IHl]; intros;
    try match goal with
    | [ |- _ \/ _] => left; eauto
    | [ |- _ = _ ] => eapply H
    end; eauto.
  all : match goal with
  | [H : _ |- _] => solve [eapply pimpl_apply; [> | exact H]; cancel]
  end.
Qed.
Proof.
  intros.
  rewrite listmatch_sym in H0.
  rewrite listmatch_sym in H1.
  eapply listmatch_unify_r; eauto.
  intros.
  eapply H; eauto.
Qed.
Proof.
  induction l; simpl; intros; split; auto; xform_dist; auto.
  rewrite IHl; auto.
  rewrite IHl; auto.
Qed.
Proof.
  unfold pprd, prod_curry, crash_xform; intros.
  apply functional_extensionality; intros; destruct x; auto.
Qed.
Proof.
  unfold listmatch; intros; split; xform_norm;
  rewrite xform_listpred; cancel;
  rewrite crash_xform_pprd; auto.
Qed.
Proof.
  induction l; simpl; intros; auto.
  xform_dist.
  rewrite H.
  rewrite IHl; auto.
Qed.
Proof.
  induction l; simpl; intros; auto.
  xform_dist; auto.
  xform_dist.
  rewrite <- H.
  rewrite <- IHl; auto.
Qed.
Proof.
  split.
  apply xform_listpred_idem_l; intros.
  apply H.
  apply xform_listpred_idem_r; intros.
  apply H.
Qed.
Proof.
  unfold listmatch; intros.
  xform_norm; cancel.
  apply xform_listpred_idem_l; intros.
  destruct e; cbn; auto.
Qed.
Proof.
  unfold listmatch; intros.
  cancel.
  xform_normr.
  rewrite <- xform_listpred_idem_r; cancel.
  auto.
Qed.
Proof.
  split.
  apply xform_listmatch_idem_l; auto.
  apply H.
  apply xform_listmatch_idem_r; auto.
  apply H.
Qed.
Proof.
  induction l; simpl.
  rewrite crash_invariant_emp; auto.
  xform_dist.
  rewrite crash_xform_ptsto_exis, IHl.
  auto.
Qed.
Proof.
  induction l; simpl.
  rewrite crash_invariant_emp; auto.
  xform_dist.
  rewrite H.
  rewrite IHl.
  cancel.
Qed.
Proof.
  unfold listmatch; induction al; destruct vl; xform_norm.
  - cancel. instantiate (1 := nil); simpl; auto.
    unfold possible_crash_list; intuition; inversion H.
    rewrite synced_list_length; auto.
  - inversion H0.
  - inversion H0.
  - rewrite crash_xform_ptsto.
    specialize (IHal vl).
    rewrite crash_xform_sep_star_dist, crash_xform_lift_empty in IHal.
    inversion H; subst.
    setoid_rewrite lift_impl with (Q := length vl = length al) at 3; intros; eauto.
    rewrite IHal; simpl.

    cancel.
    eassign (v' :: l); cancel.
    simpl; cancel.
    apply possible_crash_list_cons; simpl; auto.
    rewrite synced_list_length in *; simpl; omega.
    apply possible_crash_list_cons; simpl; auto.
    rewrite synced_list_length in *; simpl; omega.
Qed.
Proof.
  induction l; simpl; eauto.
Qed.
Proof.
  induction l; simpl; intros; split; auto.
  apply sync_xform_emp.
  apply sync_xform_emp.
  rewrite sync_xform_sep_star_dist.
  rewrite IHl; auto.
  rewrite sync_xform_sep_star_dist.
  rewrite IHl; auto.
Qed.
Proof.
  induction l; simpl; intros; auto.
  apply sync_xform_emp.
  repeat rewrite sync_xform_sep_star_dist.
  rewrite IHl by eauto.
  rewrite H; auto.
Qed.