  Proof.
    unfold selR; intros.
    destruct (lt_dec n (length l)); try omega; auto.
  Qed.
  Proof.
    unfold selR; intros.
    destruct (lt_dec n (length l)); auto; congruence.
  Qed.
  Proof.
    firstorder.
  Qed.
  Proof.
    unfold nthd; intros; rewrite selN_oob; auto; omega.
  Qed.
  Proof.
    unfold nthd, latest; intros; destruct ds; simpl in *.
    replace (length l - n) with 0 by omega.
    destruct l; firstorder.
  Qed.
  Proof.
    unfold pushd; intros; apply latest_cons.
  Qed.
  Proof.
    unfold popn; intros.
    rewrite nthd_0, cuttail_0.
    rewrite surjective_pairing; auto.
  Qed.
  Proof.
    unfold popn; intros.
    rewrite nthd_oob by omega.
    rewrite cuttail_oob by omega; auto.
  Qed.
  Proof.
    unfold latest; destruct ds, l; simpl; intuition; inversion H.
  Qed.
  Proof.
    unfold latest; destruct ds, l; simpl; intuition; inversion H.
  Qed.
  Proof.
    unfold popn; intros.
    rewrite cuttail_oob by omega; auto.
  Qed.
  Proof.
    unfold popn, singular; intros.
    rewrite cuttail_oob by omega.
    rewrite nthd_oob; auto.
  Qed.
  Proof.
    unfold popn; intros; simpl.
    rewrite cuttail_cuttail; f_equal.
    unfold nthd; simpl.
    rewrite cuttail_length.
    destruct (le_dec n (length (snd ds))).
    replace (length (snd ds) - (n + m)) with (length (snd ds) - n - m) by omega.
    unfold cuttail.
    destruct (lt_dec (length (snd ds) - n - m) (length (snd ds) - n)).
    rewrite selN_firstn at 1; auto.
    apply selN_inb; omega.
    rewrite selN_oob.
    f_equal; omega.
    rewrite firstn_length; apply Nat.min_case_strong; omega.
    rewrite cuttail_oob by omega.
    simpl; f_equal; omega.
  Qed.
  Proof.
    intros.
    replace (S n) with (1 + n) by omega.
    rewrite <- popn_popn.
    unfold popn at 2; simpl.
    rewrite cuttail_tail, cuttail_0.
    unfold nthd; simpl.
    rewrite app_length; simpl.
    rewrite selN_app2 by omega.
    replace (length ds + 1 - 1 - length ds) with 0 by omega; simpl; auto.
  Qed.
  Proof.
    induction l'; simpl; unfold pushd; simpl; intros; auto.
    rewrite IHl'.
    rewrite <- app_assoc.
    reflexivity.
  Qed.
  Proof.
    unfold popn, nthd; simpl; intros.
    rewrite cuttail_length, Nat.sub_add_distr.
    destruct (lt_dec m (length (snd ds))).
    destruct n.
    rewrite Nat.sub_0_r.
    rewrite selN_oob; auto.
    rewrite cuttail_length; auto.
    rewrite selN_cuttail; auto.
    erewrite selN_inb by omega; eauto.
    rewrite cuttail_length; omega.
    replace (length (snd ds) - m - n) with 0 by omega.
    rewrite cuttail_oob by omega; simpl.
    replace (length (snd ds) - m) with 0 by omega; auto.
 Qed.
  Proof.
    induction dlist; simpl; intros; auto.
    edestruct (IHdlist _ _ H).
    intuition.
    destruct ds.
    inversion H0; simpl in *.
    right. left. eauto.
    intuition.
    right. right. eauto.
  Qed.
  Proof.
    intros.
    assert (In d (rev l1) \/ d_in d (a, l2)).
    apply d_in_pushdlist.
    rewrite pushdlist_app. rewrite rev_involutive. eauto.
    intuition.
    left. apply in_rev. eauto.
  Qed.
  Proof.
    unfold nthd, d_in.
    destruct ds.
    destruct n.
    - left.
      apply selN_oob. omega.
    - destruct l; simpl snd.
      + eauto.
      + right.
        apply in_selN.
        simpl; omega.
  Qed.
  Proof.
    unfold d_in, latest.
    destruct ds; simpl.
    destruct l; simpl; intuition.
  Qed.
  Proof.
    unfold d_in; simpl; intuition.
  Qed.
  Proof.
    unfold d_in; simpl; intuition.
  Qed.
  Proof.
    destruct ds; unfold d_in; simpl; intuition.
  Qed.
  Proof.
    induction 1.
    - exists 0.
      erewrite nthd_0; eauto.
    - eapply in_selN_exists in H as H'.
      destruct H'.
      unfold nthd.
      exists (Datatypes.length (snd l)-x).
      replace (Datatypes.length (snd l) - (Datatypes.length (snd l) - x)) with x by omega.
      intuition.
      rewrite H2; eauto.
  Qed.
  Proof.
    destruct l.
    unfold latest, nthd, hd, fst, snd. 
    induction l.
    - simpl; auto.
    - unfold hd, fst, snd.
      replace (Datatypes.length (a :: l) - Datatypes.length (a :: l)) with 0 by omega.
      simpl; auto.
  Qed.
  Proof.
    intros.
    unfold pushd, latest.
    simpl; eauto.
  Qed.
  Proof.
    unfold popn; simpl; intros.
    rewrite cuttail_length; auto.
  Qed.
  Proof.
    intros.
    do 2 rewrite latest_nthd.
    rewrite length_popn.
    rewrite nthd_popn.
    destruct (le_dec n (length (snd ds))).
    f_equal; omega.
    rewrite nthd_oob, latest_nthd; auto.
    omega.
  Qed.
  Proof.
    induction l; eauto.
  Qed.
  Proof.
    split; intros.
    - induction H; simpl in *; eauto.
      apply SubsetIn.
      eapply list_subset_nil.
    - destruct ds, ds'; simpl in *.
      remember (l ++ [t]) as lt.
      remember (l0 ++ [t0]) as lt0.
      generalize dependent l.
      generalize dependent l0.
      generalize dependent t.
      generalize dependent t0.
      induction H; simpl in *; intros.
      + assert (@length T [] = length (l ++ [t])) by congruence.
        rewrite app_length in *; simpl in *; omega.
      + destruct l.
        * inversion Heqlt; subst.
          inversion H; subst; simpl in *.
          destruct l0.
         -- inversion Heqlt0; subst. apply NESubsetNil.
         -- assert (length [t] = length ((t1 :: l0) ++ [t0])) by congruence.
            rewrite app_length in *; simpl in *; omega.
        * inversion Heqlt; subst.
          destruct l0.
         -- inversion Heqlt0; subst.
            replace (t, t0 :: l) with (pushd t0 (t, l)) by reflexivity.
            apply NESubsetHead.
         -- inversion Heqlt0; subst.
            replace (t, t2 :: l) with (pushd t2 (t, l)) by reflexivity.
            replace (t0, t2 :: l0) with (pushd t2 (t0, l0)) by reflexivity.
            apply NESubsetIn.
            eapply IHListSubset; eauto.
      + destruct l.
        * inversion Heqlt; subst.
          inversion H.
          assert (@length T [] = length (l0 ++ [t0])) by congruence.
          rewrite app_length in *; simpl in *; omega.
        * simpl in *.
          inversion Heqlt; subst.
          replace (t, t1 :: l) with (pushd t1 (t, l)) by reflexivity.
          apply NESubsetNotIn.
          eapply IHListSubset; eauto.
  Qed.
  Proof.
    destruct ds.
    induction l.
    constructor.
    eapply NESubsetIn in IHl.
    eauto.
  Qed.
  Proof.
    induction l; intros; simpl.
    constructor.

    replace t with (fst (t, l)) at 1 by auto.
    econstructor.
    eauto.
  Qed.
  Proof.
    unfold latest.
    destruct ds, l; simpl.
    constructor.
    replace (_, _) with (pushd t0 (t, l)) by auto.
    eapply NESubsetHead; eauto.
  Qed.
  Proof.
    destruct l; intros; simpl.
    inversion H.

    replace t0 with (fst (t0, l)) at 1 by auto.
    replace t0 with (fst (t0, @nil T)) at 2 by auto.
    replace l with (snd (t0, l)) by auto.
    replace nil with (snd (t0, @nil T)) by auto.
    econstructor.
    apply nelist_subset_oldest.
  Qed.
  Proof.
    destruct ds; simpl.
    eapply nelist_subset_oldest_latest'.
  Qed.
  Proof.
    unfold popn, nthd; intros.
    destruct ds, ds'; simpl in *.
    generalize dependent l0.
    induction l.
    - unfold cuttail in *; simpl in *; eauto.
    - intros.
      destruct l.
      + unfold cuttail in *; simpl in *.
        inversion H; subst.
        replace (t, [t0]) with (pushd t0 (t, nil)) by reflexivity.
        eapply NESubsetHead.
      + replace (selN (a :: t1 :: l) (length (a :: t1 :: l) - 1) t) with (selN (t1 :: l) (length (t1 :: l) - 1) t) in H.
        2: simpl; rewrite <- minus_n_O; eauto.
        rewrite cuttail_cons in H by ( simpl; omega ).
        inversion H; subst.
        * replace (t, t0 :: t1 :: l) with (pushd t0 (t, t1 :: l)) by reflexivity.
          eapply NESubsetHead.
        * replace (t, a :: t1 :: l) with (pushd a (t, t1 :: l)) by reflexivity.
          replace (fst ds', a :: snd ds') with (pushd a (fst ds', snd ds')) by reflexivity.
          eapply NESubsetIn.
          eapply IHl.
          destruct ds, ds'; simpl in *; subst; eauto.
        * replace (t, a :: t1 :: l) with (pushd a (t, t1 :: l)) by reflexivity.
          eapply NESubsetNotIn.
          eapply IHl.
          destruct ds; simpl in *; subst; eauto.
  Qed.
  Proof.
    induction n; simpl; intros.
    rewrite popn_0 in H; auto.
    replace (S n) with (1 + n) in H by omega.
    rewrite <- popn_popn in H.
    apply IHn in H.
    eapply nelist_subset_popn1; eauto.
  Qed.
  Proof.
    induction n; simpl; intros.
    rewrite nthd_0.
    apply nelist_subset_oldest_latest; auto.
    replace (S n) with (1 + n) by omega.
    rewrite <- nthd_popn.
    erewrite <- latest_popn.
    eapply nelist_subset_popn.
    apply IHn; simpl.
    rewrite cuttail_length.
    omega.
  Qed.
  Proof.
    unfold popn, nthd; intros.
    apply nelist_list_subset in H.
    apply nelist_list_subset; simpl.
    generalize dependent H.
    generalize (snd ds ++ [fst ds]); intros.
    destruct ds'; simpl in *.
    destruct l0.
    - simpl in *; eauto.
    - match goal with
      | [ |- ListSubset l ?l' ] => replace l' with (t0 :: l0)
      end.
      + generalize dependent H. generalize (t0 :: l0). intros.
        generalize dependent l1.
        induction l; intros.
        * inversion H. assert (@length T [] = length (l1 ++ [t])) by congruence.
          rewrite app_length in *; simpl in *; omega.
        * inversion H; subst.
         -- destruct l1. apply list_subset_nil.
            inversion H3; subst.
            apply SubsetIn. eauto.
         -- apply SubsetNotIn. eauto.
      + unfold cuttail. simpl. rewrite <- minus_n_O.
        induction l0 using rev_ind; simpl; auto.
        rewrite app_length; simpl.
        replace (length l0 + 1) with (S (length l0)) by omega.
        rewrite selN_last by auto.
        replace (t0 :: l0 ++ [x]) with ((t0 :: l0) ++ [x]) by reflexivity.
        rewrite firstn_app2 by (simpl; auto).
        auto.
  Qed.
  Proof.
    induction n; simpl; intros.
    rewrite popn_0; auto.
    replace (S n) with (1 + n) by omega.
    rewrite <- popn_popn.
    apply IHn.
    eapply nelist_subset_popn1'; eauto.
  Qed.
  Proof.
    intros; unfold pushd; simpl; auto.
  Qed.
  Proof.
    induction dlist.
    reflexivity.
    simpl.
    intros.
    rewrite IHdlist.
    rewrite pushd_length.
    omega.
  Qed.
  Proof.
    unfold nthd, pushd; intros.
    destruct (Nat.eq_dec n 0).

    subst; simpl.
    f_equal; omega.

    replace (snd (_)) with ([d] ++ l) by auto.
    rewrite selN_app2; simpl.
    destruct n; intuition.
    f_equal; omega.
    destruct n; intuition.
  Qed.
  Proof.
    destruct ds; intros.
    apply nthd_pushd; auto.
  Qed.
  Proof.
    unfold nthd, pushd; intros.
    simpl; subst.
    rewrite minus_diag; auto.
  Qed.
  Proof.
    destruct ds; intros.
    apply nthd_pushd_latest; eauto.
  Qed.
  Proof.
    unfold popn; simpl; intros.
    rewrite nthd_pushd' by auto.
    rewrite cuttail_cons; auto.
  Qed.
  Proof.
    induction 1; intros; simpl.

    exists 0.
    rewrite nthd_0; eauto.

    simpl in *.
    inversion H0; subst.
    exists (S (length (snd ds))); intuition.
    setoid_rewrite nthd_pushd_latest; eauto.

    destruct (lt_dec n' (length (snd (pushd d ds'))));
    destruct ds, ds'.
    rewrite nthd_pushd in H1.
    apply IHNEListSubset in H1.
    inversion H1.
    exists x; intuition.
    rewrite nthd_pushd; auto.
    rewrite pushd_length in l; omega.
    rewrite pushd_length in l; simpl in *; omega.

    rewrite nthd_pushd_latest in H1; subst.
    exists (S (length l)); intuition.
    rewrite nthd_pushd_latest; auto.
    replace l0 with (snd (t0, l0)) by auto.
    rewrite <- pushd_length with (d:=d).
    omega.

    apply IHNEListSubset in H1; auto.
    inversion H1.
    intuition.
    exists x; intuition.
    setoid_rewrite nthd_pushd; auto.
  Qed.
Proof.
  unfold latest, d_map; intros.
  destruct ds, l; simpl; auto.
Qed.
Proof.
  unfold d_map; intros; auto.
Qed.
Proof.
  unfold d_map; intros; simpl.
  destruct n.
  repeat rewrite nthd_0; auto.
  unfold nthd; destruct (lt_dec n (length (snd ds))); simpl.
  erewrite selN_map, map_length; auto.
  rewrite map_length; omega.
  rewrite map_length.
  replace (length (snd ds) - S n) with 0 by omega.
  destruct ds, l; simpl; auto.
Qed.
Proof.
  intros.
  apply d_in_In in H.
  replace (f (fst ds) :: map f (snd ds)) with (map f ((fst ds) :: (snd ds))) in H by reflexivity.
  apply in_map_iff in H.
  destruct H.
  eexists; intuition eauto.
  apply d_in_In'; eauto.
Qed.
Proof.
  intros; simpl.
  destruct ds; simpl.
  destruct n.
  unfold d_map; simpl.
  rewrite popn_0, nthd_0, cuttail_0; auto.
  unfold popn; simpl.
  rewrite d_map_nthd; unfold d_map; simpl.
  f_equal.
  unfold cuttail.
  rewrite firstn_map_comm, map_length; auto.
Qed.
Proof.
  firstorder; simpl.
  firstorder.
Qed.
Proof.
  destruct l; unfold NEforall; intuition.
  eapply Forall_impl; eauto.
Qed.
Proof.
  destruct l1; destruct l2; unfold NEforall2; intuition; simpl in *.
  apply forall2_forall in H2 as H2'.
  apply forall2_length in H2 as H2''.
  apply forall_forall2; eauto.
  eapply Forall_impl; eauto.
  intros; destruct a; eauto.
Qed.
Proof.
  unfold NEforall2.
  destruct l1, l2; simpl in *; intros.
  generalize dependent l0.
  induction l; intuition.
  - inversion H2; subst; simpl in *.
    edestruct H0; eauto.
    exists (x, nil); simpl; intuition.
  - inversion H2; subst; simpl in *.
    edestruct H0; try apply H4.
    edestruct IHl; eauto.
    exists (fst x0, x :: snd x0); simpl.
    intuition.
Qed.
Proof.
  intros.
  unfold NEforall2, d_map in *.
  simpl; split.
  specialize (H (fst l1) (fst l2) 0).
  apply H.
  rewrite nthd_0; eauto.
  rewrite nthd_0; eauto.
  intuition.
  intuition.
  assert (length (snd l1) = length (snd l2)).
  eapply forall2_length; eauto.
  eapply forall2_map2_selN with (q := q); auto; intros.
  destruct (lt_dec n (length (snd l1))).
  - eapply H with (n := (length (snd l1) - n)); unfold nthd; subst; eauto.
    replace (length (snd l1) - (length (snd l1) - n)) with n by omega; eauto.
    replace (length (snd l2) - (length (snd l1) - n)) with n by omega; eauto.
  - rewrite selN_oob in * by omega; subst.
    eapply H; auto.
    rewrite nthd_0; auto.
    rewrite nthd_0; auto.
Qed.
Proof.
  unfold NEforall, d_in.
  intuition.
  subst; eauto.
  eapply Forall_forall; eauto.
Qed.
Proof.
  intros. destruct l. unfold NEforall2, NEforall; simpl in *.
  split.
  specialize (H t).
  eapply H.
  unfold d_in; eauto.
  unfold d_in in H; simpl in *.
  eapply Forall_forall.
  eauto.
Qed.
Proof.
  unfold NEforall2; intuition.
  apply forall2_length in H1; auto.
Qed.
Proof.
  intros.
  rewrite H0.
  rewrite H1.
  unfold nthd.
  apply NEforall2_length in H as H'.
  destruct n.

  repeat rewrite selN_oob by omega.
  firstorder.

  case_eq (Datatypes.length (snd l1)); intros.
  repeat rewrite selN_oob by omega.
  firstorder.

  rewrite <- H'. rewrite H2.
  eapply forall2_selN.
  firstorder.
  omega.
Qed.
Proof.
  destruct l1; destruct l2; unfold NEforall2; intuition; simpl in *.
  unfold latest in *; simpl.
  inversion H1; subst; eauto.
Qed.
Proof.
  intros.
  unfold list2nelist, nelist2list.
  unfold singular.
  rewrite pushdlist_app.
  rewrite rev_involutive.
  rewrite app_nil_r.
  symmetry; apply surjective_pairing.
Qed.
Proof.
  intros.
  destruct l.
  destruct H; reflexivity.
  unfold list2nelist.
  unfold singular.
  rewrite pushdlist_app.
  rewrite rev_involutive.
  rewrite app_nil_r.
  unfold nelist2list; reflexivity.
Qed.