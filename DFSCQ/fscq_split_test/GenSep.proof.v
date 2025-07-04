Proof.
  intros.
  unfold list2mem in H.
  apply ptsto_valid' in H.
  destruct (lt_dec (wordToNat i) (length l)); auto.
  unfold sel in H. rewrite nth_selN_eq in H.
  rewrite nth_overflow in H by (rewrite map_length; omega); discriminate.
Qed.
Proof.
  unfold list2mem; intros.
  unfold sel; rewrite selN_oob; auto.
  rewrite map_length; auto.
Qed.
Proof.
  intros.
  destruct (lt_dec (wordToNat i) (length l)); auto; exfalso.
  apply not_lt in n.
  apply list2mem_oob in n.
  apply ptsto_valid' in H.
  rewrite H in n.
  inversion n.
Qed.
Proof.
  intros.
  assert (wordToNat i < length l).
  eapply list2mem_inbound; eauto.
  unfold list2mem in H.
  apply ptsto_valid' in H.
  erewrite sel_map in H by auto.
  inversion H; eauto.
Qed.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold list2mem, sel, upd, Mem.upd.
  autorewrite with core.

  destruct (weq x i).
  subst; erewrite selN_updN_eq; auto.
  rewrite map_length; auto.
  erewrite selN_updN_ne; auto.
  word2nat_simpl; omega.
Qed.
Proof.
  intros.
  rewrite listupd_memupd; auto.
  apply sep_star_comm.
  apply sep_star_comm in H.
  eapply ptsto_upd; eauto.
  eapply list2mem_inbound; eauto.
Qed.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold list2mem, sel, upd, Mem.upd.

  destruct (wlt_dec x $ (length l)).
  - apply wlt_lt in w.
    erewrite wordToNat_natToWord_bound in w; eauto.
    subst; rewrite selN_map with (default' := a).
    destruct (weq x $ (length l)); subst.
    + erewrite wordToNat_natToWord_bound in *; eauto.
      rewrite selN_last; auto.
    + rewrite selN_map with (default' := a); auto.
      rewrite selN_app; auto.
    + rewrite app_length; simpl; omega.
  - destruct (weq x $ (length l)).
    + subst; erewrite selN_map with (default' := a).
      rewrite selN_last; auto.
      eapply wordToNat_natToWord_bound; eauto.
      erewrite wordToNat_natToWord_bound; eauto.
      rewrite app_length; simpl; omega.
    + apply wle_le in n.
      erewrite wordToNat_natToWord_bound in n; eauto.
      repeat erewrite selN_oob with (def := None); try rewrite map_length; auto.
      rewrite app_length; simpl; intuition.
      rewrite Nat.add_1_r; apply lt_le_S.
      apply le_lt_or_eq in n; intuition.
      contradict n0; rewrite H0.
      apply wordToNat_inj.
      erewrite wordToNat_natToWord_bound; eauto.
Qed.
Proof.
  intros.
  erewrite listapp_memupd; eauto.
  apply ptsto_upd_disjoint; auto.
  unfold list2mem, sel.
  rewrite selN_oob; auto.
  rewrite map_length.
  erewrite wordToNat_natToWord_bound; eauto.
Qed.
Proof.
  intros; apply functional_extensionality; intros.
  destruct (wlt_dec x $ (length l - 1)); unfold list2mem, sel.
  - assert (wordToNat x < length l - 1); apply wlt_lt in w.
    erewrite wordToNat_natToWord_bound with (bound:=b) in w by omega; auto.
    rewrite selN_map with (default' := def).
    rewrite selN_removelast by omega; auto.
    rewrite length_removelast by auto; omega.
  - rewrite selN_oob; auto.
    rewrite map_length.
    rewrite length_removelast by auto.
    apply wle_le in n.
    rewrite wordToNat_natToWord_bound with (bound:=b) in n by omega; auto.
Qed.
Proof.
  intros; apply functional_extensionality; intros.
  assert (exists def, firstn 1 l = def :: nil) as Hdef.
  destruct l; try congruence.
  exists a; eauto.
  destruct Hdef as [def _].

  erewrite list2mem_removelast_is with (def := def) by eauto.
  unfold list2mem, sel.
  destruct (wlt_dec x $ (length l - 1));
  destruct (weq x $ (length l - 1)); subst; intuition.
  apply wlt_lt in w; omega.
  erewrite selN_map with (default' := def); auto.
  apply wlt_lt in w; rewrite wordToNat_natToWord_bound with (bound:=b) in w by omega; omega.
  erewrite selN_oob; auto.
  rewrite map_length.
  assert ($ (length l - 1) < x)%word.
  destruct (weq $ (length l - 1) x); intuition.
  apply wlt_lt in H1; rewrite wordToNat_natToWord_bound with (bound:=b) in H1 by omega; omega.
Qed.
Proof.
  unfold_sep_star; unfold ptsto; intuition; repeat deex.
  assert (m1 = list2mem (removelast l)); subst; auto.
  apply functional_extensionality; intros.
  rewrite list2mem_removelast_list2mem with (b:=b); auto.

  destruct (weq x $ (length l - 1)); subst.
  apply mem_disjoint_comm in H1. 
  eapply mem_disjoint_either; eauto.

  rewrite H2; unfold mem_union.
  destruct (m1 x); subst; simpl; auto.
  apply eq_sym; apply H6; auto.
Qed.
Proof.
  induction l using rev_ind; intros; firstorder; simpl.
  rewrite app_length in H; simpl in H.
  erewrite listapp_memupd with (b := b); try omega.
  eapply array_app_memupd with (b := b); try omega.
  apply IHl with (b := b); omega.
Qed.
Proof.
  unfold list2mem, list2mem_off, sel; intros.
  apply functional_extensionality; intros.
  rewrite <- minus_n_O.
  reflexivity.
Qed.
Proof.
  induction l; auto; simpl; intros.
  destruct (eq_nat_dec (wordToNat a0) start); [omega |].
  apply IHl; omega.
Qed.
Proof.
  induction l; intros; apply functional_extensionality; intros.
  unfold list2mem_off; destruct (lt_dec (wordToNat x) n); auto.

  unfold list2mem_off; simpl in *.

  destruct (lt_dec (wordToNat x) n).
  destruct (eq_nat_dec (wordToNat x) n); [omega |].
  rewrite list2mem_fix_below by omega.
  auto.

  destruct (eq_nat_dec (wordToNat x) n).
  rewrite e; replace (n-n) with (0) by omega; auto.

  assert (wordToNat x - n <> 0) by omega.
  destruct (wordToNat x - n) eqn:Hxn; try congruence.

  rewrite <- IHl with (b:=b) by omega.
  unfold list2mem_off.

  destruct (lt_dec (wordToNat x) (S n)); [omega |].
  f_equal; omega.
Qed.
Proof.
  intros.
  rewrite list2mem_off_eq.
  eapply list2mem_fix_off_eq.
  rewrite <- plus_n_O.
  eassumption.
Qed.
Proof.
  induction l; intros; subst; apply functional_extensionality; intros.
  unfold list2mem_off; destruct (lt_dec (wordToNat x) n); auto.

  unfold list2mem_off; simpl in *.

  destruct (lt_dec (wordToNat x) n).
  destruct (eq_nat_dec (wordToNat x) n); [omega |].
  rewrite list2mem_fix_below by omega.
  auto.

  destruct (eq_nat_dec (wordToNat x) n).
  rewrite e; replace (n-n) with (0) by omega; auto.

  assert (wordToNat x - n <> 0) by omega.
  destruct (wordToNat x - n) eqn:Hxn; try congruence.

  rewrite <- IHl with (sz:=addrlen) by omega.
  unfold list2mem_off.

  destruct (lt_dec (wordToNat x) (S n)); [omega |].
  f_equal; omega.
Qed.
Proof.
  intros; subst.
  rewrite list2mem_off_eq.
  eapply list2mem_fix_off_eq' with (sz:=addrlen); auto.
  rewrite <- plus_n_O.
  eassumption.
Qed.
Proof.
  destruct l; simpl; auto.
  unfold_sep_star; unfold ptsto, list2mem, sel; simpl; intros.
  repeat deex.
  unfold mem_union in H0.
  apply equal_f with ($ start) in H0.
  rewrite H2 in H0.
  congruence.
Qed.
Proof.
  destruct l; simpl; auto.
  unfold list2mem, sel, emp; intros.
  pose proof (H0 $ start).
  erewrite wordToNat_natToWord_bound in H1 by eauto.
  destruct (eq_nat_dec start start); simpl in *; congruence.
Qed.
Proof.
  induction l'; simpl; intros.
  - erewrite list2mem_nil_array; eauto.
  - destruct l.
    + eapply list2mem_array_nil with (start:=start) (b:=b).
      omega.
      auto.
    + simpl in *.
      unfold sep_star in H; rewrite sep_star_is in H; unfold sep_star_impl in H.
      repeat deex.
      unfold ptsto in H3; destruct H3.
      f_equal.
      * eapply equal_f with ($ start) in H2 as H2'.
        erewrite wordToNat_natToWord_bound with (bound:=b) in H2' by omega.

        unfold mem_union in H2'.
        rewrite H3 in H2'.
        destruct (eq_nat_dec start start); congruence.
      * apply IHl' with (b:=b) (start:=S start); eauto; try omega.
        replace ($ start ^+ $1) with (natToWord addrlen (S start)) in H5 by words.
        assert (m2 = list2mem_fix (S start) l'); subst; auto.

        apply functional_extensionality; intros.
        unfold mem_union in H2.
        apply equal_f with x in H2.
        destruct (eq_nat_dec (wordToNat x) start).

        rewrite list2mem_fix_below by omega.
        eapply mem_disjoint_either.
        eauto.
        rewrite <- e in H3.
        rewrite natToWord_wordToNat in *.
        eauto.

        rewrite H2.
        rewrite H4; auto.
        intro; apply n.
        rewrite <- H6.
        rewrite wordToNat_natToWord_bound with (bound:=b); auto.
        omega.
Qed.
Proof.
  intros; eapply list2mem_array_eq' with (start:=0); try rewrite <- plus_n_O; eauto.
  erewrite <- list2mem_fix_eq; eauto.
Qed.
Proof.
  intros.
  rewrite list2mem_array_eq with (l':=l') (l:=l++a::nil) (b:=b); eauto;
    [ | rewrite app_length; simpl; omega ].
  pred_apply.
  rewrite <- isolate_bwd with (vs:=l++a::nil) (i:=$ (length l)) by
    ( rewrite wordToNat_natToWord_bound with (bound:=b) by omega;
      rewrite app_length; simpl; omega ).
  unfold sel.
  erewrite wordToNat_natToWord_bound with (bound:=b) by omega.
  rewrite firstn_app2 by auto.
  replace (S (length l)) with (length (l ++ a :: nil)) by (rewrite app_length; simpl; omega).
  rewrite skipn_oob by omega; simpl.
  instantiate (y:=a).
  rewrite selN_last by auto.
  cancel.
Qed.
Proof.
  intros; unfold array_ex.
  erewrite array_isolate with (default := def); eauto.
  ring_simplify ($ (0) ^+ i ^* $ (1)).
  ring_simplify ($ (0) ^+ (i ^+ $ (1)) ^* $ (1)).
  unfold piff; split; cancel.
Qed.
Proof.
  intros; unfold array_ex.
  erewrite array_isolate_upd; eauto.
  ring_simplify ($ (0) ^+ i ^* $ (1)).
  ring_simplify ($ (0) ^+ (i ^+ $ (1)) ^* $ (1)).
  unfold piff; split; cancel.
Qed.
Proof.
  intros.
  eapply array_except; eauto.
  eapply list2mem_array; eauto.
Qed.
Proof.
  intros.
  eapply list2mem_array_eq with (b := b); autorewrite with core; auto.
  pred_apply.
  rewrite array_except_upd; auto.
Qed.
Proof.
  intros; apply eq_sym.
  replace (updN ol (wordToNat i) v) with (upd ol i v) by auto.
  eapply list2mem_array_upd; eauto.
Qed.
Proof.
  unfold array_ex; intros.
  destruct ol.
  inversion H2.

  eapply list2mem_array_eq with (l' := nl); eauto.
  pred_apply.
  erewrite wordToNat_natToWord_bound with (bound:=b) by omega.
  rewrite firstn_removelast_eq; auto.
  rewrite skipn_oob by omega.
  unfold array at 2.
  clear H; cancel.
  rewrite length_removelast.
  omega.
  contradict H2; rewrite H2.
  unfold length; omega.
Qed.
Proof.
  intros; pred_apply; cancel.
Qed.
Proof.
  induction a; intros; subst.
  - destruct b; auto; simpl in *.
    apply equal_f with (x:=$ off) in H2.
    destruct (eq_nat_dec off (pow2 addrlen)).
    subst; omega.
    erewrite wordToNat_natToWord_idempotent' in H2.
    destruct (eq_nat_dec off off); congruence.
    unfold goodSize. omega.
  - destruct (eq_nat_dec off (pow2 addrlen)). subst; simpl in *; omega.
    assert (off < pow2 addrlen) by omega.
    destruct b; simpl in *.
    replace (S (length a0 + off)) with (S (length a0) + off) in * by omega.
    + apply equal_f with (x:=$ off) in H2.
      erewrite wordToNat_natToWord_idempotent' in H2 by auto.
      destruct (eq_nat_dec off off); congruence.
    + apply equal_f with (x:=$ off) in H2 as H2'.
      erewrite wordToNat_natToWord_idempotent' in H2' by auto.
      destruct (eq_nat_dec off off); try congruence.
      inversion H2'. f_equal.
      eapply IHa with (off:=S off) (sz:=addrlen); try omega.
      apply functional_extensionality; intro x'.
      apply equal_f with (x:=x') in H2.
      destruct (eq_nat_dec (# x') off); auto.
      rewrite list2mem_fix_below by omega.
      rewrite list2mem_fix_below by omega.
      auto.
Qed.
Proof.
  unfold goodSizeEq; intros; subst.
  erewrite list2mem_fix_eq' in H1; eauto.
  erewrite list2mem_fix_eq' in H1; eauto.
  eapply list2mem_inj' with (sz:=addrlen); eauto; omega.
Qed.