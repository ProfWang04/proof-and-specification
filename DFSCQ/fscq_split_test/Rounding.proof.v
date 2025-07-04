  Proof.
    intros.
    destruct n.
    destruct a; cbv; auto.
    destruct a; try omega.
    eapply le_trans.
    apply div_le; auto.
    rewrite Nat.mul_comm.
    destruct (mult_O_le (S n) b); auto; omega.
  Qed.
  Proof.
    intros.
    erewrite Nat.div_mod with (x := a) (y := b) by omega.
    rewrite H, Nat.add_0_r.
    setoid_rewrite Nat.mul_comm at 2.
    rewrite Nat.div_mul by omega.
    setoid_rewrite Nat.mul_comm at 2; auto.
  Qed.
  Proof.
    intros. case_eq b; intros. auto.
    apply Nat.lt_le_incl, Nat.mod_upper_bound. omega.
  Qed.
  Proof.
    intros; omega.
  Qed.
  Proof.
    intros.
    apply lt_le_S in H0.
    apply mult_le_compat_r with ( p := b ) in H0; auto.
    rewrite Nat.add_comm, <- Nat.mul_succ_l.
    eapply le_trans; eauto.
    rewrite Nat.mul_comm.
    apply Nat.mul_div_le; omega.
  Qed.
  Proof.
    intros.
    apply lt_div_mul_add_le in H0; auto; omega.
  Qed.
  Proof.
    intros.
    apply lt_le_S in H0.
    apply mult_le_compat_r with ( p := b ) in H0; auto.
    eapply lt_le_trans; [ | eauto ].
    rewrite Nat.mul_comm.
    apply Nat.mul_succ_div_gt; omega.
  Qed.
  Proof.
    intros.
    rewrite Nat.mod_eq, mult_comm; auto.
  Qed.
  Proof.
    intros. intuition.
  Qed.
  Proof.
    intros.
    rewrite mult_comm.
    destruct (mult_O_le n m); solve [ omega | auto].
  Qed.
  Proof.
    intros. rewrite mult_comm. apply mul_ge_l; auto.
  Qed.
  Proof.
    intros.
    destruct (Nat.eq_dec b 0) as [H|H]; subst; try omega.
    pose proof Nat.div_mod a b H.
    rewrite mult_comm; omega.
  Qed.
  Proof.
    intros; omega.
  Qed.
  Proof.
    intros.
    rewrite <- sub_round_eq_mod at 1 by auto.
    rewrite sub_sub_assoc; auto.
    apply div_mul_le.
  Qed.
  Proof.
    unfold roundup, divup; intros.
    rewrite (Nat.div_mod x sz) at 1 by omega.
    rewrite <- Nat.add_sub_assoc by omega.
    rewrite <- plus_assoc.
    rewrite (mult_comm sz).
    rewrite Nat.div_add_l by omega.

    case_eq (x mod sz); intros.
    - rewrite (Nat.div_mod x sz) at 2 by omega.
       nia.

    - rewrite Nat.mul_add_distr_r.
      replace (S n + (sz - 1)) with (sz + n) by omega.
      replace (sz) with (1 * sz) at 3 by omega.
      rewrite Nat.div_add_l by omega.
      rewrite (Nat.div_mod x sz) at 2 by omega.
      assert (x mod sz < sz).
      apply Nat.mod_bound_pos; omega.
      nia.
  Qed.
  Proof.
    unfold roundup; intros.
    case_eq sz; intros; subst; auto.
    unfold ge.
    rewrite <- mult_1_l at 1.
    apply mult_le_compat; auto.
    unfold divup.
    apply Nat.div_str_pos; omega.
  Qed.
  Proof.
    intros.
    apply roundup_ge.
    rewrite valubytes_is; omega.
  Qed.
  Proof.
    intros.
    case_eq x; intros.
    reflexivity.
    apply Nat.div_small.
    omega.
  Qed.
  Proof.
    unfold roundup; intros.
    rewrite divup_0. auto.
  Qed.
  Proof.
    simpl; intros.
    replace (x + 1 - 1) with x by omega.
    pose proof (Nat.divmod_spec x 0 0 0 (Nat.le_refl 0)).
    destruct (Nat.divmod x 0 0 0); simpl.
    omega.
  Qed.
  Proof.
    unfold divup; intros.
    rewrite <- Nat.add_sub_assoc by ( rewrite valubytes_is; omega ).
    rewrite Nat.div_add_l by ( rewrite valubytes_is; omega ).
    rewrite Nat.mul_add_distr_r.
    replace ((valubytes - 1) / valubytes * valubytes) with 0. omega.
    rewrite valubytes_is.
    compute.
    auto.
  Qed.
  Proof.
    intros.
    case_eq sz; intros.
    (* sz = 0 *)
    simpl. omega.
    case_eq x; intros.
    (* x = 0 *)
    rewrite divup_0; constructor.
    unfold divup.
    (* sz > 0, x > 0 *)
    rewrite Nat.div_mod with (y := S n) by omega.
    rewrite <- H.
    rewrite <- H0.
    apply le_trans with (sz * x / sz).
    apply Nat.div_le_mono.
    omega.
    replace (sz) with (1 + (sz - 1)) at 2 by omega.
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.mul_1_l.
    replace (x + sz - 1) with (x + (sz - 1)).
    apply plus_le_compat_l.
    replace x with (n0 + 1) by omega.
    rewrite Nat.mul_add_distr_l.
    rewrite plus_comm.
    rewrite Nat.mul_1_r.
    apply le_plus_l.
    omega.
    rewrite mult_comm.
    rewrite Nat.div_mul by omega.
    apply Nat.eq_le_incl.
    apply Nat.div_mod.
    omega.
  Qed.
  Proof.
    intros.
    apply le_trans with (m := divup a b * b).
    apply roundup_ge; auto.
    apply Nat.mul_le_mono_pos_r; auto.
  Qed.
  Proof.
    intros.
    case_eq sz; intros.
    reflexivity.
    apply Nat.div_le_mono.
    auto.
    omega.
  Qed.
  Proof.
    intros.
    unfold roundup.
    apply Nat.mul_le_mono_nonneg_r.
    omega.
    apply divup_mono; assumption.
  Qed.
  Proof.
    intros.
    unfold divup, divup'.
    case_eq (x mod m); intros.
    assert (Hxm := Nat.div_mod x m H).
    rewrite H0 in Hxm.
    symmetry.
    apply Nat.div_unique with (m - 1).
    omega.
    omega.
    assert (Hxm := Nat.div_mod x m H).
    symmetry.
    apply Nat.div_unique with (r := x mod m - 1).
    apply lt_trans with (x mod m).
    omega.
    apply Nat.mod_upper_bound; assumption.
    replace (x + m - 1) with (x + (m - 1)) by omega.
    rewrite Hxm at 1.
    rewrite Nat.mul_add_distr_l.
    rewrite Nat.mul_1_r.
    assert (x mod m + (m - 1) = m + (x mod m - 1)).
    omega.
    omega.
  Qed.
  Proof.
    intros.
    case_eq m; intros.
    unfold divup, divup'.
    reflexivity.
    apply divup_eq_divup'_m_nonzero.
    omega.
  Qed.
  Proof.
    intros.
    rewrite divup_eq_divup'.
    unfold divup'.
    rewrite Nat.mod_mul by assumption.
    apply Nat.div_mul.
    assumption.
  Qed.
  Proof.
    intros.
    rewrite divup_eq_divup'. unfold divup'.
    destruct (a mod b); omega.
  Qed.
  Proof.
    intros.
    destruct sz.
    - simpl.
      omega.
    - unfold divup.
      apply Nat.div_le_mono.
      omega.
      omega.
  Qed.
  Proof.
    intros.
    rewrite divup_eq_divup'.
    unfold divup'.
    case_eq (n mod sz); intros.
    rewrite Nat.mul_lt_mono_pos_l with (p := sz) by omega.
    replace (sz * (n / sz)) with n.
    eapply le_lt_trans.
    apply Nat.mul_div_le.
    omega.
    assumption.
    apply Nat.div_exact; assumption.
    apply le_lt_trans with (n / sz).
    apply Nat.div_le_mono; omega.
    omega.
  Qed.
  Proof.
    intros.
    apply divup_mono; assumption.
  Qed.
  Proof.
    unfold roundup, divup; intros.
    apply Nat.mul_le_mono_r.
    apply le_divup; assumption.
  Qed.
  Proof.
    intros.
    omega.
  Qed.
  Proof.
    assert (addrlen > 1) by ( unfold addrlen ; omega ).
    generalize dependent addrlen.
    intros.
    unfold goodSize, divup.
    apply Nat.div_lt_upper_bound.
    rewrite valubytes_is; simpl valubytes_real; auto.
    apply lt_minus'.
    unfold addrlen.
    rewrite valubytes_is; simpl valubytes_real.
    replace (4096) with (pow2 12) by reflexivity.
    rewrite <- pow2_add_mul.
    replace (pow2 (12 + n)) with (pow2 (11 + n) + pow2 (11 + n)).
    apply plus_lt_compat.
    eapply lt_trans.
    apply natToWord_goodSize.
    apply pow2_inc; omega.
    apply pow2_inc; omega.
    replace (12 + n) with ((11 + n) + 1) by omega.
    rewrite (pow2_add_mul (11+n) 1).
    simpl (pow2 1).
    omega.
  Qed.
  Proof.
    unfold divup; intros; simpl.
    replace (n - sz + sz) with n by lia.
    replace (n + sz - 1) with (n - 1 + 1 * sz) by lia.
    rewrite Nat.div_add by auto.
    omega.
  Qed.
  Proof.
    induction i; intros; simpl.
    repeat rewrite Nat.sub_0_r; auto.
    replace (n - (sz + i * sz)) with ((n - sz) - (i * sz)) by nia.
    rewrite IHi by nia.
    rewrite divup_sub_1; nia.
  Qed.
  Proof.
    intros.
    pose proof (Nat.mod_upper_bound a b H).
    omega.
  Qed.
  Proof.
    intros; destruct (Nat.eq_dec b 0); subst.
    rewrite Nat.mul_0_r; rewrite divup_0; omega.
    rewrite divup_mul; omega.
  Qed.
  Proof.
    intros; rewrite Nat.mul_comm; apply divup_mul_l.
  Qed.
  Proof.
    intros.
    eapply le_trans.
    apply divup_mono; eauto.
    rewrite divup_mul_r; auto.
  Qed.
  Proof.
    intros; apply divup_le; omega.
  Qed.
  Proof.
    intros; unfold divup.
    replace (a + b - 1) with (a - 1 + 1 * b) by omega.
    rewrite Nat.div_add by auto.
    nia.
  Qed.
  Proof.
    intros.
    assert (divup c n <= 1) by (apply divup_le_1; omega).
    assert (c - 1 < n) by omega.
    assert ((c - 1) / n < divup c n) by (apply div_lt_divup; omega).
    assert ((c - 1) / n = 0) as HH by (apply Nat.div_small; auto); rewrite HH in *.
    omega.
  Qed.
  Proof.
    intros.
    eapply le_trans.
    2: apply divup_mono; eauto.
    rewrite Nat.mul_comm.
    rewrite divup_mul; auto.
  Qed.
  Proof.
    intros.
    apply Nat.div_str_pos; omega.
  Qed.
  Proof.
    intros.
    destruct (Nat.eq_dec b 0); subst; simpl; auto.
    rewrite Nat.div_small; auto.
    apply Nat.mod_bound_pos; omega.
  Qed.
  Proof.
    intros.
    destruct (Nat.eq_dec c 0); subst; simpl; auto.
    rewrite Nat.div_mod with (x := a) (y := c) by auto.
    rewrite Nat.div_mod with (x := b) (y := c) by auto.
    replace (c * (a / c) + a mod c + (c * (b / c) + b mod c)) with
            (((a mod c + b mod c) + (b / c) * c) + (a / c) * c) by nia.
    repeat rewrite Nat.div_add by auto.
    setoid_rewrite Nat.add_comm at 2 3.
    setoid_rewrite Nat.mul_comm.
    repeat rewrite Nat.div_add by auto.
    repeat rewrite mod_div_0.
    repeat rewrite Nat.add_0_l.
    omega.
  Qed.
  Proof.
    induction i; intros; simpl.
    rewrite Nat.add_0_r; rewrite Nat.mul_0_r; auto.
    replace (n + (sz * S i)) with ((n + sz) + (sz * i)) by nia.
    rewrite IHi by nia.
    unfold divup.
    replace (n + sz + sz - 1) with (n - 1 + 2 * sz) by nia.
    replace (n + sz - 1) with (n - 1 + 1 * sz) by nia.
    repeat rewrite Nat.div_add by auto.
    omega.
  Qed.
  Proof.
    intros.
    destruct (Nat.eq_dec n 0); subst.
    rewrite divup_0; rewrite Nat.add_0_l; rewrite Nat.mul_comm.
    rewrite divup_mul; omega.
    apply divup_add'; auto.
  Qed.
  Proof.
    intros.
    destruct (addr_eq_dec a 0); subst; try lia.
    eapply (Nat.div_mod a) in H as HH.
    rewrite HH.
    rewrite plus_comm.
    rewrite divup_add by omega.
    rewrite Nat.mul_add_distr_r.
    destruct (addr_eq_dec (a mod n) 0) as [H'|H'].
    rewrite H'.
    rewrite mul_div; lia.
    rewrite divup_small.
    simpl. rewrite plus_0_r.
    pose proof Nat.mod_upper_bound a n H.
    rewrite mult_comm; omega.
    split. omega.
    apply Nat.lt_le_incl. apply Nat.mod_upper_bound.
    omega.
  Qed.
  Proof.
    intros; omega.
  Qed.
  Proof.
    intros; omega.
  Qed.
  Proof.
    intros. omega.
  Qed.
  Proof.
    intros.
    rewrite Nat.div_mod with (x := a) (y := b) by auto.
    setoid_rewrite Nat.mul_comm at 2.
    repeat rewrite Nat.div_add_l by omega.
    rewrite Nat.div_small with (a := (a mod b)).
    rewrite Nat.add_0_r, Nat.mul_comm.
    omega.
    apply Nat.mod_upper_bound; omega.
  Qed.
  Proof.
    intros.
    unfold Nat.divide in *.
    destruct H0; subst.
    destruct (addr_eq_dec x 0) as [|Hx]; subst; try omega.
    destruct (addr_eq_dec n 0) as [|Hn]; subst.
    repeat rewrite roundup_0; auto.
    destruct (addr_eq_dec a 0) as [|Ha]; subst; [> rewrite mult_comm; auto |].
    unfold roundup.
    rewrite mult_assoc.
    apply mult_le_compat_r.
    unfold divup.
    replace (n + a - 1) with ((1 * a) + (n - 1)) by omega.
    replace (n + x * a - 1) with (1 * (x * a) + (n - 1)) by lia.
    repeat rewrite Nat.div_add_l by auto.
    replace (x * a) with (a * x) by (apply mult_comm).
    rewrite <- Nat.div_div by auto.
    remember ((n - 1) / a) as r.
    apply Nat.div_mod with (x := r) in Hx as Hr.
    rewrite plus_comm in Hr.
    rewrite Hr at 1.
    rewrite plus_assoc, mult_comm.
    apply plus_le_compat_r.
    eapply lt_le_trans; [> apply Nat.mod_upper_bound | ]; auto.
  Qed.
  Proof.
    intros.
    edestruct Min.min_spec as [ [HH Hmin]|[HH Hmin] ]; rewrite Hmin in *;
    symmetry; (apply min_l || apply min_r);
    apply roundup_mono; omega.
  Qed.
  Proof.
    unfold roundup; intros.
    destruct (Nat.eq_dec a 0); subst; simpl; auto.
    replace (a * b) with (b * a) by apply mult_comm.
    destruct (Nat.eq_dec b 0); subst; simpl.
    rewrite divup_0; auto.
    rewrite divup_mul; auto.
  Qed.
  Proof.
    unfold roundup; intros.
    divup_cases.
    replace (n / sz * sz) with n; try omega.
    rewrite Nat.mul_comm.
    rewrite Nat.div_exact; omega.
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l.

    apply helper_add_sub_lt; auto.
    apply div_mul_lt; omega.
  Qed.
  Proof.
    intros.
    destruct H0 as [x H0].
    destruct (Nat.eq_dec c 0); subst; unfold roundup; auto.
    rewrite divup_sub; auto.
    rewrite Nat.mul_sub_distr_r; auto.
    unfold roundup in *.
    rewrite <- Nat.mul_lt_mono_pos_r in H by omega.
    unfold ge.
    unfold divup in *.
    apply lt_div_mul_add_le in H; omega.
  Qed.
  Proof.
    unfold roundup, divup; intros.
    replace (m + n + k - 1) with ((m + k - 1) + n) by omega.
    rewrite Nat.div_mod with (x := (m + k -1)) (y := k) by omega.
    rewrite Nat.mul_comm.
    rewrite <- Nat.add_assoc.
    repeat rewrite Nat.div_add_l by omega.
    f_equal.
    repeat rewrite Nat.div_small; auto.
    apply Nat.mod_upper_bound; omega.

    eapply add_lt_upper_bound; eauto.
    rewrite Nat.mod_eq by omega.
    rewrite Nat.mul_comm.

    destruct (le_gt_dec (m + k - 1) ((m + k - 1) / k * k)).
    replace (m + k - 1 - (m + k - 1) / k * k ) with 0 by omega.
    rewrite Nat.add_0_l.

    apply roundup_sub_lt; auto.
    rewrite helper_sub_add_cancel; try omega.
    apply roundup_ge; auto.
  Qed.
  Proof.
    unfold divup; intros.
    rewrite <- Nat.add_sub_assoc by omega.
    rewrite Nat.div_add_l by omega.
    replace ((sz - 1) / sz) with 0. omega.
    rewrite Nat.div_small; omega.
  Qed.
  Proof.
    unfold roundup; intros.
    rewrite divup_divup; auto.
  Qed.
  Proof.
    unfold roundup; intros.
    rewrite Nat.add_comm.
    setoid_rewrite Nat.mul_comm at 2.
    rewrite divup_add by omega.
    lia.
  Qed.
  Proof.
    intros; erewrite <- divup_mul; eauto.
    rewrite Nat.mul_1_l; auto.
  Qed.
  Proof.
    intros a b sz H.
    divup_cases.
    eapply Nat.mul_lt_mono_pos_r in H1; eauto.
    replace (a / sz * sz) with a in H1; auto.
    rewrite Nat.mul_comm.
    apply Nat.div_exact; omega.

    destruct b.
    destruct (Nat.eq_dec a 0); subst.
    contradict H0.
    rewrite Nat.mod_0_l; omega.
    omega.

    rewrite Nat.add_1_r in H1.
    apply lt_n_Sm_le in H1.
    eapply Nat.mul_le_mono_pos_r in H1; eauto.
    replace (a / sz * sz) with (a - a mod sz) in H1.
    rewrite H0 in H1.
    eapply Nat.le_lt_trans; eauto.
    destruct (Nat.eq_dec a 0); subst.
    contradict H0.
    rewrite Nat.mod_0_l; omega.
    omega.

    rewrite Nat.mod_eq by omega.
    setoid_rewrite Nat.mul_comm at 2.
    apply sub_sub_assoc.
    apply Nat.mul_div_le; omega.
  Qed.
  Proof.
    intros.
    unfold divup, divup_S.
    divup_cases;
    replace (S x + sz - 1) with (x + 1 * sz) by omega;
    rewrite Nat.div_add; auto.
  Qed.
  Proof.
    induction a; intros; auto.
    rewrite Nat.add_0_l in H0.
    rewrite Nat.add_0_l.
    apply divup_gt; auto.

    replace (S a * sz + b) with (a * sz + (b + sz * 1)).
    apply IHa; auto.
    rewrite divup_add; omega.
    rewrite Nat.mul_1_r.
    rewrite Nat.mul_succ_l.
    omega.
  Qed.
  Proof.
    intros.
    apply (roundup_mono _ _ sz) in H0.
    eapply le_trans; eauto.
    unfold roundup.
    apply Nat.mul_le_mono_pos_r; auto.
    apply divup_mul_l.
  Qed.
  Proof.
    destruct sz; intros.
    unfold roundup.
    repeat rewrite Nat.mul_0_r; auto.
    apply roundup_le'; auto; omega.
  Qed.
  Proof.
    intros.
    apply Nat.min_r.
    apply roundup_ge; auto.
  Qed.
  Proof.
    intros.
    divup_cases; omega.
  Qed.
  Proof.
    intros.
    unfold roundup.
    rewrite divup_eq_div_plus_1 by auto.
    rewrite Nat.mul_add_distr_r. rewrite mult_1_l.
    rewrite Nat.div_mod with (x := a) (y := b) at 1 by auto.
    rewrite mult_comm.
    assert (a mod b < b) by (apply Nat.mod_upper_bound; auto). omega.
  Qed.
  Proof.
    intros.
    unfold roundup.
    rewrite divup_eq_divup'. unfold divup'.
    destruct (a mod n) as [|n'] eqn:HH; intuition.
    replace (S n') with (a mod n) by omega.
    rewrite Nat.div_mod with (x := a) (y := n) at 2 by auto.
    rewrite <- plus_assoc.
    rewrite <- le_plus_minus by (apply mod_le_r).
    rewrite Nat.mul_add_distr_r. rewrite mult_comm. omega.
  Qed.