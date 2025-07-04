Proof.
 intros; subst; firstorder.
Qed.
Proof.
 intros; subst; firstorder.
Qed.
Proof.
  induction i; destruct n; try now firstorder.
  intros. eapply IHi. omega.
Qed.
Proof.
  induction i; destruct n; firstorder; inversion H.
Qed.
Proof.
  induction i; destruct l; intros; inversion H; firstorder.
Qed.
Proof.
  induction i; destruct l; simpl; intros; try omega; auto.
  apply IHi; auto; omega.
Qed.
Proof.
  induction i; destruct l; simpl; intros; inversion H; try omega.
  specialize (IHi _ _ H); omega.
Qed.
Proof.
  induction i; simpl; intros; auto.
  f_equal; eauto.
Qed.
Proof.
  intros.
  induction n; simpl.
  reflexivity.
  rewrite IHn.
  reflexivity.
Qed.
Proof.
  induction l; auto; intros.
  simpl.
  inversion H; subst.
  rewrite <- repeat_app.
  f_equal; auto.
Qed.
Proof.
  induction l; firstorder.
  inversion H.
Qed.
Proof.
  intros; apply eq_sym.
  apply length_nil; auto.
Qed.
Proof.
  unfold eqlen; simpl; intros.
  apply length_nil; auto.
Qed.
Proof.
  intros; auto.
Qed.
Proof.
  induction n; intros; destruct l; simpl; auto.
Qed.
Proof.
  induction vs; destruct n; simpl; intuition.
Qed.
Proof.
  induction vs; destruct n; simpl; intuition; omega.
Qed.
Proof.
  induction vs; simpl; intros; try omega.
  destruct n; auto.
  eapply IHvs.
  omega.
Qed.
Proof.
  induction vs; destruct n; simpl; intuition; omega.
Qed.
Proof.
  induction vs; destruct n; destruct n'; simpl; intuition.
Qed.
Proof.
  induction l; destruct i; simpl; firstorder.
  f_equal; auto.
  erewrite IHl; eauto.
Qed.
Proof.
  induction i; intros.
  - destruct n. omega.
    destruct l; simpl in *; inversion H0. auto.
  - destruct n. omega.
    destruct l; simpl in *; inversion H0.
    eapply IHi; [> | eauto]. omega.
Qed.
Proof.
  induction l; destruct n; simpl; firstorder.
Qed.
Proof.
  induction l; destruct n; simpl; firstorder.
Qed.
Proof.
  induction l; destruct n; simpl; firstorder.
Qed.
Proof.
  intros.
  constructor.
  reflexivity.
Qed.
Proof.
  intros.
  induction l1; simpl; auto.
Qed.
Proof.
  induction vs; destruct i, j; simpl; intuition.
  omega.
  rewrite IHvs; auto; omega.
Qed.
Proof.
  induction vs; destruct i, j; simpl; intuition.
  rewrite IHvs by omega.
  reflexivity.
Qed.
Proof.
  intros until m.
  induction m; intros; simpl; auto.
  destruct l.
  destruct n; auto.
  apply IHm.
Qed.
Proof.
  intros.
  rewrite Nat.add_comm.
  apply skipn_skipn'.
Qed.
Proof.
  induction i; intros; auto.
  destruct vs; simpl; auto.
Qed.
Proof.
  induction n; intros.
  rewrite plus_0_r, Nat.sub_0_r; auto.
  destruct b; auto.
  simpl.
  rewrite IHn.
  f_equal; omega.
Qed.
Proof.
  induction vs; destruct i, j; simpl; intuition; omega.
Qed.
Proof.
  destruct vs, j; simpl; eauto using skipN_updN'.
Qed.
Proof.
  induction off; simpl; intros.
  destruct l; simpl in *; try omega; auto.
  destruct l; simpl in *; try omega.
  apply IHoff.
  omega.
Qed.
Proof.
  intros.
  replace (length l - n) with (S (length l - n - 1)) at 2 by omega.
  rewrite <- skipn_selN_skipn by omega.
  f_equal; omega.
Qed.
Proof.
  induction l; simpl; intros; auto.
  destruct a0; auto; simpl.
  rewrite IHl; auto.
Qed.
Proof.
  induction l; simpl; intros; auto.
  destruct a0; destruct a1; simpl in *; try congruence.
  rewrite IHl by omega. auto.
Qed.
Proof.
  intros.
  generalize dependent n.
  induction l; intros; simpl.
  inversion H.
  induction n; simpl.
  reflexivity.
  f_equal.
  apply IHl.
  simpl in H.
  omega.
Qed.
Proof.
  induction len; intros; destruct a; destruct b; simpl in *; try congruence.
  f_equal.
  apply (H1 0).
  omega.
  eapply IHlen; [ omega | omega | ].
  intros.
  apply (H1 (S pos)).
  omega.
Qed.
Proof.
  intros. apply list_selN_ext' with (len:=length a) (default:=default); auto.
Qed.
Proof.
  nth_selN nth_In.
Qed.
Proof.
  induction l; try easy; intros.
  inversion H; subst.
  exists 0; simpl; split; auto; omega.
  destruct (IHl a0 def H0).
  destruct H1.
  exists (S x); simpl; split; auto; omega.
Qed.
Proof.
  induction l; cbn; intros.
  auto.
  destruct a, split.
  destruct i; cbn; auto.
Qed.
Proof.
  induction l; cbn; intros.
  auto.
  destruct a, split.
  destruct i; cbn; auto.
Qed.
Proof.
  induction l; cbn; auto.
  destruct a; cbn.
  destruct split eqn:?; cbn in *.
  congruence.
Qed.
Proof.
  induction l; cbn; auto.
  destruct a; cbn.
  destruct split eqn:?; cbn in *.
  congruence.
Qed.
Proof.
  induction n; intros; destruct l; intuition; simpl in *; destruct H; auto.
  destruct (IHn l x xn H); auto.
Qed.
Proof.
  intros.
  rewrite Forall_forall.
  rewrite Forall_forall in H.
  intros.
  apply in_app_or in H1.
  destruct H1.
  apply H; auto.
  simpl in H1.
  destruct H1.
  subst; auto.
  exfalso; auto.
Qed.
Proof.
  induction a; destruct b; cbn in *; try congruence; intros.
  split; constructor.
  split; intros H'; inversion H'; constructor; subst.
  eapply H0 in H3; auto.
  eapply IHa; auto.
  eapply H0; auto.
  apply IHa; auto.
Qed.
Proof.
  intros.
  rewrite Forall_forall in *.
  intros.
  apply in_app_or in H1.
  destruct H1.
  apply H; assumption.
  apply H0; assumption.
Qed.
Proof.
  intros; rewrite Forall_forall in *; firstorder.
  eauto using in_or_app.
Qed.
Proof.
  intros; rewrite Forall_forall in *; firstorder.
  eauto using in_or_app.
Qed.
Proof.
  intros.
  rewrite Forall_forall.
  intros.
  apply repeat_spec in H0.
  congruence.
Qed.
Proof.
  induction l; intros; auto.
  inversion H; subst; auto.
  simpl; destruct i; apply Forall_cons; auto.
Qed.
Proof.
  intros.
  rewrite Forall_forall in *; intros.
  apply H.
  apply in_cons; auto.
Qed.
Proof.
  induction l; simpl; intros.
  - constructor.
  - inversion H; subst.
    constructor; auto.
Qed.
Proof.
  intros.
  erewrite concat_hom_repeat.
  autorewrite with lists.
  eauto.
  apply Forall_repeat; auto.
Qed.
Proof.
  induction n; small_t.
  destruct l; small_t.
  intros; apply IHn.
  eapply Forall_cons2; eauto.
Qed.
Proof.
  induction n; simpl; auto; intros.
  destruct l; auto.
  inversion H; subst.
  apply Forall_cons; auto.
Qed.
Proof.
  induction l; auto.
  intros. destruct ix. auto. simpl. rewrite IHl. trivial.
Qed.
Proof.
  (* copied from proof of app_nth1 *)
  induction l.
  intros.
  inversion H.
  intros l' d n.
  case n; simpl; auto.
  intros; rewrite IHl; auto with arith.
Qed.
Proof.
  (* copied from proof of app_nth2 *)
  induction l.
  intros.
  simpl.
  rewrite <- minus_n_O; auto.
  intros l' d n.
  case n; simpl; auto.
  intros.
  inversion H.
  intros.
  rewrite IHl; auto with arith.
Qed.
Proof.
  induction l; simpl; firstorder.
  rewrite IHl; auto.
Qed.
Proof.
  (* XXX this is almost exactly the same as selN_concat *)
  induction a; intros; destruct l; simpl; inversion H0.
  trivial.
  replace (b + 0) with b by omega. subst.
  rewrite updN_app1; auto.
  trivial.
  subst. remember (a * length l) as al. rewrite updN_app2 by omega.
  replace (b + (length l + al) - length l) with (b + al) by omega. subst.
  rewrite IHa; auto.
Qed.
Proof.
  nth_selN app_nth1.
Qed.
Proof.
  nth_selN app_nth2.
Qed.
Proof.
  intros.
  replace (a :: l) with ([a] ++ l) by (simpl; auto).
  rewrite selN_app2; simpl; auto.
Qed.
Proof.
  induction b; simpl; intros.
  replace (a + 0) with (a) by omega; reflexivity.
  f_equal.
  replace (a + S b) with (S a + b) by omega.
  rewrite <- IHb.
  auto.
Qed.
Proof.
  intros; rewrite seq_right; f_equal.
Qed.
Proof.
  induction l; simpl; intros.
  - congruence.
  - destruct idx; try omega.
    apply IHl in H; omega.
Qed.
Proof.
  induction vs; auto; destruct i; simpl; f_equal; auto.
Qed.
Proof.
  induction i; destruct n; simpl; intros; try omega; auto.
  replace (S (i + base)) with (i + (S base)) by omega.
  apply IHi; omega.
Qed.
Proof.
  intros.
  replace i with (i + 0) at 2 by omega.
  apply selN_map_seq'; auto.
Qed.
Proof.
  induction l; intros; subst; cbn in *.
  auto.
  f_equal.
  rewrite <- seq_shift.
  rewrite map_map. auto.
Qed.
Proof.
  induction l; simpl; intros; try omega.
  destruct i; auto.
  apply IHl; omega.
Qed.
Proof.
  induction l; destruct i; simpl; try now firstorder.
  left; destruct a; auto.
  intros. right. eapply IHl. omega.
Qed.
Proof.
  induction len; auto; simpl; intros.
  f_equal; auto.
Qed.
Proof.
  induction len; intros; try omega.
  simpl; destruct pos; auto.
  rewrite IHlen by omega.
  auto.
Qed.
Proof.
  induction len; intros; try omega.
  simpl seq; simpl map.
  destruct pos.
  - replace (start + 0) with (start) by omega; simpl.
    f_equal.
    + destruct (eq_nat_dec start start); congruence.
    + apply map_ext_in; intros.
      destruct (eq_nat_dec a start); auto.
      apply in_seq in H0; omega.
  - simpl; f_equal.
    destruct (eq_nat_dec start (start + S pos)); auto; omega.
    rewrite IHlen by omega.
    replace (S start + pos) with (start + S pos) by omega.
    auto.
Qed.
Proof.
  induction a; auto.
Qed.
Proof.
  induction n; simpl; intros; auto.
  destruct a; simpl; auto.
  destruct b; simpl; auto.
  f_equal.
  auto.
Qed.
Proof.
  induction n.
  - simpl; intros.
    destruct a; simpl; auto.
    destruct b; simpl; auto.
    autorewrite with lists; auto.
  - intros.
    destruct a; [simpl; auto|].
    destruct b; [simpl; auto|].
    autorewrite with lists; auto.
    replace (skipn (S (S n)) (t :: a)) with (skipn (S n) a) by auto.
    replace (skipn (S (S n)) (r :: b)) with (skipn (S n) b) by auto.
    rewrite <- IHn.
    simpl; auto.
Qed.
Proof.
  intros. apply skipn_combine_comm.
Qed.
Proof.
  induction n; intros.
  simpl; auto.
  rewrite skipn_combine_comm'; auto.
Qed.
Proof.
  unfold selN; induction l; destruct n; intros;
  firstorder; inversion H.
Qed.
Proof.
  induction l; destruct i, n; intros; try omega; auto.
  apply IHl; omega.
Qed.
Proof.
  induction n; destruct l; simpl; try now firstorder.
  eauto with arith.
Qed.
Proof.
  induction l; destruct n; intros; simpl; try now firstorder.
  eauto with arith.
Qed.
Proof.
  induction n; destruct l; simpl; try now firstorder.
  eauto with arith.
Qed.
Proof.
  induction n; destruct l1; intros; inversion H; auto; subst.
  unfold firstn; simpl.
  rewrite IHn; auto.
Qed.
Proof.
  unfold skipn; induction n; destruct l; intros; auto.
  inversion H.
  apply IHn; firstorder. eauto with arith.
Qed.
Proof.
  unfold updN; induction l; destruct i; intros; auto.
  inversion H.
  rewrite IHl; firstorder. eauto with arith.
Qed.
Proof.
  unfold firstn; induction l; destruct n; intros; try now firstorder.
  rewrite IHl; firstorder. eauto with arith.
Qed.
Proof.
  intros; rewrite firstn_oob; auto.
Qed.
Proof.
  induction l; destruct n1, n2; simpl; auto.
  rewrite IHl; auto.
Qed.
Proof. induction l as [| ? ? H]; simpl; [reflexivity | now rewrite H]. Qed.

Proof.
  induction n; destruct l; intros; simpl in *; try now firstorder.
  rewrite IHn with (def:=def) by omega; auto.
Qed.
Proof.
  intros.
  rewrite H.
  apply firstn_plusone_selN; auto.
Qed.
Proof.
  intros.
  replace (S n) with (n + 1) by omega.
  apply firstn_plusone_selN; auto.
Qed.
Proof.
  intros.
  rewrite <- firstn_S_selN by auto.
  simpl; auto.
Qed.
Proof.
  induction l; destruct n; destruct i; intros; simpl; auto.
  inversion H.
  rewrite IHl by omega; auto.
Qed.
Proof.
  intros.
  rewrite firstn_plusone_selN with (def := x).
  rewrite selN_updN_eq by omega.
  rewrite firstn_updN_oob; auto.
  rewrite length_updN; auto.
Qed.
Proof.
  split; induction l; simpl; try now firstorder.
  eauto with arith.
Qed.
Proof.
  split; intros.
  apply length_not_nil in H; omega.
  apply length_not_nil; omega.
Qed.
Proof.
  induction n; destruct l; firstorder.
  inversion H.
  simpl in H0; inversion H0.
Qed.
Proof.
  intros.
  replace n with (S (n - 1)) by omega.
  replace (S (n - 1) - 1) with (n - 1) by omega.
  apply removelast_firstn; omega.
Qed.
Proof.
  induction n; firstorder.
Qed.
Proof.
  induction n; intros.
  simpl; auto.
  simpl; f_equal.
Qed.
Proof.
  intros.
  rewrite firstn_length.
  rewrite Nat.min_l; auto.
Qed.
Proof.
  intros.
  split.
  - intros.
    apply firstn_length_l; auto.
  - intros.
    rewrite firstn_length in H.
    apply Nat.min_l_iff; auto.
Qed.
Proof.
  intros.
  rewrite firstn_length.
  rewrite Nat.min_r; auto.
Qed.
Proof.
  induction n; destruct l; intros; firstorder.
Qed.
Proof.
  induction n; firstorder.
Qed.
Proof.
  induction n; firstorder.
Qed.
Proof.
  intros.
  rewrite app_assoc_reverse.
  simpl; auto.
Qed.
Proof.
  induction i; firstorder.
  rewrite firstn_app2 by omega.
  simpl; rewrite app_nil_r; auto.

  destruct b.
  simpl; rewrite app_nil_r.
  rewrite firstn_oob; auto; omega.
  rewrite firstn_cons.
  replace (length a + S i) with (length (a ++ (t :: nil)) + i).
  replace (a ++ t :: b) with ((a ++ (t :: nil)) ++ b) by auto.
  rewrite IHi; auto.
  rewrite app_length; simpl; omega.
Qed.
Proof.
  induction a; intros; simpl in *.
  inversion H. auto.
  destruct n; simpl in *; auto.
  rewrite IHa by omega; auto.
Qed.
Proof.
  induction a; firstorder.
Qed.
Proof.
  intros.
  rewrite <- H.
  apply skipn_app.
Qed.
Proof.
  induction i; firstorder.
  replace (length a + 0) with (length a) by omega.
  rewrite skipn_app; simpl; auto.

  destruct a; destruct b; simpl; firstorder.
  rewrite app_nil_r.
  rewrite skipn_oob; auto; omega.
  rewrite <- IHi with (a := a ++ (t0 :: nil)).
  rewrite cons_nil_app.
  f_equal.
  rewrite app_length; simpl; omega.
Qed.
Proof.
  intros.
  generalize dependent a.
  induction i; intros; firstorder.
  induction a; simpl; try now firstorder.
  eauto with arith.
Qed.
Proof.
  intros.
  destruct (lt_dec n (length a)).
  rewrite skipn_app_l by omega.
  rewrite not_le_minus_0 by omega.
  auto.
  replace n with (length a + (n - length a)) at 1 by omega.
  rewrite skipn_app_r.
  rewrite skipn_oob with (l := a) by omega.
  auto.
Qed.
Proof.
  unfold removeN; intros.
  rewrite firstn_app_r.
  replace (S (length a + i)) with (length a + (S i)) by omega.
  rewrite skipn_app_r.
  apply app_assoc_reverse.
Qed.
Proof.
  induction m; simpl; intros.
  replace n with 0 by omega.
  firstorder.

  unfold repeat at 1; fold repeat.
  destruct n.
  unfold repeat; simpl; auto.

  rewrite firstn_cons.
  rewrite IHm by omega; auto.
Qed.
Proof.
  induction m; simpl; intros.
  inversion H; subst; simpl; auto.
  destruct n; auto.
  rewrite <- IHm; auto.
  omega.
Qed.
Proof.
  intros; destruct (le_dec n m).
  apply skipn_repeat'; auto.
  rewrite skipn_oob.
  replace (m - n) with 0 by omega; simpl; auto.
  rewrite repeat_length; omega.
Qed.
Proof.
  induction m; unfold repeat; firstorder; fold repeat.
  rewrite <- app_comm_cons.
  rewrite IHm.
  replace (S m + n) with (S (m + n)) by omega.
  auto.
Qed.
Proof.
  induction n; intros; simpl; auto.
  unfold repeat; fold repeat; f_equal.
  rewrite <- IHn.
  auto.
Qed.
Proof.
  intros.
  unfold removeN.
  rewrite firstn_repeat by omega.
  rewrite skipn_repeat by omega.
  rewrite app_repeat.
  f_equal; omega.
Qed.
Proof.
  destruct l; simpl; intros; try congruence.
  destruct n; simpl; try omega.
  eauto.
Qed.
Proof.
  induction l; simpl; intros; try omega.
  destruct n.
  exists a; exists l; eauto.
  destruct (IHl n); try omega.
  destruct H0.
  eauto.
Qed.
Proof.
  intros.
  generalize dependent l.
  induction n; intros; simpl.
  - reflexivity.
  - induction l; simpl.
    + rewrite firstn_nil.
      reflexivity.
    + f_equal.
      apply IHn.
Qed.
Proof.
  intros.
  generalize dependent l.
  induction n; intros; simpl.
  - symmetry; apply firstn_skipn.
  - induction l; simpl.
    + rewrite firstn_nil.
      reflexivity.
    + rewrite <- skipn_skipn'.
      symmetry; apply firstn_skipn.
Qed.
Proof.
  intros.
  replace (n+off2) with (n+off1 + (off2 - off1)) by omega.
  apply skipn_sum_split.
Qed.
Proof.
  intros.
  rewrite firstn_sum_split.
  rewrite H.
  rewrite firstn_app2 by reflexivity.
  rewrite skipn_app.
  reflexivity.
Qed.
Proof.
  intros.
  rewrite H.
  rewrite <- skipn_skipn'.
  rewrite skipn_app.
  reflexivity.
Qed.
Proof.
  intros.

  case_eq (lt_dec (length l) len2); intros.
  - rewrite firstn_oob with (n := len2) by omega.
    auto.
  - rewrite <- firstn_skipn with (n := len2) (l := l) at 2.
    rewrite skipn_app_l.
    rewrite firstn_app_l.
    auto.
    rewrite skipn_length.
    all: rewrite firstn_length_l; omega.
Qed.
Proof.
  intros.
  rewrite firstn_double_skipn; auto.
  rewrite skipn_skipn; auto.
Qed.
Proof.
  intros.
  induction lists.
  rewrite concat_nil.
  simpl; reflexivity.
  rewrite concat_cons.
  rewrite app_length.
  simpl.
  rewrite IHlists.
  rewrite Forall_forall in H.
  replace k with (length a).
  reflexivity.
  apply H; apply in_cons_head.
  eapply Forall_cons2.
  eassumption.
Qed.
Proof.
  intros.
  generalize dependent n.
  induction lists; intros; simpl.
  repeat (rewrite firstn_nil).
  reflexivity.
  case_eq n; intros.
   + reflexivity.
   + rewrite firstn_cons.
     rewrite concat_cons.
     assert (H' := H).
     rewrite Forall_forall in H'.
     assert (length a = k) as Hk.
     apply H'; apply in_cons_head.
     replace (S n0 * k) with (k + n0 * k) by auto.
     rewrite <- Hk.
     rewrite firstn_app_r.
     f_equal.
     rewrite Hk.
     apply IHlists.
     eapply Forall_cons2.
     eassumption.
Qed.
Proof.
  intros.
  generalize dependent n.
  induction lists; intros; simpl.
  repeat (rewrite skipn_nil).
  reflexivity.
  case_eq n; intros.
   + reflexivity.
   + simpl.
     assert (H' := H).
     rewrite Forall_forall in H'.
     assert (length a = k) as Hk.
     apply H'. left; reflexivity.
     replace (S n0 * k) with (k + n0 * k) by auto.
     rewrite <- Hk.
     rewrite skipn_app_r.
     f_equal.
     rewrite Hk.
     apply IHlists.
     eapply Forall_cons2.
     eassumption.
Qed.
Proof.
  intros.
  rewrite updN_firstn_skipn by assumption.
  rewrite concat_app.
  rewrite concat_cons.
  rewrite concat_app.
  rewrite concat_nil.
  rewrite app_nil_l.
  f_equal.
  apply concat_hom_firstn; assumption.
  f_equal.
  replace (n * k + k) with ((n + 1) * k).
  apply concat_hom_skipn; assumption.
  rewrite Nat.mul_add_distr_r.
  rewrite Nat.mul_1_l.
  reflexivity.
Qed.
Proof.
  intros.
  generalize dependent off.
  generalize dependent l.
  induction n; intros; simpl.
  induction l; simpl.
  inversion H1. (* impossible *)
  rewrite Forall_forall in H.
  assert (length a = k).
  apply H; apply in_cons_head.
  symmetry; apply firstn_app_l.
  rewrite H2.
  assumption.
  destruct l; simpl.
  inversion H1. (* impossible *)
  apply IHn; firstorder.
  eapply Forall_cons2; eassumption. eauto with arith.
Qed.
 Proof.
  intros.
  generalize dependent off.
  generalize dependent l.
  induction n; intros; simpl.
  induction l; simpl.
  inversion H1. (* impossible *)
  rewrite Forall_forall in H.
  assert (length a = k).
  apply H; apply in_cons_head.
  rewrite skipn_app_l by omega.
  rewrite firstn_app2.
  reflexivity.
  rewrite skipn_length; omega.
  destruct l; simpl.
  inversion H1. (* impossible *)
  apply IHn; firstorder.
  eapply Forall_cons2; eassumption. eauto with arith.
Qed.
Proof.
  intros.
  destruct (le_lt_dec b a).
  apply plus_minus.
  rewrite plus_comm.
  eapply Nat.div_add in H.
  rewrite Nat.mul_1_l in *.
  erewrite Nat.sub_add in * by eassumption.
  eassumption.
  repeat rewrite Nat.div_small by omega. auto.
Qed.
Proof.
  intros.
  destruct (le_lt_dec a 0). intuition.
  rewrite <- Nat.mod_add with (b := 1) by omega.
  rewrite Nat.mul_1_l.
  rewrite Nat.sub_add by omega.
  auto.
Qed.
Proof.
  induction l; intros;
    assert (k > 0) by (destruct (Nat.eq_dec k 0); intuition; subst; intuition).
  rewrite mult_0_r in *; omega.
  destruct nvalid; [> omega | ].
  match goal with [H : Forall _ _ |- _] => inversion H end; subst.
  destruct (lt_dec off (length a)).
  - simpl; rewrite selN_app, Nat.div_small, Nat.mod_small; auto.
    apply selN_inb; auto.
  - rewrite Nat.nlt_ge in *.
    rewrite selN_cons.
    simpl in *; rewrite mult_comm in *; simpl in *; rewrite mult_comm in *.
    simpl; rewrite selN_app2 by auto.
    erewrite <- IHl by (eauto; omega).
    rewrite mod_subt; auto.
    rewrite <- div_ge_subt by omega.
    reflexivity.
    simpl in *; rewrite mult_comm in *; simpl in *; rewrite mult_comm in *.
    apply Nat.div_str_pos; omega.
Qed.
Proof.
  induction l; cbn; intros.
  repeat rewrite skipn_nil; auto.
  inversion H; subst.
  destruct (lt_dec n (length a)).
  rewrite skipn_app_l by omega.
  rewrite Nat.mod_small by auto.
  rewrite Nat.div_small by auto.
  auto.
  replace n with (length a + (n - (length a))) at 1 by omega.
  rewrite skipn_app_r.
  rewrite IHl by auto.
  rewrite mod_subt by omega.
  rewrite div_ge_subt by auto.
  rewrite <- Nat.div_small_iff in * by auto.
  destruct (n / length a) eqn:?.
  congruence.
  cbn.
  rewrite Nat.sub_0_r.
  reflexivity.
Qed.
Proof.
  induction l; cbn; intros.
  repeat rewrite firstn_nil; auto.
  inversion H; subst.
  destruct (lt_dec n (length a)).
  rewrite firstn_app_l by omega.
  rewrite Nat.mod_small by auto.
  rewrite Nat.div_small by auto.
  auto.
  rewrite firstn_app by omega.
  rewrite firstn_oob by omega.
  rewrite IHl by auto.
  rewrite mod_subt by omega.
  rewrite div_ge_subt by auto.
  rewrite <- Nat.div_small_iff in * by auto.
  destruct (n / length a) eqn:?.
  congruence.
  cbn.
  rewrite Nat.sub_0_r.
  auto using app_assoc.
Qed.
Proof.
  intros.
  eapply selN_selN_firstn_hom; auto.
  apply forall_firstn; auto.
  rewrite mult_comm; eauto.
Qed.
Proof.
  induction i; intros; destruct a, b; simpl; auto.
  rewrite IHi; auto.
Qed.
Proof.
  intros.
  erewrite <- updN_selN_eq with (l := b) at 1.
  eauto using combine_updN.
Qed.
Proof.
  intros.
  erewrite <- updN_selN_eq with (l := a) at 1.
  eauto using combine_updN.
Qed.
Proof.
  induction i; destruct a, b; intros; inversion H; auto.
  simpl; apply IHi; assumption.
Qed.
Proof.
  intros.
  rewrite combine_length.
  rewrite H; intuition.
Qed.
Proof.
  intros.
  rewrite combine_length.
  rewrite H; intuition.
Qed.
Proof.
  induction al; destruct bl; simpl; intros; try omega; auto.
  f_equal.
  apply IHal; omega.
Qed.
Proof.
   unfold removeN; intros.
   rewrite firstn_updN; auto.
   simpl; rewrite skipn_updN; auto.
Qed.
Proof.
  intros; unfold removeN.
  rewrite firstn_oob by auto.
  rewrite skipn_oob by auto.
  apply app_nil_r.
Qed.
Proof.
  unfold removeN; firstorder.
Qed.
Proof.
  induction i; destruct a, b; intros; simpl; auto.
  - unfold removeN at 2; simpl.
    repeat rewrite removeN_oob by auto.
    induction a0; firstorder.
  - rewrite removeN_head.
    rewrite IHi.
    unfold removeN; firstorder.
Qed.
Proof.
  unfold removeN; induction l; intros; simpl.
  unfold length in H; omega.
  rewrite app_length.
  rewrite firstn_length; rewrite Nat.min_l; simpl in *; try omega.
  rewrite skipn_length; omega.
Qed.
Proof.
  intros; destruct (Nat.eq_dec (length a) 0); try omega.
  rewrite removeN_length in H1; auto.
  rewrite removeN_length in H1; auto.
  omega.
Qed.
Proof.
  intros; unfold removeN.
  rewrite skipn_oob.
  rewrite firstn_app2; eauto using app_nil_r.
  rewrite app_length; simpl; omega.
Qed.
Proof.
  induction l using rev_ind; destruct n;
  intros; simpl; intuition;
  rewrite removelast_app; try congruence;
  simpl; rewrite app_nil_r;
  rewrite selN_app; auto;
  rewrite app_length in H; simpl in H; omega.
Qed.
Proof.
  induction l using rev_ind; intros; simpl; auto.
  rewrite app_length; simpl.
  rewrite removelast_app; [| congruence].
  unfold removelast; rewrite app_length; simpl.
  omega.
Qed.
Proof.
  induction l using rev_ind; intros; simpl; firstorder.
  rewrite removelast_app; simpl.
  rewrite app_nil_r.
  rewrite app_length; simpl.
  replace (length l + 1 - 1) with (length l) by omega.
  rewrite removeN_tail; auto.
  congruence.
Qed.
Proof.
  unfold removeN.
  intros.
  rewrite <- firstn_skipn with (n := i).
  rewrite in_app_iff in *.
  intuition.
  right.
  eapply in_skipn_in with (n := 1).
  rewrite skipn_skipn.
  auto.
Qed.
Proof.
  unfold removeN.
  intros.
  erewrite <- firstn_skipn with (n := i) in H.
  rewrite in_app_iff in *.
  intuition.
  right.
  eapply in_skipn_S; eauto.
Qed.
Proof.
  induction a; cbn; intros.
  destruct b; cbn in *; intuition omega.
  destruct b; cbn in *; intuition; subst.
  eauto.
  edestruct IHa; eauto.
  omega.
Qed.
Proof.
  induction a; cbn; intros.
  omega.
  destruct b; cbn in *; intuition; subst; try omega.
  eauto.
  edestruct IHa; eauto.
  omega.
Qed.
Proof.
  destruct l using rev_ind; firstorder.
  rewrite app_length; simpl.
  rewrite removelast_app; simpl; try congruence.
  replace (length l + 1 - 1) with (length l) by omega.
  rewrite firstn_app2; auto.
  rewrite app_nil_r; auto.
Qed.
Proof.
  induction a; simpl; intros.
  rewrite <- minus_n_O; auto.
  destruct n; try omega; simpl.
  f_equal.
  apply IHa.
  omega.
Qed.
Proof.
  induction n; simpl; intros; auto.
  destruct m; try omega; simpl.
  f_equal.
  apply IHn.
  omega.
Qed.
Proof.
  intros.
  destruct (le_lt_dec n (length l1)).
  - rewrite firstn_app_l by auto.
    replace (_ - _) with 0 by omega. rewrite app_nil_r. auto.
  - rewrite firstn_app_le by omega.
    f_equal. rewrite firstn_oob by omega. auto.
Qed.
Proof.
  intros.
  rewrite skipn_selN.
  rewrite selN_firstn.
  reflexivity.
  assumption.
Qed.
Proof.
  intros; subst; unfold repeat; auto.
Qed.
Proof.
  unfold setlen; intros.
  rewrite app_length.
  rewrite repeat_length.
  destruct (le_lt_dec n (length l)).
  apply Nat.sub_0_le in l0 as Heq; rewrite Heq.
  rewrite firstn_length_l; auto.
  rewrite firstn_length_r; omega.
Qed.
Proof.
  unfold setlen; intros; simpl.
  rewrite firstn_nil.
  rewrite app_nil_l.
  rewrite Nat.sub_0_r; auto.
Qed.
Proof.
  induction tl; intros; simpl; autorewrite with lists; simpl; auto.
Qed.
Proof.
  intros; destruct l.
  simpl in H. omega.
  reflexivity.
Qed.
Proof.
  induction n; intros; auto.
  destruct l; simpl; auto.
Qed.
Proof.
  induction n; intros; auto.
  destruct l; simpl; auto.
  rewrite IHn; auto.
Qed.
Proof.
  unfold removeN.
  intros.
  rewrite firstn_map_comm, skipn_map_comm, map_app.
  auto.
Qed.
Proof.
  induction n; destruct l; intros; simpl; auto.
  rewrite firstn_nil; auto.
Qed.
Proof.
  unfold setlen; intros; simpl.
  rewrite firstn_app_le by auto.
  rewrite app_assoc.
  autorewrite with lists.
  f_equal; f_equal; omega.
Qed.
Proof.
  unfold setlen; intros.
  destruct (le_gt_dec m n).
  rewrite firstn_repeat by auto.
  rewrite repeat_app, repeat_length.
  replace (m + (m - n)) with m by omega; auto.
  
  rewrite firstn_oob by (rewrite repeat_length; omega).
  rewrite repeat_app, repeat_length.
  replace (n + (m - n)) with m by omega; auto.
Qed.
Proof.
  induction n; intros; auto.
  replace a with (@nil A); auto.
  rewrite length_nil; auto; omega.
  destruct a, b; simpl; auto.
  rewrite app_nil_r, skipn_nil, skipn_oob; auto.
  simpl in H; omega.
  apply IHn.
  simpl in H; omega.
Qed.
Proof.
  intros.
  rewrite firstn_map_comm.
  rewrite firstn_exact; auto.
Qed.
Proof.
  induction l; simpl; auto.
  rewrite IHl; rewrite <- surjective_pairing; auto.
Qed.
Proof.
  induction l; cbn; intros.
  auto.
  f_equal; eauto.
Qed.
Proof.
  induction a; cbn; intros.
  auto.
  destruct b; cbn; auto.
  f_equal; eauto.
Qed.
Proof.
  intros.
  setoid_rewrite combine_map' with (g := id).
  rewrite map_id.
  auto.
Qed.
Proof.
  intros.
  setoid_rewrite combine_map' with (f := id).
  rewrite map_id.
  auto.
Qed.
Proof.
  unfold map, List.combine; induction a; intros; auto.
  destruct b; try discriminate; simpl in *.
  rewrite IHa; [ auto | congruence ].
Qed.
Proof.
  unfold map, List.combine.
  induction a; destruct b; simpl; auto; try discriminate.
  intros; rewrite IHa; eauto.
Qed.
Proof.
  induction l; intros; simpl; auto.
  destruct a0; simpl; auto.
  rewrite IHl; auto.
Qed.
Proof.
  induction ents; simpl; auto; intros.
  f_equal.
  apply IHents.
Qed.
Proof.
  induction ents; simpl; auto; intros.
  f_equal.
  apply IHents.
Qed.
Proof.
  induction l; simpl; intros; auto.
  rewrite skipn_nil; auto.
  inversion H; subst.
  destruct n; simpl; auto.
Qed.
Proof.
  induction a; simpl; intros.
  constructor.
  inversion H; constructor; eauto.
  intro; apply H2.
  apply in_or_app; eauto.
Qed.
Proof.
  induction a; simpl; intros; eauto.
  inversion H; eauto.
Qed.
Proof.
  induction b using rev_ind; simpl; intros; eauto.
  eapply NoDup_remove_1.
  eapply IHb. rewrite <- app_assoc in H. eauto.
Qed.
Proof.
  induction l1; simpl; intros; eauto.
  intuition; subst.
  inversion H0; subst; eauto.
  inversion H0; subst; eauto.
Qed.
Proof.
  induction l1; simpl; intros; eauto.
  intuition; subst.
  inversion H0; subst; eauto.
Qed.
Proof.
  induction l2; simpl; intros; try rewrite app_nil_r in *; eauto.
  constructor.
  intro H'. apply in_app_or in H'.
  eapply NoDup_remove_2; eauto.
  apply in_or_app; intuition.
  eapply IHl2; eapply NoDup_remove_1; eauto.
Qed.
Proof.
  induction l1; simpl; intros.
  rewrite app_nil_r in *. eapply NoDup_app_comm; eauto.
  rewrite app_assoc in H. apply NoDup_app_comm in H. simpl in H.
  inversion H; subst.
  constructor.
  - intro H'. apply H2.
    apply in_or_app. apply in_app_or in H'. intuition. right.
    apply in_or_app. apply in_app_or in H0. intuition.
  - eapply IHl1.
    apply NoDup_app_comm in H3. rewrite <- app_assoc in H3. eauto.
Qed.
Proof.
  intros.
  erewrite <- firstn_skipn in H.
  eapply not_In_NoDup_app; eauto.
Qed.
Proof.
  intros.
  eapply in_nodup_split; rewrite ?firstn_skipn; eauto.
Qed.
Proof.
  induction l; simpl; firstorder.
  destruct a; simpl in *; subst; eauto.
Qed.
Proof.
  unfold setlen; intros.
  destruct (le_dec n (length l)).
  right.
  rewrite repeat_is_nil in H by omega; rewrite app_nil_r in H.
  eapply in_firstn_in; eauto.
  apply in_app_or in H; destruct H.
  right. eapply in_firstn_in; eauto.
  left. eapply repeat_spec; eauto.
Qed.
Proof.
  induction l using rev_ind; intros; simpl.
  rewrite updN_oob; auto.
  rewrite skipn_nil; simpl; omega.

  destruct (lt_dec i (length l - n)).
  destruct (le_dec n (length l)).
  rewrite skipn_app_l by auto.
  repeat rewrite updN_app1 by (try rewrite skipn_length; omega).
  setoid_rewrite skipn_app_l; autorewrite with lists; auto.
  f_equal; eauto.
  rewrite updN_app1 by omega.
  repeat rewrite skipn_app_r_ge by omega.
  rewrite length_updN, skipn_oob; simpl; auto; omega.

  destruct (le_dec n (length l)).
  rewrite skipn_app_l by auto.
  repeat rewrite updN_app2 by (try rewrite skipn_length; omega).
  setoid_rewrite skipn_app_l; autorewrite with lists; auto; f_equal.
  rewrite skipn_length; f_equal; omega.
  repeat rewrite skipn_oob; autorewrite with lists; simpl; auto; omega.
Qed.
Proof.
  intros; destruct H.
  rewrite skipN_updN'; auto.
  unfold setlen.
  repeat rewrite <- skipn_firstn_comm.
  rewrite firstn_updN_oob by omega.
  repeat rewrite skipn_length.
  rewrite length_updN; auto.
Qed.
Proof.
  unfold setlen; intros.
  replace (n - length l) with 0 by omega.
  simpl; rewrite app_nil_r; auto.
Qed.
Proof.
  unfold setlen; intros.
  rewrite firstn_oob by omega; auto.
Qed.
Proof.
  unfold setlen; intros; subst.
  rewrite firstn_oob by omega; auto.
  rewrite Nat.sub_diag; simpl.
  rewrite app_nil_r; auto.
Qed.
Proof.
  induction l; cbn; intros.
  rewrite length_nil; auto.
  autorewrite with list. auto.
  destruct l'; cbn in *. omega.
  rewrite (H 0).
  f_equal; auto.
  eapply IHl.
  intros i. apply (H (S i)).
  omega.
Qed.
Proof.
  induction n; simpl; intros; auto.
  f_equal; auto.
Qed.
Proof.
  intros.
  rewrite Forall_forall in H.
  apply H.
  apply in_selN; auto.
Qed.
Proof.
  induction l; intros; eauto.
  apply Forall_cons.
  apply (H 0); simpl; omega.
  eapply IHl; intros.
  apply (H (S i)); simpl; omega.
Qed.
Proof.
  induction l.
  auto.
  intro Hni. simpl.
  destruct (dec a a0).
  subst. destruct Hni. simpl. tauto.
  rewrite IHl. trivial.
  simpl in Hni. tauto.
Qed.
Proof.
  induction l; simpl; [tauto|].
  destruct (dec b a0).
  right; apply IHl; assumption.
  intro H. destruct H. subst. auto.
  right; apply IHl; assumption.
Qed.
Proof.
  induction l; simpl; [tauto|].
  destruct (dec b a0).
  assumption.
  intro H. destruct H. subst. auto.
  apply IHl; assumption.
Qed.
Proof.
  induction l.
  auto.
  simpl. destruct (dec b a0).
  subst. intros. destruct H0; [subst; tauto | apply IHl; auto].
  simpl. intros. destruct H0; [left; auto | right; apply IHl; auto].
Qed.
Proof.
  induction l; simpl; intros; eauto.
  inversion H; subst.
  destruct (EQ v a); eauto.
  constructor; eauto.
  contradict H2.
  eapply remove_still_In; eauto.
Qed.
Proof.
  induction l; intros; subst.
  - simpl. 
    destruct (E a a); try congruence.
  - unfold remove.
    destruct (E a0 a0); subst; try congruence.
    destruct (E a0 a); subst. try congruence.
    + exfalso. inversion H.
      apply H2. constructor; auto.
    + unfold remove in IHl; simpl in IHl.
      specialize (IHl a0). 
      destruct (E a0 a0); subst; try congruence.
      rewrite IHl; auto.
      rewrite cons_app in H.
      rewrite cons_app with (l := l) in H.
      eapply NoDup_remove_mid in H; auto.
Qed.
Proof.
  induction l; intros; subst.
  - simpl.
    destruct (E a b); subst; try congruence.
  - unfold remove.
    destruct (E a0 b); subst; try congruence.
Qed.
Proof.
  induction l; cbn; intros; auto.
  repeat (destruct E; cbn); congruence.
Qed.
Proof.
  induction l; cbn; intros; auto.
  repeat (destruct E; cbn); subst.
  eauto.
  congruence.
  congruence.
  f_equal; eauto.
Qed.
Proof.
  cbn; intros; destruct E; congruence.
Qed.
Proof.
  intros; simpl; auto.
Qed.
Proof.
  induction n; destruct l; simpl; eauto.
Qed.
Proof.
  intros.
  repeat rewrite firstn_length in H.
  repeat rewrite skipn_length in H0.
  destruct (le_dec n (length a)); destruct (le_dec n (length b)).
  omega.
  rewrite Nat.min_l in H by auto.
  rewrite Nat.min_r in H by omega; subst.
  omega.
  rewrite Nat.min_r in H by omega.
  rewrite Nat.min_l in H by omega; subst.
  omega.
  rewrite Nat.min_r in H by omega.
  rewrite Nat.min_r in H by omega; subst.
  omega.
Qed.
Proof.
  induction l; simpl; intros.
  rewrite Forall_forall in *; firstorder.
  split; intros;
  inversion H; simpl; subst;
  apply Forall_cons; firstorder.
Qed.
Proof.
  induction l; simpl; split; intros;
  try apply Forall_nil; inversion H;
  subst; firstorder.
  apply Forall_cons; firstorder.
Qed.
Proof.
  induction l; simpl; split; intros;
  try apply Forall_nil; inversion H;
  subst; firstorder.
  apply Forall_cons; firstorder.
Qed.
Proof.
  induction l; simpl; intros; eauto.
  inversion H; subst.
  destruct (EQ a0 a); eauto.
Qed.
Proof.
  induction 1; simpl; auto.
Qed.
Proof.
  induction 1; simpl; auto.
Qed.
Proof.
  induction a; destruct b; firstorder.
  inversion H0.
  inversion H0.
  inversion H; subst; simpl in *.
  constructor; auto.
Qed.
Proof.
  induction la; simpl; intros.
  inversion H. constructor.
  inversion H; subst.
  constructor; eauto.
Qed.
Proof.
  induction la; simpl; intros.
  inversion H. constructor.
  inversion H; subst.
  constructor; eauto.
Qed.
Proof.
  induction la; simpl; intros.
  inversion H. constructor.
  inversion H; subst.
  constructor; eauto.
Qed.
Proof.
  induction la; simpl; intros.
  inversion H. constructor.
  inversion H; subst.
  constructor; eauto.
Qed.
Proof.
  induction la; simpl; intros; destruct lb; simpl in *; try congruence.
  constructor.
  inversion H0.
  constructor; eauto.
Qed.
Proof.
  induction la; simpl; intros; destruct lb; simpl in *; try congruence.
  constructor.
  inversion H0.
  constructor; eauto.
Qed.
Proof.
  induction la; simpl; intros; destruct lb; simpl in *; try congruence.
  constructor.
  inversion H.
  inversion H.
  inversion H; subst.
  inversion H0; subst.
  constructor; eauto.
Qed.
Proof.
  induction la; simpl; intros; destruct lb; simpl in *; try congruence.
  constructor.
  constructor; eauto.
Qed.
Proof.
  intros.
  pose proof (forall2_length H).
  apply forall2_forall in H.
  eapply Forall_selN with (i := n) in H.
  erewrite selN_combine in H; eauto.
  rewrite combine_length_eq; auto.
Qed.
Proof.
  intros.
  apply forall_forall2.
  rewrite combine_updN.
  apply Forall_updN; auto.
  apply forall2_forall; auto.
  repeat rewrite length_updN.
  eapply forall2_length; eauto.
Qed.
Proof.
  induction a; destruct b; intros; eauto.
  inversion H.
  inversion H.
  constructor.
  specialize (H0 0); simpl in *.
  apply H0; omega.
  eapply IHa.
  inversion H; auto.
  intros.
  specialize (H0 (S i)); simpl in *.
  apply H0.
  omega.
Qed.
Proof.
  intros.
  induction H0.
  - simpl. eapply Forall2_nil.
  - constructor.
    specialize (H x y).
    eapply H; eauto.
    constructor; auto.
    constructor; auto.
    eapply IHForall2; intros.
    eapply H; eauto.
    eapply in_cons; eauto.
    eapply in_cons; eauto.
Qed.
Proof.
  intros.
  induction H0.
  - simpl. eapply Forall2_nil.
  - constructor.
    specialize (H x y 0).
    eapply H; eauto.
    simpl; omega.
    eapply IHForall2; intros.
    eapply H; eauto.
    instantiate (1 := (S n)).
    simpl; omega.
    rewrite selN_cons; eauto.
    replace (S n - 1) with n by omega; eauto.
    omega.
    rewrite selN_cons; eauto.
    replace (S n - 1) with n by omega; eauto.
    omega.
Qed.
Proof.
  induction l; simpl; intros.
  inversion H; eauto.
  inversion H; subst.
  erewrite IHl; eauto.
Qed.
Proof.
  intros.
  apply Forall2_eq.
  eapply forall2_map2_in; eauto.
Qed.
Proof.
  unfold cuttail; intros.
  rewrite firstn_length.
  rewrite Nat.min_l; omega.
Qed.
Proof.
  unfold cuttail; intros.
  rewrite firstn_oob by omega; auto.
Qed.
Proof.
  unfold cuttail; intros.
  replace (length l - n) with 0 by omega.
  simpl; auto.
Qed.
Proof.
  induction l; intuition; simpl.
  rewrite Nat.sub_0_r, IHl.
  case_eq (length l); intros.
  erewrite length_nil with (l := l); auto.
  destruct l.
  inversion H.
  replace (S n - 1) with n by omega; auto.
Qed.
Proof.
  unfold cuttail; intros.
  rewrite last_selN.
  rewrite selN_firstn.
  rewrite firstn_length_l by omega; auto.
  rewrite firstn_length_l by omega; omega.
Qed.
Proof.
  unfold cuttail; intros.
  rewrite firstn_firstn, firstn_length.
  f_equal.
  apply Nat.min_case_strong; intros.
  apply Nat.min_case_strong; intros; omega.
  rewrite Nat.min_l in H; omega.
Qed.
Proof.
  unfold cuttail; intros.
  rewrite app_length; simpl.
  replace (length l + 1 - S n) with (length l - n) by omega.
  rewrite firstn_app_l; auto; omega.
Qed.
Proof.
  induction n; simpl; intros.
  rewrite cuttail_0. auto.
  destruct l using rev_ind; simpl; auto.
  rewrite cuttail_tail in *.
  rewrite IHn by auto.
  rewrite selN_app; auto.
  rewrite cuttail_length in *; omega.
Qed.
Proof.
  unfold cuttail; simpl; intros.
  destruct n; simpl.
  rewrite Nat.sub_0_r; auto.
  rewrite <- firstn_cons.
  f_equal.
  omega.
Qed.
Proof.
  unfold cuttail.
  intros; subst.
  destruct (length l) eqn:?. omega.
  rewrite Nat.sub_succ, Nat.sub_succ_l by omega.
  erewrite firstn_S_selN; auto.
  omega.
Qed.
Proof.
  unfold cuttail; intros.
  erewrite concat_hom_length by eauto.
  rewrite <- Nat.mul_sub_distr_r.
  rewrite concat_hom_firstn by eauto.
  reflexivity.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  destruct l; auto; intros.
  assert (In t nil).
  apply H; constructor; auto.
  inversion H0.
Qed.
Proof.
  induction l; unfold incl; simpl; auto; intros.
  destruct (dec a a0); subst; eauto.
  inversion H; subst; eauto.
Qed.
Proof.
  auto.
Qed.
Proof.
  intros T l start len.
  generalize dependent l.
  generalize dependent start.
  induction len; intros; auto.
  unfold upd_range in *. simpl.
  rewrite length_updN. auto.
Qed.
Proof.
  intros T l start len.
  generalize dependent l.
  generalize dependent start.
  induction len; intros. omega.
  simpl.
  destruct (Nat.eq_dec start n). subst. rewrite selN_updN_eq. auto.
  rewrite upd_range_length. auto.
  rewrite selN_updN_ne by auto.
  rewrite IHlen. auto. omega. auto.
Qed.
Proof.
  intros T l start len.
  generalize dependent l.
  generalize dependent start.
  induction len; intros. simpl.
  - unfold upd_range'. rewrite plus_0_r. simpl.
    rewrite firstn_skipn. auto.
  - simpl. rewrite IHlen by omega.
    unfold upd_range'. simpl repeat.
    erewrite firstn_S_selN by omega.
    repeat rewrite <- app_assoc.
    rewrite updN_app2. rewrite updN_app1.
    all : rewrite firstn_length_l by omega.
    rewrite plus_Snm_nSm.
    rewrite Nat.sub_diag. simpl. auto.
    all : simpl; omega.
  Unshelve.
  eauto.
Qed.
Proof.
  unfold upd_range'.
  induction l; simpl; intros.
  - assert (start = 0) by omega.
    assert (len = 0) by omega.
    subst; auto.
  - destruct start, len; simpl.
    unfold upd_range'; simpl; auto.
    erewrite IHl; eauto; try omega.
    erewrite IHl; eauto; try omega.
    erewrite IHl; eauto; try omega.
Qed.
Proof.
  intros. assert (k <> 0) by omega.
  match goal with [H : context [length (concat _)]|- _ ] =>
    pose proof H; erewrite concat_hom_length in H by eauto end.
  repeat rewrite upd_range_eq_upd_range'.
  unfold upd_range'.
  erewrite <- concat_hom_updN_first_skip; eauto.
  erewrite concat_hom_subselect_firstn; eauto.
  erewrite <- concat_hom_skipn; eauto.
  rewrite <- skipn_firstn_comm. rewrite mult_comm. rewrite <- Nat.div_mod by auto.
  erewrite <- Nat.min_l with (n := _ * _) at 1. rewrite <- firstn_firstn.
  repeat rewrite app_assoc. rewrite firstn_skipn.
  repeat rewrite <- app_assoc. repeat f_equal.
  erewrite concat_hom_subselect_skipn; eauto.
  rewrite <- skipn_firstn_comm.
  rewrite le_plus_minus_r by auto.
  erewrite <- concat_hom_skipn; eauto.
  rewrite <- skipn_firstn_comm.
  rewrite skipn_skipn. rewrite Nat.add_shuffle0.
  rewrite plus_comm with (m := _ * _). rewrite mult_comm. rewrite <- Nat.div_mod by auto.
  remember (k - start mod k - len) as e.
  replace k with (start mod k + len + e) at 3 6 by omega.
  repeat rewrite plus_assoc. rewrite <- Nat.div_mod by auto.
  rewrite skipn_firstn_comm.
  rewrite plus_comm with (m := e).
  repeat rewrite <- skipn_skipn.
  rewrite firstn_skipn. auto.
  all : try (apply Nat.div_lt_upper_bound; auto; rewrite mult_comm; omega).
  all : try apply Nat.mul_div_le; auto.
  - omega.
  - eapply le_trans; eauto. apply Nat.eq_le_incl.
    symmetry. apply Forall_selN; auto.
    apply Nat.div_lt_upper_bound; auto. rewrite mult_comm; omega.
Qed.
Proof.
  intros.
  rewrite <- Nat.mod_divide in * by omega.
  erewrite upd_range_concat_hom_small; eauto. repeat (f_equal; auto).
  all : omega.
Qed.
Proof.
  intros T start len.
  generalize start.
  induction len; intros; simpl; auto.
  rewrite IHlen. auto.
Qed.
Proof.
  intros.
  generalize dependent start. generalize dependent len.
  induction len; intros. auto.
  simpl. rewrite IHlen.
  destruct (lt_dec start n).
  erewrite selN_eq_updN_eq. auto.
  rewrite repeat_selN; auto.
  rewrite updN_oob. auto.
  rewrite repeat_length. omega.
  Unshelve. eauto.
Qed.
Proof.
  intros.
  generalize dependent start. generalize dependent l.
  induction len; intros.
  rewrite upd_range_0. auto.
  simpl. apply Forall_updN; auto.
Qed.
Proof.
  intros.
  generalize dependent n. generalize dependent l.
  generalize dependent n'. induction len; intros.
  rewrite upd_range_0. auto.
  simpl. rewrite firstn_updN_oob by omega. auto.
Qed.
Proof.
  intros T l start len.
  generalize dependent start. generalize dependent l.
  induction len; intros; simpl; auto.
  rewrite updN_comm by omega.
  rewrite IHlen by omega. auto.
Qed.
Proof.
  intros T l start len1.
  generalize dependent l. generalize dependent start.
  induction len1; intros; simpl.
  rewrite plus_0_r. auto.
  rewrite upd_range_updN_oob by omega.
  rewrite <- plus_Snm_nSm. rewrite IHlen1. auto.
Qed.
Proof.
  intros T l start len. generalize dependent start.
  generalize dependent l.
  induction len; simpl; intros. auto.
  rewrite IHlen. auto.
Qed.
Proof.
  induction vs; cbn; intros; auto.
  destruct start; f_equal; auto.
Qed.
Proof.
  induction vs; cbn; intros.
  rewrite upd_range_nil. auto.
  destruct start, len; cbn; auto.
  rewrite upd_range_hd.
  cbn; f_equal; auto.
  rewrite upd_range_fast_len_0. auto.
  rewrite upd_range_hd. cbn.
  f_equal.
  rewrite IHvs. reflexivity.
Qed.
Proof.
  intros T l1 l2 start len. generalize dependent start.
  generalize dependent l1. generalize dependent l2.
  induction len; intros; simpl; auto.
  rewrite IHlen by omega.
  rewrite updN_app1. auto.
  rewrite upd_range_length. omega.
Qed.
Proof.
  intros T l1 l2 start len. generalize dependent start.
  generalize dependent l1. generalize dependent l2.
  induction len; intros; simpl; auto.
  rewrite IHlen by omega.
  rewrite updN_app2 by omega. repeat f_equal. omega.
Qed.
Proof.
  intros T l start len.
  generalize dependent start. generalize dependent l.
  induction len; intros; simpl; auto.
  rewrite selN_updN_ne by omega. apply IHlen.
  omega.
Qed.
Proof.
  destruct len; intros; simpl;
    rewrite removeN_updN; auto.
Qed.
Proof.
  intros T l i.
  generalize dependent l.
  induction i; intros.
  - destruct l; simpl in *. rewrite removeN_nil. auto.
    destruct i'; try omega. repeat rewrite removeN_head. auto.
  - destruct l; simpl in *. rewrite removeN_nil. auto.
    destruct i'; try omega. repeat rewrite removeN_head.
    simpl. f_equal. apply IHi. omega.
Qed.
Proof.
  intros T l start len. generalize dependent start.
  generalize dependent l.
  induction len; intros; simpl.
  - rewrite plus_0_r. rewrite removeN_updN. auto.
  - repeat rewrite removeN_updN_lt by omega. f_equal.
    rewrite <- plus_Snm_nSm. apply IHlen.
Qed.
Proof.
  intros T l start len. generalize dependent start.
  generalize dependent l.
  induction len; intros; simpl.
  + rewrite firstn_oob by omega. replace (_ - _) with 0 by omega.
    rewrite app_nil_r. auto.
  + rewrite IHlen by omega.
    destruct (le_lt_dec (length l) start).
    - repeat rewrite firstn_oob by omega.
      repeat replace (_ - _) with 0 by omega.
      rewrite app_nil_r. rewrite updN_oob; auto.
    - replace (S start) with (start + 1) by omega.
      rewrite firstn_sum_split.
      rewrite updN_app1, updN_app2.
      all : try rewrite app_length.
      all : repeat rewrite firstn_length_l.
      rewrite Nat.sub_diag.
      destruct (skipn start l) eqn:H'.
      apply f_equal with (f := @length _) in H'. simpl in *.
      all : try rewrite skipn_length in *; try omega.
      rewrite <- app_assoc. simpl.
      replace (length l - start) with (S (length l - (start + 1))) by omega.
      auto.
Qed.
Proof.
  intros T l start len.
  generalize dependent start. generalize dependent l.
  induction len; intros; simpl. auto.
  rewrite updN_oob. rewrite IHlen; auto.
  rewrite upd_range_length. auto.
Qed.
Proof.
  intros.
  destruct (le_lt_dec (length l) (start + len)).
  + rewrite upd_range_eq_app_firstn_repeat by auto.
    unfold removeN.
    repeat rewrite firstn_app_le by (rewrite firstn_length_l; omega).
    rewrite firstn_length_l by omega.
    repeat rewrite skipn_app_r_ge by (rewrite firstn_length_l; omega).
    repeat rewrite skipn_repeat.
    repeat rewrite firstn_repeat by omega.
    repeat rewrite <- app_assoc. repeat rewrite repeat_app.
    f_equal. f_equal. rewrite firstn_length_l by omega.
    repeat rewrite <- Nat.sub_add_distr.
    omega.
  + repeat rewrite upd_range_eq_upd_range' by omega.
    unfold upd_range', removeN.
    repeat (
      rewrite firstn_app_le; rewrite firstn_length;
      (let H := fresh in let H' := fresh in
        edestruct Min.min_spec as [ [H H']|[H H'] ];
        rewrite H' in *; clear H'); try omega;
      rewrite firstn_app_l by (rewrite repeat_length; omega)).
    repeat rewrite <- app_assoc. f_equal.
    rewrite skipn_app_r_ge by (rewrite firstn_length_l; omega).
    rewrite skipn_app_r_ge with (n := S _) by (rewrite firstn_length_l; omega).
    repeat rewrite firstn_length_l by omega.
    repeat rewrite firstn_repeat by omega.
    match goal with [|- context [skipn ?a (repeat _ ?b ++ _)] ] =>
      rewrite le_plus_minus with (m := b) (n := a) at 1 by omega;
      rewrite <- repeat_app, <- app_assoc;
      rewrite skipn_app_l, skipn_oob by (rewrite repeat_length; omega)
    end. symmetry.
    match goal with [|- context [skipn ?a (repeat _ ?b ++ _)] ] =>
      rewrite le_plus_minus with (m := b) (n := a) at 1 by omega;
      rewrite <- repeat_app, <- app_assoc;
      rewrite skipn_app_l, skipn_oob by (rewrite repeat_length; omega)
    end.
    repeat rewrite app_nil_l. repeat rewrite app_assoc.
    repeat rewrite repeat_app. do 2 f_equal.
    omega.
Qed.
Proof.
  induction l; intros; simpl.
  repeat rewrite upd_range_nil. auto.
  apply Forall_inv in H as H'.
  apply Forall_cons2 in H as H''. subst.
  destruct len. auto.
  simpl. rewrite upd_range_hd.
  destruct start; simpl.
  -rewrite IHl by auto. simpl.
    rewrite <- upd_range_upd_range. simpl.
    rewrite upd_range_app_l by omega.
    rewrite upd_range_app_r.
    rewrite upd_range_eq_app_firstn_repeat with (len := length _) by omega.
    simpl. rewrite repeat_length. rewrite Nat.sub_0_r, Nat.sub_diag. auto.
    rewrite upd_range_length. omega.
  - rewrite upd_range_app_r. f_equal.
    rewrite minus_plus.
    rewrite <- IHl with (len := S len) by auto.
    auto.
    apply le_plus_l.
Qed.
Proof.
  induction l; intros.
  rewrite upd_range_nil. rewrite skipn_nil. rewrite app_nil_r.
  replace len with 0 by (simpl in *; omega). auto.
  destruct len. auto. simpl in *.
  rewrite upd_range_hd. rewrite IHl by omega. auto.
Qed.
Proof.
  induction l; intros.
  simpl. rewrite upd_range_nil. auto.
  simpl in *. destruct len; try omega.
  simpl. rewrite upd_range_hd. rewrite IHl by omega. auto.
Qed.
Proof.
  intros T l1 l2 start len.
  generalize dependent l1. generalize dependent l2.
  generalize dependent start.
  induction len; intros; auto.
  rewrite upd_range_eq_upd_range' by auto.
  unfold upd_range'.
  rewrite firstn_app_l by omega.
  rewrite upd_range_eq_app_firstn_repeat by omega.
  rewrite <- app_assoc. f_equal.
  rewrite app_length in *.
  destruct (le_dec (length l2) (S len - (length l1 - start))).
  rewrite upd_range_all by omega.
  rewrite skipn_oob by (rewrite app_length; omega).
  rewrite repeat_app. rewrite app_nil_r. f_equal. omega.
  rewrite upd_range_start_0 by omega.
  rewrite app_assoc. rewrite repeat_app.
  rewrite skipn_app_r_ge by omega. repeat (omega || f_equal).
Qed.
Proof.
  firstorder.
Qed.
Proof.
  unfold postfix; intros.
  exists (length l).
  rewrite skipn_oob; auto.
Qed.
Proof.
  unfold postfix; intros.
  exists 0; auto.
Qed.
Proof.
  unfold postfix; intros.
  destruct H. eexists; subst.
  rewrite skipn_app_r; eauto.
Qed.
Proof.
  intros.
  rewrite cons_app.
  apply postfix_app; auto.
Qed.
Proof.
  unfold postfix; intros.
  destruct H.
  destruct l; try congruence.
  destruct x; simpl in *; try congruence.
  rewrite skipn_nil in H; congruence.
Qed.
Proof.
  intros.
  rewrite <- rev_involutive. rewrite <- H. rewrite -> rev_involutive.
  reflexivity.
Qed.
Proof.
  split; intros; apply f_equal with (f := @rev T) in H;
    rewrite rev_involutive in *; auto.
Qed.
Proof.
  induction l; simpl; auto; intros.
  inversion H; subst; auto.
  intro; intuition; subst.
  rewrite in_app_iff in H2; intuition.
  eapply IHl; eauto.
Qed.
Proof.
  induction l using rev_ind; simpl; intros; auto.
  rewrite rev_app_distr; simpl.
  apply NoDup_app_l in H as H1.
  apply NoDup_app_not_In in H as H2.
  constructor; eauto.
  contradict H2.
  apply in_rev; auto.
Qed.
Proof.
  induction l; simpl; intros; auto.
  apply NoDup_app_l in H as H1.
  apply NoDup_app_not_In in H as H2.
  constructor; eauto.
  contradict H2.
  apply in_rev in H2; auto.
Qed.
Proof.
  split.
  apply NoDup_rev_1.
  apply NoDup_rev_2.
Qed.
Proof.
  induction l; cbn; auto.
  intros.
  destruct (lt_dec n (length l)).
  rewrite selN_app1 by (rewrite rev_length; auto).
  rewrite IHl by auto.
  destruct (length l - n) eqn:?; try omega.
  f_equal; omega.
  rewrite selN_app2 by (rewrite rev_length; omega).
  rewrite rev_length.
  repeat match goal with |- context [?a - ?b] =>
    destruct (a - b) eqn:?; try omega
  end.
  auto.
Qed.
Proof.
  induction l using rev_ind; cbn; intros.
  auto using firstn_nil.
  rewrite rev_app_distr; cbn.
  rewrite app_length; cbn.
  rewrite plus_comm.
  rewrite skipn_app_split.
  rewrite rev_app_distr.
  rewrite <- Nat.sub_add_distr.
  rewrite plus_comm with (n := n).
  rewrite Nat.sub_add_distr.
  rewrite Nat.add_sub.
  destruct n.
  repeat rewrite skipn_oob by (cbn; omega).
  auto.
  cbn.
  congruence.
Qed.
Proof.
  induction a; destruct b; cbn; intros; auto.
  congruence.
  rewrite combine_app; cbn.
  f_equal; auto.
  repeat rewrite rev_length; auto.
Qed.
Proof.
  intros.
  erewrite <- firstn_skipn at 1.
  f_equal.
  cbn.
  erewrite skipn_selN_skipn.
  f_equal.
  rewrite firstn_rev by auto.
  rewrite rev_involutive.
  f_equal; omega.
  omega.
Qed.
Proof.
  induction l; simpl; auto.
  destruct (f a); simpl; auto; omega.
Qed.
Proof.
  unfold disjoint; firstorder.
Qed.
Proof.
  unfold disjoint; firstorder.
Qed.
Proof.
  unfold disjoint; firstorder; subst.
  specialize (H x0); intuition.
  pose proof (H x); pose proof (H x0); intuition.
  firstorder; subst; intuition.
Qed.
Proof.
  intros.
  unfold enumerate.
  destruct d.
  rewrite selN_combine.
  rewrite nth_selN_eq, seq_nth; auto.
  apply seq_length.
Qed.
Proof.
  unfold enumerate; intros.
  rewrite combine_length_eq; rewrite seq_length; auto.
Qed.
Proof.
  induction n; intros; auto; simpl.
  destruct b; auto; simpl; f_equal; auto.
Qed.
Proof.
  unfold enumerate; intros.
  rewrite firstn_combine_comm; f_equal.
  rewrite firstn_seq; f_equal.
  rewrite firstn_length; auto.
Qed.
Proof.
  unfold enumerate.
  split; intros; subst; auto.
  generalize dependent H.
  generalize 0.
  generalize dependent l2.
  induction l1; simpl in *; intros;
  destruct l2; try inversion H; auto.
  f_equal; eauto.
Qed.
Proof.
  unfold part. intros.
  destruct (Nat.eq_dec 0 k); subst.
  auto.
  rewrite Nat.div_0_l by auto. auto.
Qed.
Proof.
  intros.
  unfold Nat.divide in *. destruct H.
  unfold part.
  rewrite H, Nat.div_mul by auto.
  rewrite map_length, seq_length; auto.
Qed.
Proof.
  intros.
  destruct H. unfold part; rewrite H.
  rewrite Nat.div_mul by auto.
  apply Forall_map, Forall_forall.
  intros x0 HH.
  apply in_seq in HH.
  apply firstn_length_l.
  rewrite skipn_length, H.
  rewrite <- Nat.mul_sub_distr_r, mult_comm.
  rewrite <- mult_1_r at 1.
  apply mult_le_compat_l. omega.
Qed.
Proof.
  intros.
  unfold part.
  destruct H.
  remember (length l) as n.
  generalize dependent n.
  generalize dependent l.
  generalize dependent k.
  induction x; intros.
  simpl in *; rewrite H in *.
  rewrite Nat.div_0_l by auto.
  simpl.
  symmetry; apply length_nil. auto.
  rewrite H; simpl.
  rewrite Nat.div_add, Nat.div_same by auto.
  simpl in *.
  rewrite <- seq_shift, map_map.
  simpl in *.
  rewrite <- firstn_skipn with (l := l) at 2.
  f_equal.
  rewrite <- IHx with (k := k) (n := x * k); auto.
  rewrite Nat.div_mul by auto.
  f_equal. apply map_ext.
  intros.
  f_equal.
  rewrite skipn_skipn'; auto.
  rewrite skipn_length.
  assert (x * k >= 0) by intuition.
  omega.
Qed.
Proof.
  unfold part.
  intros.
  erewrite concat_hom_length; eauto.
  rewrite Nat.div_mul by auto.
  induction l; simpl; intros. auto.
  inversion H; subst.
  f_equal. rewrite firstn_app2; auto.
  rewrite <- seq_shift, map_map.
  simpl in *.
  rewrite <- IHl at 2 by auto.
  apply map_ext.
  intros.
  f_equal.
  rewrite skipn_app_r. auto.
Qed.
  Proof.
    induction vs; simpl; intros; try congruence.
    destruct cond.
    inversion H; simpl; auto.
    apply le_Sn_le.
    apply IHvs; auto.
  Qed.
  Proof.
    induction vs; simpl; intros; try congruence.
    destruct (cond a) eqn: C.
    inversion H; simpl; omega.
    replace (start + S (length vs)) with (S start + length vs) by omega.
    apply IHvs; auto.
  Qed.
  Proof.
    induction vs; simpl; intros; try congruence.
    destruct (cond a) eqn: C.
    inversion H; simpl; auto.
    eapply IHvs; eauto.
  Qed.
  Proof.
    induction vs; simpl; intros; try congruence.
    destruct cond.
    inversion H; simpl; auto.
    rewrite Nat.sub_diag; simpl; auto.
    replace (fst r - start) with (S (fst r - S start)).
    apply IHvs; auto.
    apply ifind_list_ok_mono in H; omega.
  Qed.
  Proof.
    intros; intuition eauto using
      ifind_list_ok_mono,
      ifind_list_ok_bound,
      ifind_list_ok_cond,
      ifind_list_ok_item.
  Qed.
  Proof.
    induction l; simpl; intros; try omega.
    destruct ix.
    rewrite Nat.add_0_r.
    destruct cond; congruence.
    rewrite <- plus_Snm_nSm.
    apply IHl; try omega.
    destruct (cond a); congruence.
  Qed.
Proof.
  induction a; simpl; intros.
  constructor.
  inversion H; subst.
  constructor.
  eauto.
Qed.
Proof.
  induction a; simpl; intros; eauto.
  inversion H; subst; eauto.
Qed.
Proof.
  induction a; simpl; intros; eauto.
  inversion H; subst.
  constructor; eauto.
Qed.
Proof.
  induction n; simpl; intros; constructor; eauto.
Qed.
Proof.
  induction n; simpl; intros; try constructor.
  destruct l; try constructor.
  inversion H; subst.
  constructor; eauto.
Qed.
Proof.
  induction n; simpl; intros; eauto.
  destruct l; try constructor.
  inversion H; subst; eauto.
Qed.
Proof.
  induction n2; simpl; intros.
  constructor.
  destruct n1; try omega.
  destruct l; try constructor.
  simpl in *.
  inversion H0; subst.
  constructor.
  eapply IHn2.
  2: eauto.
  omega.
Qed.
Proof.
  induction n1; simpl; intros.
  eapply list_same_skipn; eauto.
  destruct n2; try omega; simpl.
  destruct l; simpl in *.
  constructor.
  eapply IHn1; eauto.
  omega.
Qed.
Proof.
  intros.
  destruct (le_dec off (length l)).
  - rewrite upd_range_eq_upd_range' by omega; unfold upd_range'.
    rewrite skipn_app_r_ge by ( rewrite firstn_length, min_l; omega ).
    rewrite firstn_length, min_l by omega.
    replace (off - off) with 0 by omega.
    simpl.
    apply list_same_app_both.
    apply list_same_repeat.
    replace (off + (length l - off)) with (length l) by omega.
    rewrite skipn_oob by omega.
    constructor.
  - rewrite not_le_minus_0 by auto. rewrite upd_range_0.
    rewrite skipn_oob by omega. constructor.
Qed.
Proof.
  intros.
  rewrite upd_range_eq_upd_range' by omega; unfold upd_range'.
  rewrite skipn_app_r_ge by ( rewrite firstn_length, min_l; omega ).
  rewrite firstn_length, min_l by omega.
  replace (off - off) with 0 by omega.
  simpl.
  apply list_same_app_both.
  apply list_same_repeat.
  auto.
Qed.
Proof.
  induction off; simpl; intros.
  destruct l; simpl in *; try omega.
  inversion H0; auto.
  destruct l; simpl in *; try omega.
  eapply IHoff; eauto.
  omega.
Qed.
Proof.
  intros.
  subst.
  erewrite Nat.div_mod with (x := off) at 1 by eauto.
  rewrite plus_comm, mult_comm.
  erewrite updN_concat; auto.
  erewrite selN_inb; eauto.
  apply Nat.div_lt_upper_bound; auto.
  apply Nat.mod_bound_pos; omega.
Qed.
Proof.
  split; auto using in_or_app.
Qed.
Proof.
  eauto with incl_app.
Qed.
Proof.
  eauto with incl_app.
Qed.
Proof.
  unfold incl; intros.
  eapply in_or_app.
  specialize (H _ H0).
  eapply in_app_or in H.
  intuition.
Qed.
Proof.
  unfold incl; intros.
  apply H.
  eapply in_or_app.
  eapply in_app_or in H0.
  intuition.
Qed.
Proof.
  unfold incl; intros.
  eapply H.
  eapply in_or_app.
  eauto.
Qed.
Proof.
  unfold incl; intros.
  eapply H.
  eapply in_or_app.
  eauto.
Qed.
Proof.
  induction l1; intros; eauto.
  simpl.
  inversion H; subst.
  constructor; eauto.
  contradict H4.
  eapply In_incl; eauto.
  eapply incl_app2r; eauto.
Qed.
Proof.
  induction l; simpl; intros; eauto.
  constructor; eauto.
  inversion H; subst.
  constructor.
  - apply not_in_app in H3; destruct H3.
    intro H'.
    apply in_app_or in H'; destruct H'.
    eauto.
    rewrite cons_app in H3. apply in_app_or in H3. destruct H3.
    simpl in *; intuition eauto.
    eauto.
  - eapply IHl; eauto.
Qed.
Proof.
  induction l2; intros; eauto.
  rewrite app_nil_r; eauto.

  eapply List.NoDup_remove in H; intuition.
  specialize (IHl2 _ _ H2 H0 H1).

  eapply NoDup_remove_inverse; eauto.
  contradict H3.
  eapply In_incl.
  eauto.
  eapply incl_app2l; eauto.
Qed.
Proof.
  induction l1; simpl; intros.
  apply incl_nil.
  apply incl_cons.
  edestruct (H0 a).
  intuition.
  intuition congruence.
  eauto.
  eapply IHl1 with (a := a0).
  intuition.
  intro; intro. apply H0.
  inversion H1; subst; simpl; eauto.
Qed.
Proof.
  unfold incl; intros.
  apply H; intuition.
Qed.
Proof.
  unfold incl; intros.
  intuition.
Qed.
Proof.
  induction l1; simpl; intros.
  - apply incl_nil.
  - intuition.
    apply incl_cons.
    + specialize (H a).
      simpl in *. intuition. exfalso; eauto.
    + eapply IHl1; eauto.
      eapply incl_cons_inv; eauto.
Qed.
Proof.
  induction l1; simpl; intros; eauto.
  repeat rewrite IHl1.
  destruct (E a x); omega.
Qed.
Proof.
  induction l; simpl; intros; eauto.
  destruct (E a0 a); destruct (E a b); subst; try congruence; simpl.
  rewrite IHl by eauto; omega.
  destruct (E b b); try congruence.
  rewrite IHl by eauto; omega.
  destruct (E a b); try congruence.
  rewrite IHl by eauto; omega.
Qed.
Proof.
  intros.
  unfold incl_count in *.
  eapply count_occ_In with (eq_dec := E).
  specialize (H n).
  assert (count_occ E (n :: l2) n  >= 1).
  erewrite count_occ_cons_eq with (l := l2); eauto.
  omega.
  omega.
Qed.
Proof.
  induction l; intros.
  - intro.
    apply H0.
  - apply not_in_cons.
    intuition.
    subst.
    rewrite count_occ_cons_eq in H. omega. auto.
    eapply IHl; eauto.
    destruct (E x a); subst.
    + rewrite count_occ_cons_eq in H. omega. auto.
    + exfalso.
      eapply IHl with (x := x); eauto.
      rewrite count_occ_cons_neq in H; eauto.
Qed.
Proof.
  split.
  + induction l; intros.
    - unfold count_occ.
      omega.
    - destruct (E x a).
      ++ rewrite count_occ_cons_eq; auto.
        subst.
        inversion H; subst.
        assert (count_occ E l a = 0).
        erewrite <- count_occ_not_In; eauto.
        rewrite H0. omega.
      ++ rewrite count_occ_cons_neq; eauto.
        inversion H; subst.
        apply IHl; eauto.
  + induction l.
    - constructor.
    - constructor.
      specialize (H a).
      rewrite count_occ_cons_eq in H; auto.
      eapply incl_count_not_In with (E:=E); eauto.
      omega.
      apply IHl.
      intro.
      destruct (E x a); subst.
      ++
        specialize (H a). 
        rewrite count_occ_cons_eq in H; auto.
        omega.
      ++
        specialize (H x). 
        rewrite count_occ_cons_neq in H; auto.
 Qed.
Proof.
  intros.
  destruct (In_dec E x l).
  + right.
    eapply count_occ_NoDup with (E:= E) (x := x) in H.
    assert (count_occ E l x > 0).
    apply count_occ_In; eauto.
    omega.
  + left.
    apply count_occ_not_In; auto.
Qed.
Proof.
  intros.
  eapply count_occ_NoDup with (E:= E); eauto.
  intro.
  eapply count_occ_NoDup with (E:= E) (x := x) in H0 as H0'; eauto.
  unfold incl_count in H.
  specialize (H x).
  rewrite H0' in H; eauto.
Qed.
Proof.
  unfold incl_count, incl; intros.
  specialize (H a).
  rewrite count_occ_In with (eq_dec := E) in *.
  omega.
Qed.
Proof.
  unfold incl_count, permutation; intros.
  specialize (H x).
  omega.
Qed.
Proof.
  unfold incl_count; intros.
  specialize (H x0).
  simpl.
  destruct (E x x0); omega.
Qed.
Proof.
  unfold incl_count; intros.
  specialize (H x0).
  simpl.
  destruct (E x x0); omega.
Qed.
Proof.
  unfold incl_count in *; intros.
  specialize (H x).
  rewrite cons_app in H.
  rewrite cons_app with (l := l2) in H.
  repeat rewrite count_occ_app in H.
  omega.
Qed.
Proof.
  intros.
  rewrite Hidden_App.app_is in *.
  rewrite app_nil_r in *.
  intros; eauto.
Qed.
Proof.
  rewrite Hidden_App.app_is.
  unfold incl_count; intros.
  specialize (H x0).
  repeat rewrite count_occ_app in *; simpl in *.
  destruct (E x x0); omega.
Qed.
Proof.
  rewrite Hidden_App.app_is.
  unfold incl_count; intros.
  specialize (H x0).
  simpl.
  destruct (E x x0); omega.
Qed.
Proof.
  unfold incl_count; simpl; intros; omega.
Qed.
Proof.
  unfold incl_count; intros.
  specialize (H x).
  specialize (H0 x).
  omega.
Qed.
Proof.
  unfold incl_count; intros.
  omega.
Qed.
Proof.
  induction l; cbn; auto; intros.
  repeat (destruct E; subst; cbn; auto).
  congruence.
Qed.
Proof.
  induction l; intros; subst.
  + simpl in *. auto.
  + destruct (E n  a); subst.
    - rewrite remove_cons_eq; auto.
      eapply count_occ_NoDup with (E := E) (x := a) in H as H'.
      rewrite cons_app in H'.
      rewrite count_occ_app in H'; auto.
      simpl in H'.
      destruct (E a a); subst; try congruence.
      omega.
    - rewrite remove_cons_neq; auto.
      rewrite cons_app.
      rewrite count_occ_app.
      simpl.
      destruct (E a n); subst; try congruence.
      eapply IHl.
      inversion H; auto.
Qed.
Proof. 
  unfold incl_count in *; intros.
  eapply count_occ_NoDup with (E := E) (x := x) in H as H'.    
  eapply count_occ_NoDup with (E := E) (x := x) in H0 as H0'.    
  rewrite cons_app in H0'.
  rewrite count_occ_app in H0'.
  destruct (E n x); subst.
  - simpl in *.
    destruct (E x x); subst; try congruence.
    assert ( count_occ E (remove E x l1) x <= 0).
    eapply count_occ_remove_NoDup_eq; auto.
    omega.
  - simpl in H0'.
    destruct (E n x); subst; try congruence.
    rewrite count_occ_remove_ne; auto.
    specialize (H1 x).
    rewrite cons_app in H1.
    rewrite count_occ_app in H1.
    simpl in H1.
    destruct (E n x); subst; try congruence.  
    omega.
Qed.
Proof.
  unfold incl_count; intros.
  specialize (H x0).
  rewrite cons_app.
  rewrite cons_app with (l := l2).
  repeat rewrite count_occ_app.
  omega.
Qed.
Proof.
  unfold permutation; intros.
  specialize (H x).
  specialize (H0 x).
  omega.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  unfold permutation. cbn; intros.
  destruct E; congruence.
Qed.
Proof.
  unfold incl_count; intros.
  repeat rewrite count_occ_app.
  omega.
Qed.
Proof.
  unfold permutation; intros.
  repeat rewrite count_occ_app.
  omega.
Qed.
Proof.
  unfold permutation; intros.
  repeat rewrite count_occ_app.
  specialize (H x).
  specialize (H0 x).
  omega.
Qed.
Proof.
  unfold permutation.
  intros.
  destruct (E x x0); subst.
  repeat rewrite count_occ_remove_eq; auto.
  repeat rewrite count_occ_remove_ne by auto.
  eauto.
Qed.
Proof.
  unfold permutation.
  intros.
  rewrite count_occ_In in *.
  rewrite <- H. eauto.
Qed.
Proof.
  unfold incl_count; intros.
  repeat rewrite count_occ_app.
  specialize (H x).
  specialize (H0 x).
  omega.
Qed.
Proof.
  unfold NoDupApp; intros; repeat rewrite concat_app in *.
  rewrite app_assoc. apply NoDup_app_comm.
  apply NoDup_3app_rev.
  eauto.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  induction a; simpl; intros.
  apply NoDupApp_cons_nil; eauto.
  constructor.
  - intro H'.
    apply in_app_or in H'; intuition.
    + inversion H0; eauto.
    + eapply H1; eauto.
  - apply IHa; eauto.
    inversion H0; eauto.
Qed.
Proof.
  induction l; simpl; intros.
  firstorder.
  intuition subst.
  unfold NoDupApp in H; simpl in H.
  eapply NoDup_app_l; eauto.
  eapply IHl; eauto.
  unfold NoDupApp in H; simpl in H.
  eapply NoDup_app_r; eauto.
Qed.
Proof.
  intros.
  unfold incl; intros.
  specialize (H0 a).
  edestruct H0; subst; eauto.

  eapply in_app_or in H1.
  eapply in_or_app.
  intuition.

  exfalso. inversion H. eauto.
Qed.
Proof.
  intros.
  unfold incl_count in *; intros.
  specialize (H x0).
  rewrite count_occ_app in *.
  simpl in *.
  destruct (E x x0); omega.
Qed.
Proof.
  destruct x; simpl; intros.
  apply incl_nil.

  induction l; simpl; intros.
  - exfalso; simpl in *; eauto.
  - inversion H; subst.
    apply incl_appl. apply incl_refl.
    apply incl_appr. eauto.
Qed.
Proof.
  induction l1; simpl; intros.
  - apply incl_nil.
  - apply incl_cons_inv' in H; intuition.
    eapply incl_app; eauto.
    eapply incl_concat'; eauto.
Qed.
Proof.
  induction l2; simpl; intros.
  - constructor.
  - apply incl_count_incl in H0 as Hi.
    specialize (Hi a) as H0'; simpl in *; intuition. clear H2.

    apply in_split in H3. destruct H3. destruct H1. subst.
    eapply incl_pick_inv' in H0 as H0'; eauto.
    rewrite cons_app in H. apply NoDupApp_pick in H. simpl in H.
    eapply NoDupApp_cons.

    eapply IHl2; eauto.
    eapply incl_count_tl; eauto.
    unfold NoDupApp in *; simpl in *. eapply NoDup_app_l; eauto.

    intros; intro.
    unfold NoDupApp in *; simpl in *.
    eapply not_In_NoDup_app in H; eauto.
    apply H.

    apply incl_count_incl in H0'.
    eapply incl_concat in H0'. apply H0'. eauto.
Qed.
Proof.
  unfold incl_count.
  intros.
  rewrite (NoDup_count_occ E) in H0.
  rewrite (NoDup_count_occ E); intros.
  specialize (H x).
  specialize (H0 x).
  omega.
Qed.
Proof.
  intros; subst; reflexivity.
Qed.
Proof.
  intros; subst.
  rewrite concat_app; auto.
Qed.
Proof.
  intros; subst.
  rewrite concat_app; auto.
Qed.
Proof.
  reflexivity.
Qed.
Proof.
  intros. simpl. rewrite app_nil_r. auto.
Qed.
Proof.
  intros.
  nodupapp.
  Grab Existential Variables.
  exact eq_nat_dec.
Qed.
Proof.
  intros.
  nodupapp.
  Grab Existential Variables.
  exact eq_nat_dec.
Qed.
Proof.
  intros.
  nodupapp.
Abort.

Proof.
  unfold selN_each.
  induction l; cbn -[skipn]; intros; auto.
  rewrite skipn_selN.
  f_equal.
  eauto.
Qed.
Proof.
  induction l; cbn; intros.
  split; constructor.
  split; intro H'; inversion H'; subst.
  constructor; auto.
  rewrite IHl in *.
  rewrite InA_alt in *.
  intro Ha.
  match goal with H: context [not] |- _ => eapply H end.
  eexists; split; eauto.
  eapply H; auto.
  eapply IHl; eauto.
  constructor.
  rewrite InA_alt in *.
  intro Ha.
  destruct Ha; intuition.
  rewrite H in *.
  subst; auto.
  eapply IHl; auto.
Qed.
Proof.
  induction l; cbn; intros.
  constructor.
  inversion H; subst.
  destruct f; auto.
  constructor; eauto.
  rewrite filter_In.
  intuition.
Qed.
Proof.
  induction a; cbn; intros.
  constructor.
  destruct b.
  constructor.
  intuition try match goal with H : NoDup (_ :: _) |- _ => inversion H; subst end.
  constructor; eauto using in_combine_l.
  constructor; eauto using in_combine_r.
Qed.
Proof.
  induction l; cbn; intros.
  intuition.
  inversion H; subst.
  match goal with H : f _ = f _ |- _ => rename H into Hf end.
  intuition subst; auto.
  rewrite Hf in *.
  exfalso.
  eauto using in_map.
  rewrite <- Hf in *.
  exfalso.
  eauto using in_map.
Qed.
Proof.
  induction l; cbn; intros.
  auto.
  rewrite IHl by auto.
  specialize (H a).
  rewrite H.
  destruct f'; auto.
Qed.
Proof.
  unfold index_of.
  intros.
  destruct ifind_list eqn:H'.
  eapply ifind_list_ok_facts in H'; eauto.
  rewrite Nat.sub_0_r in *.
  intuition.
  match goal with H: _ |- _ => rewrite H end.
  auto.
  omega.
Qed.
Proof.
  unfold index_of.
  intros.
  destruct ifind_list eqn:H'.
  eapply ifind_list_ok_facts in H'.
  rewrite (surjective_pairing p).
  omega.
  destruct H as [x [Ha Hb] ].
  eapply in_selN_exists in Ha.
  destruct Ha as [? [? Ha] ].
  eapply ifind_list_none in H'; eauto.
  rewrite Ha in *.
  congruence.
Unshelve.
  all: eauto.
  destruct p; eauto.
Qed.
Proof.
  unfold inb.
  intros.
  destruct in_dec; intuition congruence.
Qed.
Proof.
  induction t; cbn; auto.
Qed.
Proof.
  induction lt; cbn.
  auto.
  intros.
  destruct selN eqn: Hp.
  remember (split (sort_by_index _ _ _ _ _)) as r.
  rewrite (surjective_pairing r); cbn.
  subst r.
  rewrite IHlt; auto.
  f_equal.
  unfold index_of in *.
  destruct ifind_list eqn:Ha.
  eapply ifind_list_ok_facts in Ha.
  rewrite Nat.sub_0_r in *.
  intuition subst.
  eapply f_equal with (f := snd) in Hp.
  match goal with H: selN _ _ _ = _ |- _ => rewrite H in * end.
  rewrite Hp in *.
  rewrite H0 in *. subst.
  auto.
  specialize (H a) as ?.
  intuition.
  match goal with H: _ |- _ => eapply in_selN_exists in H;
    destruct H as [i ?]; intuition end.
  rewrite split_length_r in *.
  eapply ifind_list_none with (ix := i) in Ha; eauto.
  rewrite <- selN_split_r in *.
  match goal with
    Hf : context [iff],
    Hb : _ = a |- _ => symmetry in Hb; eapply Hf in Hb end.
  rewrite Ha in *.
  congruence.
Unshelve.
  all: eauto.
Qed.
Proof.
  unfold index_of.
  intros.
  destruct ifind_list eqn:H'.
  eapply ifind_list_ok_facts in H'.
  rewrite Nat.sub_0_r in *.
  intuition auto.
  repeat match goal with H: _ |- _ => rewrite H in * end.
  eapply NoDup_In_inj; eauto.
  match goal with H: _ |- _ => rewrite <- H end.
  eapply in_selN; eauto.
  eapply in_selN_exists in H.
  destruct H as [i [? Hs] ].
  eapply ifind_list_none in H'; eauto.
  eapply f_equal with (f := fn) in Hs.
  match goal with H: forall x y, _, H' : f ?a ?b = false |- _ =>
    specialize (H a b) end.
  rewrite Hs in *.
  intuition.
  congruence.
Unshelve.
  all: eauto.
Qed.
Proof.
  unfold index_of.
  intros.
  destruct ifind_list eqn:H'.
  eapply ifind_list_ok_facts in H'.
  rewrite Nat.sub_0_r in *.
  intuition auto.
  repeat match goal with H: _ |- _ => rewrite H in * end.
  congruence.
  match goal with H: _ |- _ => eapply in_selN_exists in H; destruct H end.
  intuition.
  eapply ifind_list_none in H'; eauto.
  match goal with H: forall x y, _, H' : f ?a ?b = false |- _ =>
    specialize (H a b) end.
  match goal with H: _ |- _ => rewrite H in * end.
  intuition congruence.
Unshelve.
  all: eauto.
Qed.
Proof.
  induction t; cbn; intros.
  auto.
  intuition subst.
  left.
  eapply index_of_in_sort_by_index; auto.
  right.
  eapply IHt; auto.
Qed.
Proof.
  induction t; cbn in *.
  intuition auto.
  intros.
  match goal with H: context [iff] |- _ => rename H into Hf end.
  inversion H; subst.
  edestruct (H1 a).
  left; eauto.
  intuition subst.
  eapply in_selN.
  eapply index_of_inb.
  eexists.
  split; try eassumption.
  rewrite Hf; auto.
  match goal with |- ?a = ?b \/ _ => destruct (f a b) eqn:? end.
  left.
  rewrite <- Hf; eauto.
  exfalso; eapply NoDup_selN_index_of_multiple with (fn := snd) (l := l); eauto.
  intro Hs.
  symmetry in Hs.
  rewrite <- Hf in Hs.
  rewrite Hs in *.
  congruence.
  eapply IHt; eauto.
  right.
  eapply IHt; eauto.
Qed.
Proof.
  cbn; intros.
  eapply Permutation.NoDup_Permutation.
  eapply NoDup_map_inv with (f := snd).
  rewrite map_snd_split.
  rewrite sort_by_index_spec; auto.
  intros.
  match goal with H: _, H': _ |- _ => apply H in H'; destruct H' as [? Ha] end.
  eapply in_split_r in Ha.
  auto.
  eauto using Nat.eqb_eq.
  eapply NoDup_filter.
  eauto using NoDup_map_inv.
  intros.
  intuition.
  match goal with H: _ |- _ => eapply in_sort_by_index in H end.
  rewrite filter_In.
  rewrite <- inb_spec. auto.
  eauto.
  eauto using NoDup_map_inv.
  intuition.
  eauto using Nat.eqb_eq.
  rewrite filter_In in *. intuition cbn in *.
  eapply in_sort_by_index'; cbn; auto.
  rewrite inb_spec; eauto.
  eauto using Nat.eqb_eq.
Unshelve.
  all: eauto.
Qed.
Proof.
  cbn; induction l; cbn.
  constructor.
  destruct partition eqn:?.
  destruct f; cbn in *.
  constructor.
  auto.
  eapply Permutation_cons_app.
  eauto.
Qed.
Proof.
  intros.
  pose proof (split_combine s).
  destruct (split s) eqn:Hs; cbn.
  subst s.
  match goal with H: _ |- _ => rewrite <- H end.
  f_equal.
  eapply f_equal with (f := snd) in Hs; cbn in Hs.
  subst.
  eapply sort_by_index_spec; auto.
  intros.
  rewrite List.combine_split; auto.
Qed.
Proof.
  induction l; cbn; intros.
  auto.
  destruct partition eqn:He; cbn.
  rewrite IHl in He.
  destruct f; cbn; congruence.
Qed.
Proof.
  induction l; cbn; intros.
  auto.
  rewrite H by auto.
  destruct f'; cbn.
  f_equal; auto.
  auto.
Qed.
Proof.
  induction a; cbn; intros.
  auto.
  destruct b; cbn in *; try congruence.
  rewrite <- seq_shift.
  erewrite filter_map_ext.
  destruct f; cbn; rewrite map_map.
  f_equal.
  all: eauto.
Qed.
Proof.
  induction a; cbn; intros.
  auto.
  destruct b; cbn in *; try congruence.
  rewrite <- seq_shift.
  erewrite filter_map_ext.
  destruct f; cbn; rewrite map_map.
  f_equal.
  all: eauto.
Qed.
Proof.
  induction l; cbn; intros.
  auto.
  rewrite <- seq_shift.
  erewrite filter_map_ext.
  destruct f; cbn.
  f_equal.
  all: autorewrite with lists; eauto.
Qed.
Proof.
  intros.
  apply Permutation.NoDup_Permutation; auto using NoDup_filter.
  intros.
  rewrite filter_In.
  unfold inb.
  destruct in_dec; intuition.
  congruence.
Qed.