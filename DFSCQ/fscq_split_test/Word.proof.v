Proof.
  induction w. auto. unfold wordToNat. simpl. rewrite mult_comm. reflexivity.
Qed.
Proof.
  induction n; simpl; intuition; rethink.
Qed.
Proof.
  induction n; simpl; intuition; rewrite <- plus_n_Sm; rethink.
Qed.
Proof.
  induction n; simpl; intuition; rewrite <- plus_n_Sm; f_equal; rethink.
Qed.
Proof.
  induction n; simpl; intuition; f_equal; rethink.
Qed.
Proof.
  induction w; rewrite wordToNat_wordToNat'; intuition; f_equal; unfold natToWord, wordToNat'; fold natToWord; fold wordToNat';
    destruct b; f_equal; autorewrite with div2; intuition.
Qed.
Proof.
  induction a; destruct b; try now firstorder; simpl.
  repeat rewrite Nat.add_0_r.
  rewrite Nat.mul_1_r; auto.
  simpl.
  repeat rewrite Nat.add_0_r.
  rewrite IHa.
  simpl.
  repeat rewrite Nat.add_0_r.
  rewrite Nat.mul_add_distr_r; auto.
Qed.
Proof.
  intros.
  rewrite pow2_add_mul.
  apply Nat.mul_lt_mono_nonneg; omega.
Qed.
Proof.
  intros.
  replace c with (a + (c - a)) by omega.
  apply mult_pow2_bound; auto.
Qed.
Proof.
  induction c; intros.
  rewrite Nat.mul_1_r; auto.
  rewrite Nat.mul_succ_r.
  apply lt_plus_trans.
  apply IHc; auto.
Qed.
Proof.
  intros.
  replace c with (S (c - 1)) by omega.
  apply lt_mul_mono'; auto.
Qed.
Proof.
  induction sz; simpl; omega.
Qed.
Proof.
  intros.
  induction n.
  simpl; omega.
  remember (S n); simpl.
  omega.
Qed.
Proof.
  induction n; firstorder. omega.
Qed.
Proof.
  induction sz; simpl; auto.
  repeat rewrite Nat.add_0_r.
  rewrite pow2_add_mul.
  repeat rewrite mul2_add.
  pose proof (zero_lt_pow2 sz).
  omega.
Qed.
Proof.
  intros.
  replace b with (a + (b - a)) by omega.
  rewrite pow2_add_mul.
  apply lt_mul_mono; auto.
  pose proof (zero_lt_pow2 (b - a)).
  omega.
Qed.
Proof.
  intros.
  generalize dependent n; intros.
  induction m; simpl.
  intros. inversion H0.
  unfold lt in H0.
  rewrite Nat.add_0_r.
  inversion H0.
  apply Nat.lt_add_pos_r.
  apply zero_lt_pow2.
  apply Nat.lt_trans with (pow2 m).
  apply IHm.
  exact H2.
  apply Nat.lt_add_pos_r.
  apply zero_lt_pow2.
Qed.
Proof.
  induction sz; simpl; intuition.
Qed.
Proof.
  auto.
Qed.
  Proof.
    induction n; simpl; intuition; apply PH; intuition.
    elimtype False; omega.
  Qed.
  Proof.
    intros; eapply strong'; eauto.
  Qed.
Proof.
  induction n using strong; simpl; intuition.

  destruct n; simpl in *; intuition.
  destruct n; simpl in *; intuition.
  do 2 f_equal.
  replace (div2 n + S (div2 n + 0)) with (S (div2 n + (div2 n + 0))); auto.
Qed.
Proof.
  induction n using strong; simpl; intuition.

  destruct n; simpl in *; intuition.
  destruct n; simpl in *; intuition.
  f_equal.
  replace (div2 n + S (div2 n + 0)) with (S (div2 n + (div2 n + 0))); auto.
Qed.
Proof.
  induction sz; simpl; intuition; repeat rewrite untimes2.

  exists w; intuition.

  case_eq (mod2 w); intro Hmw.

  specialize (IHsz (div2 w)); firstorder.
  simpl wordToNat.
  rewrite wordToNat_wordToNat' in *.
  exists x; intuition.
  rewrite mult_assoc.
  rewrite (mult_comm x 2).
  rewrite mult_comm. simpl mult at 1.
  rewrite (plus_Sn_m (2 * wordToNat' (natToWord sz (div2 w)))).
  rewrite <- mult_assoc.
  rewrite <- mult_plus_distr_l.
  rewrite H; clear H.
  symmetry; apply div2_odd; auto.

  specialize (IHsz (div2 w)); firstorder.
  simpl wordToNat.
  exists x; intuition.
  rewrite mult_assoc.
  rewrite (mult_comm x 2).
  rewrite <- mult_assoc.
  rewrite mult_comm.
  rewrite <- mult_plus_distr_l.
  rewrite H; clear H.
  symmetry; apply div2_even; auto.
Qed.
Proof.
  intros; destruct (wordToNat_natToWord' sz w) as [k]; exists k; intuition.
Qed.
Proof.
  intuition.
  apply (f_equal (@whd _)) in H0; tauto.
  apply (f_equal (@wtl _)) in H0; tauto.
Qed.
Proof.
  destruct a; eauto.
Qed.
Proof.
  intros; repeat eexists; apply (shatter_word a).
Qed.
Proof.
  intros; apply (shatter_word a).
Qed.
Proof.
  firstorder.
Qed.
Proof.
  induction x; simpl; intros.
  { split; auto. }
  { rewrite (shatter_word y) in *. simpl in *.
    case_eq (eqb b (whd y)); intros.
    case_eq (weqb x (wtl y)); intros.
    split; auto; intros. rewrite eqb_true_iff in H. f_equal; eauto. eapply IHx; eauto.
    split; intros; try congruence. inversion H1; clear H1; subst.
    eapply inj_pair2_eq_dec in H4. eapply IHx in H4. congruence.
    eapply Peano_dec.eq_nat_dec.
    split; intros; try congruence.
    inversion H0. apply eqb_false_iff in H. congruence. }
Qed.    
Proof.
  intros.
  destruct ab.
  destruct bc.
  rewrite (UIP_dec eq_nat_dec (eq_trans eq_refl eq_refl) eq_refl).
  simpl.
  auto.
Qed.
Proof.
  intros; congruence.
Qed.
Proof.
  intros.
  destruct Heq.
  rewrite (UIP_dec eq_nat_dec (eq_rect_word_offset_helper offset eq_refl) eq_refl).
  reflexivity.
Qed.
Proof.
  intros; congruence.
Qed.
Proof.
  intros.
  destruct Heq.
  rewrite (UIP_dec eq_nat_dec (eq_rect_word_mult_helper scale eq_refl) eq_refl).
  reflexivity.
Qed.
Proof.
  intros.
  destruct H.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.
Proof.
  intros.
  rewrite eq_rect_word_match.
  generalize dependent w.
  remember Heq as Heq'. clear HeqHeq'.
  generalize dependent Heq'.
  replace (n') with (n) by omega.
  intros. rewrite <- (eq_rect_eq_dec eq_nat_dec). reflexivity.
Qed.
Proof.
  intros.
  repeat match goal with
           | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
         end.
  generalize dependent w; clear.
  intros.
  generalize Heq Heq'.
  subst.
  intros.
  rewrite (UIP_dec eq_nat_dec Heq' (refl_equal _)).
  rewrite (UIP_dec eq_nat_dec Heq0 (refl_equal _)).
  reflexivity.
Qed.
Proof.
  induction sz1; shatterer.
Qed.
Proof.
  induction sz1; shatterer.
Qed.
Proof.
  induction sz1; shatterer.
Qed.
Proof.
  induction w1; simpl; intuition.

  rewrite (UIP_dec eq_nat_dec Heq (refl_equal _)); reflexivity.

  rewrite (IHw1 _ _ _ _ (plus_assoc _ _ _)); clear IHw1.
  repeat match goal with
           | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
         end.  
  generalize dependent (combine w1 (combine w2 w3)).
  rewrite plus_assoc; intros.
  rewrite (UIP_dec eq_nat_dec e (refl_equal _)).
  rewrite (UIP_dec eq_nat_dec Heq0 (refl_equal _)).
  reflexivity.
Qed.
Proof.
  induction n1; simpl; intuition.

  f_equal.
  apply whd_match.
  assert (n1 + n2 + n3 = n1 + (n2 + n3)) as Heq' by omega.
  rewrite IHn1 with (Heq:=Heq').
  f_equal.
  apply wtl_match.
Qed.
Proof.
  induction n1; simpl; intuition.

  rewrite (UIP_dec eq_nat_dec Heq (refl_equal _)); reflexivity.

  rewrite (IHn1 _ _ (plus_assoc _ _ _)).
  f_equal.
  apply wtl_match.
Qed.
Proof.
  induction n1; simpl; intros.

  rewrite (UIP_dec eq_nat_dec Heq (refl_equal _)).
  reflexivity.

  rewrite (shatter_word w).
  simpl.
  assert (n1 + (n2 + n3) = n1 + n2 + n3) as Heq' by omega.
  rewrite <- wtl_match with (Heq':=Heq').
  rewrite <- IHn1.
  f_equal.
Qed.
Proof.
  induction n1; simpl; intros.

  rewrite (UIP_dec eq_nat_dec Heq (refl_equal _)).
  reflexivity.

  rewrite (shatter_word w).
  simpl.
  assert (n1 + n2 + n3 = n1 + (n2 + n3)) as Heq' by omega.
  rewrite <- wtl_match with (Heq':=Heq').
  rewrite <- IHn1.
  f_equal.
Qed.
Proof.
  intros.
  replace w with WO.
  auto.
  rewrite word0; auto.
Qed.
Proof.
  destruct n; intros; subst;
    eq_rect_simpl; auto.
Qed.
Proof.
  induction a; simpl; intros.
  eq_rect_simpl; auto.
  erewrite WS_eq_rect.
  erewrite IHa.
  auto.

  Grab Existential Variables.
  omega.
Qed.
Proof.
  induction w; intros.
  - replace v with WO; auto.
  - simpl; rewrite IHw.
    erewrite WS_eq_rect.
    reflexivity.
Qed.
Proof.
  intros.
  generalize Heq.
  replace (n + 0) with n by omega.
  intros.
  f_equal.
  eq_rect_simpl.
  reflexivity.
Qed.
Proof.
  intros.
  generalize dependent Heq.
  rewrite <- Heq'; simpl; intros.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.
Proof.
  intros.
  generalize Heq.
  replace (n * 1) with n by auto.
  intros.
  eq_rect_simpl.
  reflexivity.
Qed.
Proof.
  intros.
  generalize Heq.
  rewrite <- Heq'.
  intros. eq_rect_simpl.
  reflexivity.
Qed.
Proof.
  intros.
  induction n; intros.
  shatterer.
  simpl.
  erewrite wtl_eq_rect.
  rewrite IHn.
  rewrite whd_eq_rect.
  simpl.
  shatterer.

  Grab Existential Variables.
  omega.
Qed.
Proof.
  intros.
  simpl.
  eq_rect_simpl.
  reflexivity.
Qed.
Proof.
  induction n1; simpl; intros.

  rewrite (UIP_dec eq_nat_dec Heq (refl_equal _)).
  apply combine_split.

  rewrite (shatter_word w) in *.
  simpl.
  eapply trans_eq; [ | apply IHn1 with (Heq := plus_assoc _ _ _) ]; clear IHn1.
  repeat f_equal.
  repeat match goal with
           | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
         end.
  simpl.
  generalize dependent w.
  rewrite plus_assoc.
  intros.
  rewrite (UIP_dec eq_nat_dec e (refl_equal _)).
  rewrite (UIP_dec eq_nat_dec Heq0 (refl_equal _)).
  reflexivity.
Qed.
Proof.
  intros.
  generalize (plus_reg_l n2' n2 n1 Heq); intros.
  generalize dependent Heq.
  generalize dependent w2.
  rewrite e; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.
Proof.
  intros.
  erewrite combine_assoc, eq_rect_word_match.
  reflexivity.
Qed.
Proof.
  intros; omega.
Qed.
Proof.
  intros.
  generalize (eq_rect_split2_helper n1 Heq); intros.
  generalize dependent Heq.
  generalize dependent w.
  assert (n2' = n2) as H' by omega.
  generalize dependent e.
  rewrite H'; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.
Proof.
  intros.
  assert (H' := Heq).
  generalize dependent w.
  generalize dependent Heq.
  generalize dependent Heq2.
  rewrite H'; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.
Proof.
  intros.
  assert (n1 = n1') as H' by omega.
  generalize dependent w.
  generalize dependent Heq.
  rewrite H'; intros.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.
Proof.
  intros.
  assert (n2 = n2') by omega.
  generalize dependent Heq.
  generalize dependent w.
  rewrite <- H; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  apply combine_split.
Qed.
Proof.
  intros; omega.
Qed.
Proof.
  intros; omega.
Qed.
Proof.
  intros.
  generalize (eq_rect_split1_helper n2 Heq); intros.
  generalize dependent Heq.
  generalize dependent w.
  assert (n1' = n1) as H' by omega.
  generalize dependent e.
  rewrite H'; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.
Proof.
  intros.
  generalize dependent w.
  generalize dependent Heq1.
  rewrite Heq; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.
Proof. intros. subst. reflexivity. Qed.

Proof.
  intros a a' b H.
  subst a'; intros; eq_rect_simpl; auto.
Qed.
Proof.
  intros.
  assert (n2 = n2') as H' by omega.
  generalize dependent w.
  generalize dependent Heq.
  rewrite H'; intros.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.
Proof. intros; subst. apply Nat.mul_add_distr_r. Qed.

Fact eq_rect_combine_dist_helper2 : forall a b c d, b * c = d -> a * c + d = (a + b) * c.
Proof. intros; subst. symmetry; apply Nat.mul_add_distr_r. Qed.

Proof.
  intros.
  subst d.
  rewrite combine_split.
  eq_rect_simpl.
  generalize dependent w.
  generalize dependent H2.
  rewrite H1.
  intros.
  eq_rect_simpl; auto.
Qed.
Proof.
  intros a b c H.
  rewrite H.
  reflexivity.
Qed.
Proof. intros a b H. rewrite H. auto. Qed.

Proof.
  induction sz1; auto; simpl; intros.
  f_equal. eauto.
Qed.
Proof.
  induction sz1; auto.
Qed.
Proof.
  induction sz1; simpl; intros.
  - rewrite (word0 a) in *.
    rewrite (word0 c) in *.
    simpl in *.
    intuition.
  - rewrite (shatter_word a) in *.
    rewrite (shatter_word c) in *.
    simpl in *.
    inversion H.
    apply (inj_pair2_eq_dec _ eq_nat_dec) in H2.
    destruct (IHsz1 _ _ _ _ _ H2).
    intuition.
    f_equal; auto.
Qed.
Proof.
  induction sz1; auto.
  unfold wzero in *.
  intros; simpl; f_equal; auto.
Qed.
Proof.
  induction sz1; auto.
  intros; simpl; f_equal; auto.
Qed.
Proof.
  induction w; intuition.
  destruct b; unfold wordToN, wordToNat; fold wordToN; fold wordToNat.

  rewrite N_of_S.
  rewrite N_of_mult.
  rewrite <- IHw. 
  rewrite Nmult_comm.
  reflexivity.

  rewrite N_of_mult.
  rewrite <- IHw.
  rewrite Nmult_comm.
  reflexivity.
Qed.
Proof.
  induction n using strong; intros.
  destruct n; simpl in *.
  elimtype False; omega.
  destruct n; simpl in *; auto.
  destruct k; simpl in *.
  discriminate.
  apply H with k; auto.
Qed.
Proof.
  unfold wzero; induction sz; simpl; intuition.
  congruence.
Qed.
Proof.
  induction p; destruct sz; simpl; intuition; f_equal; try rewrite wzero'_def in *.
  
  rewrite ZL6.
  destruct (ZL4 p) as [? Heq]; rewrite Heq; simpl.
  replace (x + S x) with (S (2 * x)) by omega.
  symmetry; apply mod2_S_double.

  rewrite IHp.
  rewrite ZL6.
  destruct (nat_of_P p); simpl; intuition.
  replace (n + S n) with (S (2 * n)) by omega.
  rewrite div2_S_double; auto.

  unfold nat_of_P; simpl.
  rewrite ZL6.
  replace (nat_of_P p + nat_of_P p) with (2 * nat_of_P p) by omega.
  symmetry; apply mod2_double.

  rewrite IHp.
  unfold nat_of_P; simpl.
  rewrite ZL6.
  replace (nat_of_P p + nat_of_P p) with (2 * nat_of_P p) by omega.
  rewrite div2_double.
  auto.
  auto.
Qed.
Proof.
  destruct n; simpl; intuition; try rewrite wzero'_def in *.
  auto.
  apply posToWord_nat.
Qed.
Proof.
  unfold wplusN, wplus, wordBinN, wordBin; intros.

  repeat rewrite wordToN_nat; repeat rewrite NToWord_nat.
  rewrite nat_of_Nplus.
  repeat rewrite nat_of_N_of_nat.
  reflexivity.
Qed.
Proof.
  unfold wmultN, wmult, wordBinN, wordBin; intros.

  repeat rewrite wordToN_nat; repeat rewrite NToWord_nat.
  rewrite nat_of_Nmult.
  repeat rewrite nat_of_N_of_nat.
  reflexivity.
Qed.
Proof.
  induction n; simpl; intuition.
  rewrite <- IHn; clear IHn.
  case_eq (Npow2 n); intuition.
Qed.
Proof.
  intro n. apply nat_of_N_eq. rewrite Nat2N.id. apply Npow2_nat.
Qed.
Proof.
  unfold wnegN, wneg; intros.
  repeat rewrite wordToN_nat; repeat rewrite NToWord_nat.
  rewrite nat_of_Nminus.
  do 2 f_equal.
  apply Npow2_nat.
  apply nat_of_N_of_nat.
Qed.
Proof.
  intros; unfold wminusN, wminus; rewrite wneg_alt; apply wplus_alt.
Qed.
Proof.
  intros; rewrite wplus_alt; unfold wplusN, wordBinN; intros.
  rewrite roundTrip_0; apply natToWord_wordToNat.
Qed.
Proof.
  intros; repeat rewrite wplus_alt; unfold wplusN, wordBinN; f_equal; auto.
Qed.
Proof.
  induction n using strong; intros.

  do 2 (destruct n; simpl in *; repeat rewrite untimes2 in *; intuition).

  destruct k; simpl in *; intuition.

  destruct k; simpl; intuition.
  rewrite <- plus_n_Sm.
  repeat rewrite untimes2 in *.
  simpl; auto.
  apply H; omega.
Qed.
Proof.
  induction n using strong; intros.

  do 2 (destruct n; simpl in *; intuition; repeat rewrite untimes2 in *).
  destruct k; simpl in *; intuition.

  destruct k; simpl in *; intuition.
  rewrite <- plus_n_Sm.
  apply H; omega.
Qed.
Proof.
  intros; case_eq (mod2 n); intro Heq.

  rewrite (div2_odd _ Heq) in H.
  omega.

  rewrite (div2_even _ Heq) in H.
  omega.
Qed.
Proof.
  induction sz; simpl; intuition; repeat rewrite untimes2 in *; f_equal.

  rewrite mult_assoc.
  rewrite (mult_comm k).
  rewrite <- mult_assoc.
  apply drop_mod2.
  rewrite mult_assoc.
  rewrite (mult_comm 2).
  rewrite <- mult_assoc.
  auto.

  rewrite <- (IHsz (div2 n) k).
  rewrite mult_assoc.
  rewrite (mult_comm k).
  rewrite <- mult_assoc.
  rewrite div2_minus_2.
  reflexivity.  
  rewrite mult_assoc.
  rewrite (mult_comm 2).
  rewrite <- mult_assoc.
  auto.
  
  apply div2_bound.
  rewrite mult_assoc.
  rewrite (mult_comm 2).
  rewrite <- mult_assoc.
  auto.
Qed.
Proof.
  intros.
  destruct n; auto; destruct n; auto.
Qed.
Proof.
  intros.
  induction n; auto.
  rewrite mod2_S_S.
  destruct (mod2 n); replace (mod2 (S n)); auto.
Qed.
Proof.
  intros.
  do 2 rewrite mod2_S_not.
  rewrite H.
  auto.
Qed.
Proof.
  intros.
  induction n.
  simpl.
  rewrite Nat.add_0_r.
  replace (k + k) with (2 * k) by omega.
  apply mod2_double.
  replace (S n + 2 * k) with (S (n + 2 * k)) by omega.
  apply mod2_S_eq; auto.
Qed.
Proof.
  induction n; intros.
  simpl.
  rewrite Nat.add_0_r.
  replace (k + k) with (2 * k) by omega.
  apply div2_double.
  replace (S n + 2 * k) with (S (n + 2 * k)) by omega.
  destruct (Even.even_or_odd n).
  - rewrite <- even_div2.
    rewrite <- even_div2 by auto.
    apply IHn.
    apply Even.even_even_plus; auto.
    apply Even.even_mult_l; repeat constructor.

  - rewrite <- odd_div2.
    rewrite <- odd_div2 by auto.
    rewrite IHn.
    omega.
    apply Even.odd_plus_l; auto.
    apply Even.even_mult_l; repeat constructor.
Qed.
Proof.
  induction sz; simpl; intuition; repeat rewrite untimes2 in *; f_equal.
  - rewrite mult_assoc.
    rewrite (mult_comm k).
    rewrite <- mult_assoc.
    apply drop_mod2_add.

  - rewrite <- (IHsz (div2 n) k).
    rewrite mult_assoc.
    rewrite (mult_comm k).
    rewrite <- mult_assoc.
    rewrite div2_plus_2.
    reflexivity.
Qed.
Proof.
  intros; repeat rewrite wplus_alt; unfold wplusN, wordBinN; intros.

  repeat match goal with
           | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
             let Heq := fresh "Heq" in
               destruct (wordToNat_natToWord sz w) as [? [Heq ?]]; rewrite Heq
         end.

  replace (wordToNat x + wordToNat y - x1 * pow2 sz + wordToNat z)
    with (wordToNat x + wordToNat y + wordToNat z - x1 * pow2 sz) by auto.
  replace (wordToNat x + (wordToNat y + wordToNat z - x0 * pow2 sz))
    with (wordToNat x + wordToNat y + wordToNat z - x0 * pow2 sz) by auto.
  repeat rewrite drop_sub; auto.
Qed.
Proof.
  induction sz; simpl in *; intuition.
Qed.
Proof.
  intros. rewrite wordToNat_wordToNat'.
  destruct b; simpl.

  rewrite untimes2.
  case_eq (2 * wordToNat x); intuition.
  eapply mod2_S; eauto.
  rewrite <- (mod2_double (wordToNat x)); f_equal; omega.
Qed.
Proof.
  destruct b; rewrite wordToNat_wordToNat'; unfold wordToNat'; fold wordToNat'.
  apply div2_S_double.
  apply div2_double.
Qed.
Proof.
  intros; rewrite wmult_alt; unfold wmultN, wordBinN; intros.
  destruct sz; simpl.
  rewrite (shatter_word x); reflexivity.
  rewrite roundTrip_0; simpl.
  rewrite plus_0_r.
  rewrite (shatter_word x).
  f_equal.

  apply mod2_WS.

  rewrite div2_WS.
  apply natToWord_wordToNat.
Qed.
Proof.
  intros; repeat rewrite wmult_alt; unfold wmultN, wordBinN; auto with arith.
Qed.
Proof.
  intros.
  rewrite wmult_comm.
  apply wmult_unit_l.
Qed.
Proof.
  intros; repeat rewrite wmult_alt; unfold wmultN, wordBinN; intros.

  repeat match goal with
           | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
             let Heq := fresh "Heq" in
               destruct (wordToNat_natToWord sz w) as [? [Heq ?]]; rewrite Heq
         end.

  rewrite mult_minus_distr_l.
  rewrite mult_minus_distr_r.
  rewrite (mult_assoc (wordToNat x) x0).
  rewrite <- (mult_assoc x1).
  rewrite (mult_comm (pow2 sz)).
  rewrite (mult_assoc x1).
  repeat rewrite drop_sub; auto with arith.
  rewrite (mult_comm x1).
  rewrite <- (mult_assoc (wordToNat x)).
  rewrite (mult_comm (wordToNat y)).
  rewrite mult_assoc.
  rewrite (mult_comm (wordToNat x)).
  repeat rewrite <- mult_assoc.
  auto with arith.
  repeat rewrite <- mult_assoc.
  auto with arith.
Qed.
Proof.
  intros; repeat rewrite wmult_alt; repeat rewrite wplus_alt; unfold wmultN, wplusN, wordBinN; intros.

  repeat match goal with
           | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
             let Heq := fresh "Heq" in
               destruct (wordToNat_natToWord sz w) as [? [Heq ?]]; rewrite Heq
         end.

  rewrite mult_minus_distr_r.
  rewrite <- (mult_assoc x0).
  rewrite (mult_comm (pow2 sz)).
  rewrite (mult_assoc x0).

  replace (wordToNat x * wordToNat z - x1 * pow2 sz +
    (wordToNat y * wordToNat z - x2 * pow2 sz))
    with (wordToNat x * wordToNat z + wordToNat y * wordToNat z - x1 * pow2 sz - x2 * pow2 sz).
  repeat rewrite drop_sub; auto with arith.
  rewrite (mult_comm x0).
  rewrite (mult_comm (wordToNat x + wordToNat y)).
  rewrite <- (mult_assoc (wordToNat z)).
  auto with arith.
  generalize dependent (wordToNat x * wordToNat z).
  generalize dependent (wordToNat y * wordToNat z).
  intros.
  omega.
Qed.
Proof.
  reflexivity.
Qed.
Proof.
  induction w; simpl; intuition.
  destruct b; simpl; omega.
Qed.
Proof.
  apply wordToNat_bound.
Qed.
Proof.
  intros.
  unfold goodSize.
  induction sz.
  shatterer.
  simpl.
  shatterer.
  specialize (IHsz (wtl w)).
  destruct (whd w).
  simpl.
  omega.
  simpl.
  omega.
Qed.
Proof.
  intros.
  unfold goodSize in *.
  apply le_lt_trans with n2; omega.
Qed.
Proof.
  intros.
  unfold goodSize.
  eapply le_lt_trans.
  eassumption.
  apply wordToNat_bound.
Qed.
Proof.
  intros.
  eapply goodSize_word_bound; eauto.
Qed.
Proof.
  intros; eapply goodSize_trans with (n2 := n); eauto; omega.
Qed.
Proof.
  intros.
  eapply goodSize_bound.
  rewrite H.
  auto.
Qed.
Proof.
  intros; eapply goodSize_trans with (n2 := a + b); auto; omega.
Qed.
Proof.
  intros; eapply goodSize_trans with (n2 := a + b); auto; omega.
Qed.
Proof.
  induction sz; simpl; intuition.

  generalize (div2_double (pow2 sz)); simpl; intro Hr; rewrite Hr; clear Hr.
  f_equal.
  generalize (mod2_double (pow2 sz)); auto.
  auto.
Qed.
Proof.
  intros; rewrite wneg_alt; rewrite wplus_alt; unfold wnegN, wplusN, wzero, wordBinN; intros.

  repeat match goal with
           | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
             let Heq := fresh "Heq" in
               destruct (wordToNat_natToWord sz w) as [? [Heq ?]]; rewrite Heq
         end.
  
  replace (wordToNat x + (pow2 sz - wordToNat x - x0 * pow2 sz))
    with (pow2 sz - x0 * pow2 sz).
  rewrite drop_sub; auto with arith.
  apply natToWord_pow2.
  generalize (wordToNat_bound x).
  omega.
Qed.
Proof.
  eapply weqb_true_iff.
Qed.
Proof.
  intros.
  rewrite (shatter_word w), (shatter_word w').
  auto.
Qed.
Proof.
  induction sz1; intros; auto.
  simpl.
  f_equal.
  rewrite (shatter_word w), (shatter_word w'); auto.
  rewrite <- IHsz1, bitwp_wtl.
  reflexivity.
Qed.
Proof.
  induction sz1; intros; auto.
  simpl; rewrite <- IHsz1, bitwp_wtl.
  reflexivity.
Qed.
Proof.
  induction sz1; intros; rewrite (shatter_word wa), (shatter_word wa'); simpl; f_equal; auto.
Qed.
Proof.
  intros a b H; subst a.
  intros; eq_rect_simpl; reflexivity.
Qed.
Proof.
  intros a b H1; subst a.
  intros; eq_rect_simpl; reflexivity.
Qed.
Proof.
  intros a b H.
  subst a; intros; eq_rect_simpl; auto.
Qed.
Proof.
  unfold wnot'.
  induction sz; intros w; shatterer.
Qed.
Proof.
  intros.
  repeat rewrite wnot_wnot'_equiv.
  unfold wnot'.
  erewrite <- split1_combine with (w := wones _).
  rewrite <- split1_bitwp_dist, combine_wones.
  reflexivity.
Qed.
Proof.
  intros.
  repeat rewrite wnot_wnot'_equiv.
  unfold wnot'.
  erewrite <- split2_combine with (z := wones _).
  rewrite <- split2_bitwp_dist, combine_wones.
  reflexivity.
Qed.
Proof.
  intros.
  repeat rewrite wnot_wnot'_equiv.
  unfold wnot'.
  rewrite <- combine_wones, combine_bitwp.
  reflexivity.
Qed.
Proof.
  induction sz; simpl; f_equal; eauto.
Qed.
Proof.
  induction sz; simpl; f_equal; try rewrite IHsz; eauto.
Qed.
Proof.
  intros.
  subst b; eq_rect_simpl; auto.
Qed.
Proof.
  unfold wzero, wor; induction x; simpl; intuition congruence.
Qed.
Proof.
  unfold wor; induction x; intro y; rewrite (shatter_word y); simpl; intuition; f_equal; auto with bool.
Qed.
Proof.
  unfold wor; induction x; intro y; rewrite (shatter_word y); simpl; intuition; f_equal; auto with bool.
Qed.
Proof.
  unfold wand; induction x; simpl; intuition congruence.
Qed.
Proof.
  unfold wzero, wand; induction x; simpl; intuition congruence.
Qed.
Proof.
  unfold wand; induction x; intro y; rewrite (shatter_word y); simpl; intuition; f_equal; auto with bool.
Qed.
Proof.
  unfold wand; induction x; intro y; rewrite (shatter_word y); simpl; intuition; f_equal; auto with bool.
Qed.
Proof.
  unfold wand, wor; induction x; intro y; rewrite (shatter_word y); intro z; rewrite (shatter_word z); simpl; intuition; f_equal; auto with bool.
  destruct (whd y); destruct (whd z); destruct b; reflexivity.
Qed.
Proof.
  unfold wor; induction sz; intros; simpl; auto.
  rewrite IHsz; auto.
Qed.
Proof.
  unfold wor; induction sz; shatterer.
Qed.
Proof.
  unfold wand; induction sz; shatterer.
Qed.
Proof.
  intros. rewrite <- wzero'_def.
  unfold wand; induction sz; shatterer.
Qed.
Proof.
  unfold wxor; induction sz; shatterer.
Qed.
Proof.
  unfold wxor; induction sz; shatterer; destruct (whd w); auto.
Qed.
Proof.
  unfold wxor; induction sz. shatterer.
  intros. rewrite (shatter_word w1), (shatter_word w2).
  simpl.
  rewrite xorb_comm, IHsz.
  reflexivity.
Qed.
Proof.
  unfold wxor.
  induction sz; intros; rewrite (shatter_word w1), (shatter_word w2), (shatter_word w3); auto.
  simpl; f_equal.
  rewrite xorb_assoc_reverse; auto.
  rewrite IHsz.
  reflexivity.
Qed.
Proof.
  intros.
  compute [wone natToWord wor]. simpl.
  fold natToWord.
  change (natToWord sz 0) with (wzero sz).
  rewrite orb_true_r.
  rewrite wor_comm, wor_wzero.
  reflexivity.
Qed.
Proof.
  intros.
  compute [wone natToWord wand]. simpl.
  fold natToWord.
  change (natToWord sz 0) with (wzero sz).
  rewrite andb_true_r.
  rewrite wand_comm, wand_wzero.
  reflexivity.
Qed.
Proof.
  intros.
  compute [wone natToWord wxor]. simpl.
  fold natToWord.
  change (natToWord sz 0) with (wzero sz).
  rewrite xorb_true_r.
  rewrite wxor_comm, wxor_wzero.
  reflexivity.
Qed.
Proof.
  intros; intro; subst.
  unfold wminus in H.
  rewrite wminus_inv in H.
  tauto.
Qed.
Proof.
  intros.
  case_eq (wlt_dec l r); intros;
    try contradiction;
    auto.
Qed.
Proof.
  intros.
  case_eq (wlt_dec r l); intros;
    try contradiction;
    auto.
Qed.
Proof.
  unfold wlt, N.lt. intros. intro. rewrite <- Ncompare_antisym in H0. rewrite H in H0. simpl in *. congruence.
Qed.
Proof.
  intros; subst. unfold wlt, N.lt. rewrite N.compare_refl. congruence.
Qed.
Proof.
  induction a; intro b0; rewrite (shatter_word b0); intuition.
  destruct b; destruct (whd b0); intros; unfold wordToN in H; fold wordToN in H.
  f_equal. eapply IHa. eapply N.succ_inj in H.
  destruct (wordToN a); destruct (wordToN (wtl b0)); simpl in H; try congruence.
  destruct (wordToN (wtl b0)); destruct (wordToN a); inversion H.
  destruct (wordToN (wtl b0)); destruct (wordToN a); inversion H.
  f_equal. eapply IHa. 
  destruct (wordToN a); destruct (wordToN (wtl b0)); simpl in *; try congruence.
Qed.
Proof.
  intros; apply wordToN_inj.
  repeat rewrite wordToN_nat.
  apply Nat2N.inj_iff; auto.
Qed.
Proof.
  intros.
  transitivity (b1 ^+ wzero _).
  rewrite wplus_comm. rewrite wplus_unit. auto.
  transitivity (b1 ^+ (a ^+ b2)). congruence.
  rewrite wplus_assoc.
  rewrite (wplus_comm b1). rewrite H. rewrite wplus_unit. auto.
Qed.
Proof.
  intros. destruct (weq (wneg b) (wneg a)).
  transitivity (a ^+ (^~ b ^+ b)).
  rewrite (wplus_comm (^~ b)). rewrite wminus_inv. 
  rewrite wplus_comm. rewrite wplus_unit. auto.
  rewrite e. rewrite wplus_assoc. rewrite wminus_inv. rewrite wplus_unit. auto.
  unfold wminus in H.
  generalize (unique_inverse a (wneg a) (^~ b)).
  intros. elimtype False. apply n. symmetry; apply H0.
  apply wminus_inv.
  auto.
Qed.
Proof.
  intros; destruct (wlt_dec b a); auto.
  elimtype False. apply H0. unfold wlt, N.lt in *.
  eapply wordToN_inj. eapply Ncompare_eq_correct.
  case_eq ((wordToN a ?= wordToN b)%N); auto; try congruence.
  intros. rewrite <- Ncompare_antisym in n. rewrite H1 in n. simpl in *. congruence.
Qed.
Proof.
  intros; destruct (weq a b); try solve [ elimtype False; auto ].
  f_equal. 
  eapply UIP_dec. eapply weq.
Qed.
Proof.
  destruct sz; intuition.
  rewrite wplus_alt.
  unfold wplusN, wordBinN.
  destruct (wordToNat_natToWord (S sz) n); intuition.
  destruct (wordToNat_natToWord (S sz) m); intuition.
  rewrite H0; rewrite H2; clear H0 H2.
  replace (n - x * pow2 (S sz) + (m - x0 * pow2 (S sz))) with (n + m - x * pow2 (S sz) - x0 * pow2 (S sz))
    by omega.
  repeat rewrite drop_sub; auto; omega.
Qed.
Proof.
  intros; change (S n) with (1 + n); apply natToWord_plus.
Qed.
Proof.
  unfold goodSize.
  intros.
  apply (f_equal (@wordToNat _)) in H.
  destruct (wordToNat_natToWord sz n).
  destruct (wordToNat_natToWord sz m).
  intuition.
  rewrite H4 in H; rewrite H2 in H; clear H4 H2.
  assert (x = 0).
  destruct x; auto.
  simpl in *.
  generalize dependent (x * pow2 sz).
  intros.
  omega.
  assert (x0 = 0).
  destruct x0; auto.
  simpl in *.
  generalize dependent (x0 * pow2 sz).
  intros.
  omega.
  subst; simpl in *; omega.
Qed.
Proof.
  intros.
  destruct (wordToNat_natToWord sz n); intuition.
  destruct x.
  simpl in *; omega.
  simpl in *.
  apply Nlt_out in H.
  autorewrite with N in *.
  rewrite Npow2_nat in *.
  generalize dependent (x * pow2 sz).
  intros; omega.
Qed.
Proof.
  intros.
  apply (f_equal (fun x => x ^+ ^~ c)) in H.
  repeat rewrite <- wplus_assoc in H.
  rewrite wminus_inv in H.
  repeat rewrite (wplus_comm _ (wzero sz)) in H.
  repeat rewrite wplus_unit in H.
  assumption.
Qed.
Proof.
  destruct sz; intuition.
  rewrite wmult_alt.
  unfold wmultN, wordBinN.
  destruct (wordToNat_natToWord (S sz) n); intuition.
  destruct (wordToNat_natToWord (S sz) m); intuition.
  rewrite H0; rewrite H2; clear H0 H2.
  replace ((n - x * pow2 (S sz)) * (m - x0 * pow2 (S sz)))
    with ((n - x * pow2 (S sz)) * m - (n - x * pow2 (S sz)) * (x0 * pow2 (S sz)))
    by (rewrite Nat.mul_sub_distr_l; auto).
  rewrite mult_assoc; rewrite drop_sub.
  repeat rewrite mult_comm with (m:=m).
  replace (m * (n - x * pow2 (S sz)))
    with (m * n - m * (x * pow2 (S sz)))
    by (rewrite Nat.mul_sub_distr_l; auto).
  rewrite mult_assoc; rewrite drop_sub.
  auto.
  rewrite <- mult_assoc; apply Nat.mul_le_mono_l; auto.
  rewrite <- mult_assoc; apply Nat.mul_le_mono_l; auto.
Qed.
Proof.
  intros.
  unfold wlt in H.
  repeat rewrite wordToN_nat in *.
  apply Nlt_out in H.
  repeat rewrite Nat2N.id in *.
  auto.
Qed.
Proof.
  intros.
  unfold wlt in H.
  repeat rewrite wordToN_nat in *.
  apply Nge_out in H.
  repeat rewrite Nat2N.id in *.
  auto.
Qed.
Proof.
  intros.
  apply wlt_lt.
  auto.
Qed.
Proof.
  intros.
  apply wlt_lt in H.
  destruct (wordToNat_natToWord' sz m).
  rewrite <- H0.
  apply lt_plus_trans with (p := x * pow2 sz).
  assumption.
Qed.
Proof.
  intros.
  apply wle_le in H.
  destruct (wordToNat_natToWord' sz m).
  rewrite <- H0.
  apply le_plus_trans with (p := x * pow2 sz).
  assumption.
Qed.
Proof.
  intros.
  apply lt_word_lt_nat in H.
  apply Nat.lt_le_incl.
  assumption.
Qed.
Proof.
  unfold goodSize.
  intros.
  destruct (wordToNat_natToWord sz n); intuition.
  destruct x.
  simpl in *; omega.
  simpl in *.
  generalize dependent (x * pow2 sz).
  intros; omega.
Qed.
Proof.
  intros.
  apply wle_le in H0.
  rewrite wordToNat_natToWord_idempotent' in H0; auto.
Qed.
Proof.
  intros.
  apply wordToNat_natToWord_idempotent'.
  eapply le_lt_trans; eauto.
  apply wordToNat_bound.
Qed.
Proof.
  intros.
  case_eq (lt_dec n (pow2 sz)); intros.
  rewrite wordToNat_natToWord_idempotent'; auto.
  eapply le_trans.
  apply Nat.lt_le_incl.
  apply wordToNat_bound.
  omega.
Qed.
Proof.
  intros.
  eapply le_lt_trans.
  apply wordToNat_natToWord_le.
  auto.
Qed.
Proof.
  intros. rewrite <- H. rewrite natToWord_wordToNat. auto.
Qed.
Proof.
  intros.
  apply wlt_lt in H.
  erewrite wordToNat_natToWord_bound in H; eauto.
Qed.
Proof.
  intros.
  rewrite wplus_alt. unfold wplusN, wordBinN. simpl.
  assert (goodSize sz 1).
  unfold goodSize.
  inversion H.
  simpl; auto.
  apply one_lt_pow2.
  erewrite wordToNat_natToWord_bound.
  rewrite wordToNat_natToWord_idempotent' by auto.
  reflexivity.
  apply wlt_lt in H0.
  rewrite wordToNat_natToWord_idempotent' by auto.
  instantiate (1:=bound). omega.
Qed.
Proof.
  intros.
  unfold wlt.
  repeat rewrite wordToN_nat.
  apply Nlt_in.
  repeat rewrite Nat2N.id.
  auto.
Qed.
Proof.
  intros.
  unfold wlt.
  repeat rewrite wordToN_nat.
  apply N.le_ngt.
  apply N.ge_le.
  apply Nge_in.
  repeat rewrite Nat2N.id.
  auto.
Qed.
Proof.
  intros.
  apply wlt_lt in H.
  apply le_wle.
  omega.
Qed.
Proof.
  intros.
  unfold wminusN, wplusN, wnegN, wordBinN.
  destruct (weq y (natToWord sz 0)); subst.

  rewrite roundTrip_0.
  repeat rewrite <- minus_n_O.
  rewrite <- drop_sub with (k:=1) (n:=pow2 sz); try omega.
  replace (pow2 sz - 1 * pow2 sz) with (0) by omega.
  rewrite roundTrip_0.
  rewrite <- plus_n_O.
  reflexivity.

  rewrite wordToNat_natToWord_idempotent' with (n:=pow2 sz - wordToNat y).
  rewrite <- drop_sub with (k:=1).
  simpl.
  rewrite <- plus_n_O.
  replace (wordToNat x + (pow2 sz - wordToNat y) - pow2 sz) with (wordToNat x - wordToNat y).
  auto.
  rewrite Nat.add_sub_assoc.
  omega.

  remember (wordToNat_bound y); omega.

  simpl. rewrite <- plus_n_O.
  rewrite Nat.add_sub_assoc; [| remember (wordToNat_bound y); omega ].
  rewrite plus_comm.
  rewrite <- Nat.add_sub_assoc.
  omega.

  apply Nat.nlt_ge.
  unfold not in *; intros.
  apply H.
  apply lt_wlt; auto.

  apply Nat.sub_lt.
  remember (wordToNat_bound y); omega.

  assert (wordToNat y <> 0); try omega.

  assert (wordToN y <> wordToN (natToWord sz 0)).
  unfold not in *. intros. apply n.
  apply wordToN_inj.
  auto.

  repeat rewrite wordToN_nat in H0.
  unfold not in *. intros. apply H0.
  apply N2Nat.inj.
  repeat rewrite Nat2N.id.
  rewrite roundTrip_0.
  auto.
Qed.
Proof.
  intros.
  eapply well_founded_lt_compat with (f:=@wordToNat sz).
  apply wlt_lt.
Qed.
Proof.
  intros.

  destruct sz.
  exfalso.
  rewrite word0 with (w:=w') in H.
  rewrite word0 with (w:=w) in H.
  apply wlt_lt in H.
  omega.

  rewrite wplus_alt.
  unfold wplusN, wordBinN.
  rewrite wordToNat_natToWord_idempotent'.

  rewrite roundTrip_1.
  omega.

  eapply Nat.le_lt_trans; [| apply wordToNat_bound ].
  rewrite wordToNat_natToWord_idempotent';
    [| erewrite <- roundTrip_1; apply wordToNat_bound ].
  apply wlt_lt in H.
  instantiate (1:=w').
  omega.
Qed.
Proof.
  intros.
  destruct sz.
  rewrite word0 with (w:=n) in H.
  rewrite word0 with (w:=natToWord 0 0) in H.
  exfalso; auto. 

  destruct (weq n (natToWord (S sz) 0)); intuition.
  rewrite wminus_Alt.
  rewrite wminus_Alt2.
  unfold wordBinN.
  rewrite roundTrip_1.
  erewrite wordToNat_natToWord_bound with (bound:=n); try omega.
  assert (wordToNat n <> 0); try omega.
  unfold not; intros; apply n0; clear n0.
  rewrite <- H0; rewrite natToWord_wordToNat; auto.
  unfold not; intros; apply n0; clear n0.
  apply wlt_lt in H0.
  replace n with (natToWord (S sz) (wordToNat n)) by (rewrite natToWord_wordToNat; auto).
  f_equal; rewrite roundTrip_1 in *.
  omega.
Qed.
Proof.
  intros.
  erewrite Nat.succ_inj with (n2 := wordToNat (n ^- (natToWord sz 1))); auto.
  rewrite wordToNat_minus_one'; auto.
  assert (wordToNat n <> 0).
  intuition.
  erewrite <- roundTrip_0 with (sz := sz) in H0.
  apply wordToNat_inj in H0; tauto.
  omega.
Qed.
Proof.
  intros; omega.
Qed.
Proof.
  intros.
  rewrite wminus_Alt.
  rewrite wminus_Alt2; auto.
  unfold wordBinN.
  eapply wordToNat_natToWord_idempotent'.
  unfold goodSize.
  apply lt_minus.
  apply wle_le; auto.
  apply wordToNat_bound.
  apply wordToNat_bound.
Qed.
Proof.
  split; intuition.
  apply wordToNat_inj in H0; auto.
  subst; auto.
Qed.
Proof.
  unfold not.
  intros.
  induction sz.
  omega.
  unfold natToWord in H0; fold natToWord in H0.
  discriminate H0.
Qed.
Proof.
  split; intros.
  apply wordToNat_neq_inj.
  rewrite roundTrip_0; auto.
  apply wordToNat_neq_inj in H.
  rewrite roundTrip_0 in H; auto.
Qed.
Proof.
  split; intros.
  apply neq0_wneq0; omega.
  apply wordToNat_neq_inj in H.
  rewrite roundTrip_0 in H; omega.
Qed.
Proof.
  intros.
  apply lt_wlt; subst.
  rewrite wordToNat_minus_one; auto.
  apply gt0_wneq0 in H.
  omega.
Qed.
Proof.
  intros; rewrite wordToNat_minus_one; auto.
  apply gt0_wneq0; subst; auto.
Qed.
Proof.
  intros; omega.
Qed.
Proof.
  intros; omega.
Qed.
Proof.
  intros.
  unfold wlshift.
  eapply split1_0.
Qed.
Proof.
  intros.
  unfold wrshift.
  simpl.
  rewrite combine_n_0.
  eq_rect_simpl. reflexivity.
Qed.
Proof.
  intros sz n w H.
  generalize dependent w.
  remember (n - sz) as e.
  assert (n = sz + e) by omega; subst n.
  intros w.
  unfold wlshift.
  rewrite <- combine_wzero.
  erewrite combine_assoc, eq_rect_word_match.
  eq_rect_simpl.
  rewrite eq_rect_combine.
  apply split1_combine.
  Grab Existential Variables. omega.
Qed.
Proof.
  intros sz n w H.
  generalize dependent w.
  remember (n - sz) as e.
  assert (n = sz + e) by omega; subst n.
  intros w.
  unfold wrshift.
  erewrite wzero_rev, <- combine_wzero.
  eq_rect_simpl.
  rewrite <- eq_rect_word_match, <- eq_rect_combine, eq_rect_word_match.
  eq_rect_simpl.
  rewrite eq_rect_combine_assoc', split2_combine.
  reflexivity.
  Grab Existential Variables. omega.
Qed.
Proof.
  intros.
  unfold wlshift.
  eq_rect_simpl.
  reflexivity.
Qed.
Proof.
  intros.
  unfold wrshift.
  eq_rect_simpl.
  reflexivity.
Qed.
Proof.
  intros.
  unfold wlshift.
  rewrite wnot_split1.
  eq_rect_simpl.
  rewrite wnot_eq_rect.
  rewrite wnot_combine.
  rewrite wnot_zero.
  reflexivity.
Qed.
Proof.
  intros.
  unfold wrshift.
  rewrite wnot_split2.
  eq_rect_simpl.
  rewrite wnot_eq_rect.
  rewrite wnot_combine.
  rewrite wnot_zero.
  reflexivity.
Qed.
Proof.
  intros.
  replace (pow2 n + (pow2 n + 0)) with (2 * pow2 n) by omega.
  rewrite Nat.div2_double.
  auto.
Qed.
Proof.
  intros.
  destruct sz.
  left. rewrite (word0 n). auto.
  destruct (weq n $0); intuition.
  right.
  exists (wordToNat (n ^- $1)); intuition.
  rewrite wminus_Alt.
  rewrite wminus_Alt2.
  unfold wordBinN.
  rewrite roundTrip_1.
  erewrite wordToNat_natToWord_bound with (bound:=n); try omega.
  assert (wordToNat n <> 0); try omega.
  unfold not; intros; apply n0; clear n0.
  rewrite <- H. rewrite natToWord_wordToNat; auto.
  unfold not; intros; apply n0; clear n0.
  apply wlt_lt in H.
  replace n with (natToWord (S sz) (wordToNat n)) by (rewrite natToWord_wordToNat; auto).
  f_equal.
  rewrite roundTrip_1 in *.
  omega.
Qed.
Proof.
  unfold not.
  induction sz; intros; try omega.
  unfold wbit, wzero, wor in *.
  simpl in *.
  destruct (zero_or_wordToNat_S n).
  subst; rewrite roundTrip_0 in *. discriminate.
  destruct H1. destruct H1.
  rewrite H1 in *.
  inversion H0.
  apply (inj_pair2_eq_dec _ eq_nat_dec) in H5.
  rewrite div2_pow2_twice in H5.
  repeat rewrite <- H2 in H5.
  eapply IHsz; eauto.
  omega.
Qed.
Proof.
  intros.
  replace (pow2 n + (pow2 n + 0)) with (2 * pow2 n) by omega.
  apply mod2_double.
Qed.
Proof.
  induction sz; intros; try omega.
  unfold wbit, wzero, wand.
  simpl.
  destruct (zero_or_wordToNat_S n1); destruct (zero_or_wordToNat_S n2);
    try congruence; destruct_conjs; subst; try rewrite roundTrip_0.

  repeat rewrite H4; simpl; repeat rewrite mod2_pow2_twice; f_equal.
  rewrite wand_kill; auto.

  repeat rewrite H4; simpl; repeat rewrite mod2_pow2_twice; f_equal.
  rewrite wand_comm; rewrite wand_kill; auto.

  repeat rewrite H4; repeat rewrite H6; simpl.
  repeat rewrite mod2_pow2_twice; f_equal.
  repeat rewrite div2_pow2_twice.
  eapply IHsz; try omega.

  apply word_neq.
  unfold not in *; intros; apply H1; clear H1.
  apply sub_0_eq; rewrite <- H2.
  ring_sz sz'.
Qed.
Proof.
  induction sz; intros; try omega.
  unfold wbit, wzero, wand, wnot.
  simpl.
  f_equal.
  apply andb_negb_r.

  destruct (zero_or_wordToNat_S n); subst.
  rewrite roundTrip_0; simpl.
  apply wand_kill.

  do 2 destruct H0.
  rewrite H0; simpl.
  rewrite div2_pow2_twice.
  fold wnot.
  rewrite <- H1.
  eapply IHsz.
  omega.
Qed.
Proof.
  induction sz; intros; try omega.
  unfold wbit, wzero, wand, wnot.
  simpl.
  destruct (zero_or_wordToNat_S n1); destruct (zero_or_wordToNat_S n2);
    try congruence; destruct_conjs; subst; fold wnot; try rewrite roundTrip_0; simpl;
    f_equal.

  rewrite H4; simpl; rewrite mod2_pow2_twice; auto.
  rewrite H4; simpl; rewrite div2_pow2_twice; apply wand_kill.

  rewrite H4; simpl; rewrite mod2_pow2_twice; auto.
  rewrite H4; simpl; rewrite div2_pow2_twice.
  rewrite wnot_zero. rewrite wand_comm. apply wand_unit.

  rewrite H4; simpl; rewrite mod2_pow2_twice; simpl; apply andb_true_r.
  rewrite H4; rewrite H6; simpl.
  repeat rewrite div2_pow2_twice.
  apply IHsz; try omega.

  apply word_neq.
  unfold not in *; intros; apply H1.
  apply sub_0_eq.
  rewrite <- H2.
  ring_sz sz'.
Qed.
Proof.
  intros.
  exact H.
Qed.