Proof. intros; omega. Qed.

Proof.
  intros.
  unfold list2byteset, byteset2list.
  symmetry; apply surjective_pairing.
Qed.
Proof.
  intros.
  unfold list2byteset, byteset2list. 
  destruct l.
  destruct H; reflexivity.
  reflexivity.
Qed.
Proof.
  intros.
  unfold valu2list.
  rewrite bsplit_list_len.
  rewrite valubytes_is.
  reflexivity.
Qed.
Proof.
  destruct i; intros. simpl.
  inversion H.
  simpl.
  rewrite <- minus_n_O.
  reflexivity.
Qed.
Proof.
  induction i.
  reflexivity.
  destruct l.
  intros.
  destruct H; reflexivity.
  intros.
  rewrite valuset2bytesets_rec_expand.
  replace (S i - 1) with i by omega.
  simpl.
  rewrite IHi.
  reflexivity.
  unfold not; intros; inversion H0.
  omega.
Qed.
Proof.
  intros.
  unfold valuset2bytesets.
  rewrite map_length.
  apply valuset2bytesets_rec_len.
  unfold not; intros; inversion H.
Qed.
Proof. intros. omega. Qed.

Fact lt_le_trans: forall n m p, n < m -> m <= p -> n < p.
Proof. intros. omega. Qed.

Proof. intros. omega. Qed.

Proof. intros. omega. Qed.

Proof. intros. omega. Qed.

Proof. intros. omega. Qed.

Proof. intros. omega. Qed.

Proof. intros. omega. Qed.

Proof. 
  induction p; intros.
  repeat rewrite <- mult_n_O in H; inversion H.
  omega.
Qed.
Proof. 
  induction p; intros.
  repeat rewrite <- mult_n_O in H; inversion H.
  omega.
Qed.
Proof. intros. omega. Qed.

Proof.
  assert(A: forall x, 0 * x = 0). intros. omega.
  induction n. intros.
  destruct m.
  rewrite A in H; inversion H.
  omega. intros.
  destruct m.
  rewrite A in H; inversion H.
  apply lt_n_S.
  apply IHn.
  simpl in H.
  apply plus_lt_compat_rev in H.
  apply H.
Qed.
Proof. intros.
omega.
Qed.
Proof. intros.
omega.
Qed.
Proof.
  intros.
  rewrite Nat.div_add_l.
  apply Nat.div_small in H.
  rewrite H; symmetry; apply plus_n_O.
  unfold not; intros; rewrite H0 in H; inversion H.
Qed.
Proof.
  split; intros.
  inversion H; reflexivity.
  rewrite H; reflexivity.
Qed.
Proof.
  induction lists.
  reflexivity.
  intros.
  rewrite Forall_forall in H.
  destruct n.
  simpl.
  apply selN_app1.
  destruct H with (x:= a).
  apply in_eq.
  apply H0.
  destruct H with (x:=a).
  apply in_eq.
  simpl.
  rewrite selN_app2.
  replace (length a + n * length a + i - length a) with (n * length a + i).
  apply IHlists.
  rewrite Forall_forall.
  intros.
  eapply in_cons in H1.
  apply H in H1.
  apply H1.
  apply H0.
  remember (n * length a + i) as x.
  replace (length a + n * length a + i - length a) with (length a + x - length a).
  omega.
  rewrite Heqx.
  omega.
  unfold ge.
  remember (n * length a + i) as x.
  replace (length a + n * length a + i) with (length a + x).
  apply le_plus_l.
  omega.
Qed.
Proof. induction l; intros; reflexivity. Qed.


Proof.
  induction vs.
  reflexivity.
  simpl.
  rewrite app_length.
  rewrite IHvs.
  rewrite valuset2bytesets_len.
  reflexivity.
Qed.
Proof. intros; destruct i; reflexivity. Qed.


Proof.
  intros.
  induction l.
  rewrite firstn_nil.
  reflexivity.
  simpl.
  apply app_nil_r.
Qed.
  Proof. intros; subst; reflexivity. Qed.

Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  rewrite firstn_app_l.
  reflexivity.
  rewrite Forall_forall in H.
  destruct H with (x:= a).
  apply in_eq.
  apply H0.
Qed.
Proof.
  intros.
  rewrite map_map.
  unfold selN'.
  replace (fun x : list A => fst (list2byteset def x)) with
    (fun x : list A => selN x 0 def).
  reflexivity.
  apply functional_extensionality.
  intros; symmetry; apply fst_list2byteset.
Qed.
Proof. intros; reflexivity. Qed.

Proof.
  intros.
  simpl.
  apply natToWord_wordToNat.
Qed.
Proof.
  intros; subst; auto.
Qed.
Proof.
  intros.
  generalize (bytes_eq_to_word_eq H).
  generalize_proof.
  destruct H; intros.
  eq_rect_simpl; auto.
Qed.
Proof.
  intros.
  rewrite eq_rect_bytes_to_word.
  unfold bcombine.
  rewrite combine_n_0.
  eq_rect_simpl; auto.
Qed.
Proof.
  intros.
  unfold valu2list, list2valu.
  rewrite bytes2valu2bytes.

  unfold bytes2valubytes.
  destruct (le_dec (length l) valubytes); try omega.
  simpl.

  generalize_proof.
  rewrite <- H.
  rewrite Nat.sub_diag.
  intros.

  rewrite bcombine_0.
  rewrite list2bytes2list; auto.
Qed.
Proof.
  unfold list2valu, valu2list; intros.

  assert (length (bsplit_list (valu2bytes v)) = valubytes).
  rewrite bsplit_list_len; auto.

  unfold bytes2valu.
  eq_rect_simpl.
  rewrite eq_rect_bytes_to_word; eq_rect_simpl.
  unshelve erewrite bytes2list2bytes; auto.

  unfold bytes2valubytes.
  match goal with
  | [ |- context[match ?d with _ => _ end] ] =>
    destruct d
  end; try omega.

  unfold bytes.
  unfold bcombine.
  repeat rewrite eq_rect_bytes_to_word; eq_rect_simpl.
  repeat generalize_proof; intros.
  destruct e.
  simpl.
  generalize_proof.
  rewrite H, Nat.sub_diag; simpl.
  rewrite combine_n_0.
  intros.
  eq_rect_simpl.
  rewrite <- valu2bytes2valu.
  unfold bytes2valu.
  eq_rect_simpl.
  rewrite eq_rect_bytes_to_word; eq_rect_simpl.
  repeat generalize_proof; intros.
  assert (e = e2) by (apply ProofIrrelevance.proof_irrelevance).
  congruence.
Qed.
Proof. intros; rewrite H; reflexivity. Qed.

Proof.
  induction l; intros.
  rewrite H; reflexivity.
  simpl.
  destruct i.
  inversion H.
  simpl.
  rewrite IHl.
  reflexivity.
  simpl in H.
  inversion H; reflexivity.
Qed.
Proof.
  intros.
  destruct l.
  inversion H.
  simpl in H; omega.
Qed.
Proof.
	intros.
	unfold valuset2bytesets.
	simpl.
	rewrite v2b_rec_nil.
	rewrite map_map.
	rewrite map_map.
	unfold cons', list2byteset; simpl.
	rewrite map_id.
	reflexivity.
	symmetry; apply valu2list_len.
Qed.
Proof.
	induction i; intros.
	simpl.
	apply length_zero_iff_nil in H; subst; reflexivity.
	simpl.
	rewrite IHi.
	unfold selN'; simpl.
	destruct a.
	simpl in H; inversion H.
	reflexivity.
	destruct a.
	simpl in H; inversion H.
	simpl in H; omega.
	rewrite Forall_forall; intros.
	apply in_map_iff in H1.
	repeat destruct H1.
	rewrite Forall_forall in H0.
	apply H0 in H2.
	destruct x0.
	simpl in H2; inversion H2.
	simpl in H2; omega.
Qed.
	Proof.
		intros.
		unfold valuset2bytesets.
		unfold byteset2list; simpl.
		apply mapfst_valuset2bytesets_rec.
		apply valu2list_len.
		rewrite Forall_forall; intros.
		apply in_map_iff in H.
		repeat destruct H.
		apply valu2list_len.
	Qed.
Proof.
  intros.
  simpl.
  unfold bsplit1_dep, bsplit2_dep.
  reflexivity.
Qed.
Proof.
	induction l; simpl.
	reflexivity.
	rewrite IHl.
	reflexivity.
Qed.
Proof.
	intros.
	rewrite map_map.
	unfold list2byteset, cons'; simpl.
	reflexivity.
Qed.
	Proof.
		induction k; intros.
		simpl.
		rewrite Forall_forall in H.
		assert (In a (a::l)).
		apply in_eq.
		apply H in H0.
		apply length_zero_iff_nil in H0.
		rewrite H0; reflexivity.
		destruct a.
		assert (In nil (nil::l)).
		apply in_eq.
		rewrite Forall_forall in H.
		apply H in H0.
		simpl in H0; inversion H0.
		simpl.
		destruct l.
		simpl.
		rewrite v2b_rec_nil.
		rewrite merge_bs_nil.
		rewrite l2b_cons_x_nil.
		reflexivity.
		assert (In (b::a) ((b::a)::nil)).
		apply in_eq.
		rewrite Forall_forall in H.
		apply H in H0.
		simpl in H0; inversion H0.
		reflexivity.
		simpl.
		rewrite IHk.
		reflexivity.
		rewrite Forall_forall; intros.
		repeat destruct H0.
		assert (In (b::a) ((b::a)::l::l0)).
		apply in_eq.
		rewrite Forall_forall in H.
		apply H in H0.
		simpl in H0; inversion H0.
		reflexivity.
		assert (In l ((b::a)::l::l0)).
		apply in_cons.
		apply in_eq.
		rewrite Forall_forall in H.
		apply H in H0.
		destruct l.
		simpl in H0; inversion H0.
		simpl in H0; inversion H0.
		reflexivity.
		apply in_map_iff in H0.
		repeat destruct H0.
		rewrite Forall_forall in H.
		eapply in_cons in H1.
		eapply in_cons in H1.
		apply H in H1.
		destruct x0.
		simpl in H1; inversion H1.
		simpl in H1; inversion H1.
		reflexivity.
	Qed.
Proof.
  unfold valuset2byteset.
  generalize valubytes.
  induction n; intros; subst; auto.
  destruct vs; cbn [length] in *.
  omega.
  cbn -[skipn selN_each].
  f_equal.
  rewrite <- seq_shift.
  rewrite map_map.
  rewrite IHn by (cbn; omega).
  apply map_ext. intros.
  rewrite selN_each_S. reflexivity.
Qed.
Proof.
  unfold valuset2bytesets, valuset2bytesets'.
  intros.
  setoid_rewrite valuset2bytesets_rec_eq_valuset2bytesets.
  destruct vs; cbn.
  unfold valuset2byteset at 1.
  rewrite map_map.
  cbn.

  rewrite combine_map.
  f_equal.
  rewrite map_selN_seq; auto.
  rewrite valu2list_len; auto.
  autorewrite with list.
  destruct vs; cbn. omega.
Qed.
Proof.
  unfold bytesets2valuset.
  induction n; intros; subst; auto.
  cbn -[skipn].
  destruct bs; cbn [length] in *.
  omega.
  f_equal.
  rewrite <- seq_shift.
  rewrite map_map.
  rewrite IHn by (cbn; omega).
  apply map_ext. intros.
  rewrite selN_each_S. reflexivity.
Qed.
Proof.
  unfold selN_each.
  induction l; cbn; intros; auto.
  rewrite surjective_pairing with (p := split l).
  destruct a; cbn.
  f_equal.
  eauto.
Qed.
Proof.
  unfold selN_each.
  induction l; cbn; intros; auto.
  rewrite surjective_pairing with (p := split l).
  destruct a; cbn.
  f_equal.
  eauto.
Qed.
Proof.
  unfold bytesets2valuset, bytesets2valuset'.
  intros.
  setoid_rewrite bytesets2valuset_rec_eq_map.
  cbn.
  repeat f_equal.
  apply selN_each_fst_list2byteset.
  rewrite <- seq_shift.
  repeat rewrite map_map.
  eapply Forall_selN in H as H'.
  rewrite H'.
  apply map_ext. intros.
  rewrite selN_each_snd_list2byteset. auto.
  rewrite Valulen.valubytes_is in H0. omega.
  autorewrite with list.
  rewrite Valulen.valubytes_is in H0. omega.
Qed.
Proof.
  intros.
  rewrite valuset2bytesets_eq_valuset2bytesets'.
  destruct vs; cbn.
  erewrite bytesets2valuset_eq_bytesets2valuset' with (n := length l).
  cbv [bytesets2valuset' valuset2bytesets'].
  rewrite combine_split. cbn.
  rewrite valu2list2valu.
  f_equal.
  induction l; cbn; auto.
  f_equal.
  unfold valuset2byteset.
  rewrite map_map. cbn.
  rewrite map_selN_seq.
  apply valu2list2valu.
  rewrite valu2list_len. auto.
  rewrite <- seq_shift.
  rewrite map_map.
  cbn.
  rewrite <- IHl at 2.
  apply map_ext. intros.
  f_equal.
  unfold valuset2byteset, selN_each.
  repeat rewrite map_map.
  reflexivity.
  rewrite valu2list_len.
  unfold valuset2byteset.
  autorewrite with list. auto.
  unfold valuset2bytesets', valuset2byteset. cbn.
  apply Forall_forall. intros x H.
  destruct x; cbn in *.
  apply in_combine_r in H.
  rewrite in_map_iff in *. deex.
  autorewrite with lists. auto.
  unfold valuset2bytesets', valuset2byteset. cbn.
  autorewrite with lists.
  rewrite seq_length.
  rewrite valu2list_len.
  apply Nat.min_id.
Qed.
Proof.
  induction l2; intros.
  split.
  auto.

  destruct l1.
  unfold not in H; destruct H; reflexivity.
  destruct a0.
  unfold updN_list in *.
  simpl in *.
  inversion H0.
  unfold updN_list in *.
  simpl in *.
  inversion H0.
Qed.
Proof.
  induction l; intros.
  inversion H.
  destruct n.
  simpl.
  unfold not; intros; inversion H0.
  simpl.
  apply IHl.
  simpl in H.
  omega.
Qed.
Proof.
  induction i; intros.
  left. reflexivity.
  right.
  destruct bn.
  reflexivity.
  simpl in H.
  inversion H.
Qed.
Proof.
intros; unfold d_map; simpl.
rewrite map_map; reflexivity.
Qed.
Proof.
intros.
rewrite <- Nat.add_mod_idemp_l; try omega.
rewrite Nat.mod_same; simpl; try omega.
apply Nat.mod_1_l; auto.
Qed.
Proof.
  assert(A: forall x, 0 * x = 0). intros. omega.
  induction n. intros.
  destruct m.
  omega.
  omega. intros.
  destruct m.
  inversion H0.
  apply plus_is_O in H2.
  destruct H2.
  omega.
  apply le_n_S.
  apply IHn.
  auto.
  simpl in H0.
  omega.
Qed.
Proof.
intros.
unfold valuset2bytesets.
destruct l.
simpl.
rewrite map_map; simpl.
rewrite valuset2bytesets_rec_expand.
simpl.
unfold selN'.
rewrite map_map; reflexivity.
rewrite valubytes_is; omega.
Qed.
Proof. intros; subst; reflexivity. Qed.

Proof. induction j; destruct l; intros; simpl.
inversion H0.
apply skipn_app_l.
rewrite Forall_forall in H1.
destruct H1 with (x:= l).
apply in_eq.
omega.
inversion H0.
erewrite IHj.
reflexivity.
eauto.
simpl in H0; omega.
eapply Forall_cons2.
eauto.
Qed.
Proof.
  induction l; intros.
  simpl in H0; symmetry in H0.
  eapply map_eq_nil in H0.
  eauto.
  destruct l'.
  rewrite map_cons in H0; simpl in H0.
  inversion H0.
  repeat rewrite map_cons in H0.
  inversion H0.
  apply H in H2.
  rewrite H2.
  eapply IHl in H.
  apply cons_simpl.
  eauto.
  eauto.
Qed.
Proof. intros; rewrite H; reflexivity. Qed.


Fact minus_eq_O: forall n m, n >= m -> n - m = 0 -> n = m.
Proof.
induction n; intros.
inversion H; reflexivity.
destruct m.
inversion H0.
apply eq_S.
apply IHn.
omega. omega.
Qed.
Proof. rewrite valubytes_is; unfold not; intros H'; inversion H'. Qed.

Fact divmult_plusminus_eq:forall n m, m <> 0 ->
   m + n / m * m = n + (m - n mod m).
Proof.
intros.   
rewrite Nat.add_sub_assoc.
replace (n + m - n mod m) 
    with (m + n - n mod m) by omega.
rewrite <- Nat.add_sub_assoc.
rewrite Nat.add_cancel_l with (p:= m); eauto.
rewrite Nat.mod_eq; eauto.
rewrite Rounding.sub_sub_assoc.
apply Nat.mul_comm.
apply Nat.mul_div_le; eauto.
apply Nat.mod_le; eauto.
apply Nat.lt_le_incl.
apply Nat.mod_upper_bound; eauto.
Qed.
Proof. intros.
remember (n - (m - k mod m)) as b.
replace (b - b / m * m) with (b mod m).
apply Nat.lt_le_incl.
apply Nat.mod_upper_bound; eauto.
rewrite Nat.mul_comm.
apply Nat.mod_eq; eauto.
Qed.
Proof. intros. omega. Qed.

Proof.
induction b; intros.
unfold not in H0; destruct H0; reflexivity.
destruct a.
unfold not in H; destruct H; reflexivity.
unfold not in *; intros.
apply IHb; auto.
intros.
rewrite H2 in H1.
rewrite Nat.mod_1_r in H1; inversion H1.
simpl in H1.
destruct b.
reflexivity.
simpl in *.
destruct (snd (Nat.divmod a (S b) 0 b)); omega.
Qed.
Proof.
intros.
unfold get_sublist.
rewrite firstn_length_l.
reflexivity.
rewrite skipn_length.
omega.
Qed.
Proof. 
  intros.
  unfold bytes2valubytes.
  destruct (le_dec 1 valubytes).
  simpl.
  unfold eq_rect.
  destruct (bytes_eq l).
  simpl.
  unfold bsplit1_dep, bsplit2_dep; simpl.
  rewrite bsplit1_bcombine.
  rewrite bsplit2_bcombine.
  unfold natToWord.
  exists (bsplit_list
       ((fix natToWord (sz n : addr) {struct sz} : word sz :=
           match sz as sz0 return (word sz0) with
           | 0 => WO
           | S sz' => WS (mod2 n) (natToWord sz' (Nat.div2 n))
           end) ((valubytes - 1) * 8) 0)).
  unfold byte2bytes.
  unfold word2bytes.
  eq_rect_simpl.
  reflexivity.
  rewrite valubytes_is in n; omega.
Qed.
	Proof.
		intros; repeat rewrite app_length.
		repeat rewrite map_length.
		rewrite firstn_length_l.
		rewrite skipn_length.
		omega.
		omega.
	Qed.
	Proof.
		intros;
		apply DiskLogHash.PaddedLog.Desc.le_add_le_sub.
		apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
		apply valubytes_ne_O.
		auto.
	Qed.
	Proof. intros; omega. Qed.
	
Proof. intros; omega. Qed.

	Proof. intros; omega. Qed.

	Proof. intros; omega. Qed.
	
	Proof. intros; omega. Qed.

	Proof. intros; omega. Qed.

	Proof. intros; omega. Qed.
	
	Lemma ppmm_4_5_minus_distr_le: forall a b c d e,
d <= a + b + c ->
e <= d ->
a + b + c - (d - e) = a + b + c - d + e.
	Proof. intros; omega. Qed.
	
	Proof. intros; omega. Qed.
	
	Proof. intros; repeat rewrite app_assoc; reflexivity. Qed.
	
	Proof. intros; omega. Qed.
	
	Proof. intros; omega. Qed.



Proof.
  induction n; intros; simpl.
  reflexivity.
  destruct (length l / m) eqn:D.
  destruct m eqn:D1; simpl; try omega.
  apply Nat.div_small_iff in D; try omega.
  rewrite H0 in D.
  destruct n.
  simpl in D. rewrite <- plus_n_O in D; omega.
  simpl in D. apply lt_S_n in D.
  assert (forall a b, a + (S b) < a -> False).
  intros; omega.
  apply H1 in D; inversion D.
  rewrite IHn; try omega.
  rewrite skipn_length.
  rewrite H0.
  replace (S n * m - m) with (n * m).
  rewrite H0 in D.
  rewrite Nat.div_mul in *.
  inversion D.
  reflexivity.
  all: try omega.
  simpl.
  rewrite pm_1_3_cancel.
  reflexivity.
  rewrite skipn_length.
  rewrite H0.
  simpl.
  apply pm_1_3_cancel.
Qed.
Proof.
  intros;
  unfold valuset2bytesets.
  simpl.
  unfold byte2valu.
  unfold bytes2valubytes.
  destruct (le_dec 1 valubytes).
  rewrite v2b_rec_nil.
  rewrite l2b_cons_x_nil.
  unfold word2bytes.
  eq_rect_simpl.
  unfold valu2list.
  rewrite bytes2valu2bytes.
  unfold bcombine.
  eq_rect_simpl.
  unfold eq_rect.
  destruct (bytes_eq l).
  simpl.
  unfold bsplit1_dep; simpl.
  unfold bsplit1.
  eq_rect_simpl.
  rewrite Word.split1_combine.
  unfold byte2bytes.
  unfold word2bytes.
  eq_rect_simpl.
  reflexivity.
  rewrite valu2list_len; reflexivity.
  rewrite valubytes_is in n; omega.
Qed.
Proof.
  induction a; intros.
  simpl in H.
  apply length_zero_iff_nil in H; rewrite H.
  simpl.
  rewrite <- H0; rewrite firstn_exact; reflexivity.
  simpl.
  rewrite skipn_app_l.
  rewrite IHa.
  rewrite firstn_app_l.
  reflexivity.
  all: try omega.
  all: try rewrite H; simpl; try apply le_plus_trans; try omega.
  rewrite skipn_length. rewrite H; simpl. apply pm_1_3_cancel.
Qed.
Proof.
    induction a; intros.
    reflexivity.
    simpl.
    rewrite IHa.
    rewrite firstn_map_comm.
    rewrite skipn_map_comm.
    reflexivity.
Qed.
Proof.
  intros; unfold get_sublist.
  rewrite <- firstn_map_comm; 
  rewrite <- skipn_map_comm;
  reflexivity.
Qed.  
Proof.
  intros. 
  destruct l.
  destruct H; reflexivity.
  reflexivity.
Qed.
Proof.
  induction a; intros.
  simpl in *.
  symmetry in H; apply length_zero_iff_nil in H. symmetry; auto.
  simpl.
  rewrite IHa.
  apply firstn_skipn.
  rewrite skipn_length.
  rewrite <- H; simpl; rewrite pm_1_3_cancel; reflexivity.
Qed.
Proof.
  intros.
  replace (m1 + 1) with (S m1) by omega.
  reflexivity.
Qed.
Proof.
  induction a; intros.
  simpl in *.
  inversion H1.
  simpl in *.
  destruct H1.
  unfold not; intros.
  rewrite <- H1 in H2.
  apply length_zero_iff_nil in H2.
  rewrite firstn_length_l in H2; try omega.
  rewrite H0; apply le_plus_trans. apply le_n.
  eapply IHa; eauto.
  rewrite skipn_length.
  rewrite H0; apply pm_1_3_cancel.
Qed.
Proof.  intros. omega. Qed.


Proof. intros. omega. Qed.

Proof. intros; omega. Qed.

Proof. intros; omega. Qed.

Fact merge_bs_length: forall l l',
length (merge_bs l l') = length l.
Proof.
induction l; intros.
reflexivity.
simpl.
destruct l'; simpl; rewrite IHl; reflexivity.
Qed.
Proof.
intros.
unfold updN_list.
repeat rewrite app_length.
rewrite merge_bs_length.
rewrite firstn_length_l; try omega.
rewrite skipn_length.
rewrite Nat.add_assoc.
symmetry; apply le_plus_minus.
auto.
Qed.
Proof.
intros.
unfold updN_list; simpl.
unfold get_sublist; simpl.
rewrite firstn_firstn.
rewrite Nat.min_id.
replace (firstn (length ln) (skipn a l)) with (firstn (length ln + 0) (skipn a l)).
rewrite skipn_firstn_comm.
simpl. rewrite app_nil_r. reflexivity.
rewrite <- plus_n_O; reflexivity.
Qed.
Proof. intros; rewrite H; reflexivity. Qed.

Proof. intros; rewrite H; reflexivity. Qed.

Proof. rewrite valubytes_is; omega. Qed.


Proof. intros; rewrite valubytes_is in *; omega. Qed.

Proof. intros; rewrite valubytes_is in *; omega. Qed.

Proof.
intros.
rewrite get_sublist_length.
rewrite Nat.div_mul.
omega.
apply valubytes_ne_O.
simpl.
eapply length_data_ge_m1; eauto.
Qed.
Proof. intros; rewrite valubytes_is in *; omega. Qed.

Proof. intros; apply length_zero_iff_nil in H; rewrite valubytes_is in *; omega. Qed.

Proof. intros; rewrite valubytes_is in *; omega. Qed.

Proof. intros; rewrite valubytes_is in *; omega. Qed.

Proof.
intros.
destruct l.
unfold not in H; destruct H; reflexivity. repeat eexists.
Qed.
Proof. intros; subst; reflexivity. Qed.

Proof. intros; omega. Qed.

Proof. 
  intros.
  remember (a / b * b + b) as x.
  rewrite Nat.div_mod with (x:= a)(y:= b).
  rewrite Heqx.
  apply plus_le_compat.
  rewrite Nat.mul_comm; apply le_n.
  apply Nat.lt_le_incl; apply Nat.mod_upper_bound.
  all: auto.
Qed.
Proof. intros; omega. Qed.

Proof. intros; omega. Qed.

Proof. intros; omega. Qed.

Proof.
  intros.
  eapply Nat.mod_unique.
  apply Nat.mod_upper_bound.
  auto.
  instantiate (1:= (a - b) / b + 1).
  remember (b * ((a - b) / b + 1) + (a - b) mod b) as x.
  rewrite <- Nat.sub_add with (n:= b)(m:= a).
  rewrite Nat.div_mod with (x:= a-b)(y:=b).
  rewrite Nat.add_comm.
  rewrite Nat.add_assoc.
  rewrite Heqx.
  rewrite Nat.mul_add_distr_l.
  omega.
  all: auto.
Qed.
Proof.
  intros.
  rewrite le_minus_dist.
  rewrite <- Nat.add_sub_swap.
  all: auto.
  remember (a+c) as x.
  apply Nat.mul_cancel_l with (p:= b).
  auto.
  replace (b * ((x - b) / b)) with ((x - b) - (x-b) mod b).
  rewrite Nat.mul_sub_distr_l.
  replace (b * (x / b)) with (x - x mod b).
  rewrite modulo_eq.
  omega.
  all: auto.
  rewrite Heqx.
  omega.
  replace (x - x mod b) 
    with (b*(x / b) + x mod b - x mod b).
  apply Nat.add_sub.
  rewrite <- Nat.div_mod.
  reflexivity.
  auto.
  replace (x - b - (x - b) mod b) 
    with (b * ((x-b)/b) + (x-b) mod b - (x - b) mod b).
  apply Nat.add_sub.
  rewrite <- Nat.div_mod.
  reflexivity.
  auto.
Qed.
	Proof.
		induction c; intros.
		simpl.
		rewrite <- minus_n_O.
		reflexivity.
		replace (a - S c * b) with ((a - b) - c * b).
		rewrite IHc.
		apply modulo_eq.
		all: auto.
		simpl in H0.
		eapply le_trans.
		2: apply H0.
		apply le_plus_l.
		apply Nat.le_add_le_sub_l.
		simpl in H0; auto.
		simpl.
		rewrite Nat.sub_add_distr.
		reflexivity.
	Qed.
	Proof. intros; omega. Qed.
	

	
  Lemma div_lt_le: forall a b c,
      b <> 0 ->
      a >= c ->
      a / b >= c / b.
  Proof.
    intros.
    apply Nat.div_le_mono; eauto.
  Qed.
	Proof. intros; subst; reflexivity. Qed.
	
	Proof.
	 intros.
	 remember (a mod b) as x.
	 remember (a / b * b) as y.
	 rewrite Nat.div_mod with (x:= a)(y:= b); eauto.
	 rewrite Heqx; rewrite Heqy.
	 rewrite Nat.add_sub.
	 apply Nat.mul_comm.
 Qed.
	Proof.
		intros.
		rewrite mod_minus.
		apply Nat.mod_mul.
		all: auto.
	Qed.
Proof. intros; omega. Qed.


Proof.
  intros.
  destruct c; simpl in *; try omega.
  rewrite Nat.sub_0_r in *.
  destruct (Nat.eq_dec a (b + c * b)); try omega.
  subst.
  exfalso.
  rewrite Nat.mod_add in H2 by auto.
  rewrite Nat.mod_same in * by auto.
  omega.
Qed.
Proof.
  induction a; intros.
  simpl; apply plus_n_O.
  simpl.
  rewrite IHa.
  rewrite app_length; simpl; omega.
Qed.
Proof.
  induction a; intros.
  reflexivity.
  simpl.
  rewrite IHa.
  rewrite selN_app1.
  reflexivity.
  auto.
  rewrite app_length.
  simpl; omega.
Qed.
Proof.
  intros.
  destruct (lt_dec i (length l + a)).
  generalize dependent l.
  induction a; intros.
  simpl.
  rewrite selN_oob; auto.
  simpl.
  destruct (le_dec (S (length l)) i).
  apply IHa.
  rewrite app_length; simpl; omega.
  rewrite app_length; simpl; omega.
  apply Nat.nle_gt in n.
  rewrite list_zero_pad_selN_l.
  rewrite selN_app2.
  simpl.
  destruct (i - length l); try omega; reflexivity.
  auto.
  rewrite app_length; simpl; omega.
  apply selN_oob.
  rewrite list_zero_pad_length; omega.
Qed.
Proof.
  induction c; intros.
  inversion H1.
  destruct (lt_dec a b).
  apply Nat.mod_small_iff in l.
  rewrite l.
  unfold not; intros.
  rewrite H2 in H0; inversion H0.
  auto.
  apply Nat.nlt_ge in n.
  replace (S c - 1) with c in H0 by omega.
  simpl in *.
  rewrite <- modulo_eq.
  apply IHc.
  all: try omega.
  rewrite Nat.mul_sub_distr_r.
  apply Nat.lt_add_lt_sub_r.
  simpl; rewrite <- plus_n_O.
  rewrite Nat.sub_add; try omega.
  destruct c. omega.
  simpl;  apply le_plus_l.
Qed.
Proof. induction l; intros.
  simpl.
  repeat rewrite firstn_nil.
  reflexivity.
  destruct l'.
  rewrite firstn_nil.
  repeat rewrite merge_bs_nil.
  apply firstn_map_comm.
  destruct a0.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.
Proof. 
  induction a; intros; simpl.
  rewrite app_nil_r; reflexivity.
  rewrite IHa.
  simpl.
  remember ((l ++ byte0 :: nil) ++ list_zero_pad nil a) as x.
  rewrite IHa.
  rewrite Heqx.
  rewrite <- app_comm_cons.
  apply app_assoc_reverse.
Qed.  
Proof.
  induction a; intros.
  split; intros.
  split; simpl in *; auto.
  destruct H.
  rewrite H; reflexivity.
  split; intros.
  simpl in H.
  apply IHa in H.
  destruct H.
  apply app_eq_nil in H.
  destruct H.
  inversion H1.
  destruct H.
  inversion H0.
Qed.
Proof. intros; omega. Qed.

Proof.
  induction a; intros.
  inversion H.
  destruct b.
  exists a.
  omega.
  simpl.
  apply IHa.
  omega.
Qed.
Proof. intros. omega. Qed.

Proof.
	induction a; intros.
	reflexivity.
	destruct b.
	reflexivity.
	simpl.
	rewrite list_zero_pad_expand.
	simpl.
	rewrite IHa.
	symmetry; apply list_zero_pad_expand.
Qed.
	Proof. 
	intros; inversion H. exists 0. reflexivity.
	exists m. reflexivity.
	Qed.
	Proof.
	intros. apply Nat.lt_add_lt_sub_r; simpl.
	apply Nat.mod_upper_bound; auto.
	Qed.
	Proof. intros; omega. Qed.
	
	Lemma mod_upper_bound_le': forall a b,
	b <> 0 ->
	b >= a mod b.
	Proof. 
	intros; apply Nat.lt_le_incl; 
	apply Nat.mod_upper_bound; auto.
	Qed.
Proof. 
	intros. 
	rewrite Nat.div_mod with (x:= a)(y:= b).
	apply Nat.add_nonneg_pos.
	all: try omega.
	apply le_0_n.
Qed.
Proof. intros; omega. Qed.

 Lemma lt_plus_minus_l: forall a b c,
  c > 0 -> a < b + c -> a - b < c.
Proof.  intros; omega. Qed.

Proof. intros; omega. Qed.

Proof.
  intros.
  destruct b; simpl in *.
  inversion H0.
  rewrite <- minus_n_O in *.

  pose proof (Nat.le_exists_sub (b*c) a); intuition; deex.
  rewrite Nat.mod_add by auto.
  rewrite Nat.mod_small by omega.
  omega.
Qed.
	Proof.
		intros.
		destruct (lt_dec a (c * b)).
		apply Nat.lt_le_incl in H0 as H'.
		apply between_exists in H'; auto.
		omega.
		omega.
	Qed.