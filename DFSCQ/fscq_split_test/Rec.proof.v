  Proof.
    intros.
    unfold well_formed in *.
    inversion H.
    split.
    rewrite firstn_length_l; omega.
    rewrite Forall_forall; intros.
    apply in_firstn_in in H2.
    rewrite Forall_forall in H1.
    apply H1.
    assumption.
  Qed.
  Proof.
    intros.
    unfold well_formed in *.
    inversion H0.
    split.
    rewrite firstn_length_l; omega.
    rewrite Forall_forall in *; intros.
    eapply H2.
    eapply in_firstn_in; eauto.
  Qed.
  Proof.
    intros.
    unfold well_formed in *.
    inversion H.
    split.
    rewrite skipn_length; omega.
    rewrite Forall_forall; intros.
    apply in_skipn_in in H2.
    rewrite Forall_forall in H1.
    apply H1.
    assumption.
  Qed.
  Proof.
    intros.
    unfold well_formed in *.
    inversion H.
    split.
    simpl in *.
    omega.
    rewrite Forall_forall in *; intros.
    apply H1.
    constructor; assumption.
  Qed.
  Proof.
    intros.
    unfold well_formed.
    split; auto.
    apply length_nil in H.
    subst.
    auto.
  Qed.
  Proof.
    intros n f. inversion f.
  Qed.
  Proof.
    intros t n n' ft ne f. inversion f; subst.
    contradiction ne. reflexivity.
    apply H3.
  Qed.
  Proof.
    induction t; intros.
    contradiction (empty_field_in p).
    destruct a as [n0 ft0]. destruct r as [v0 r'].
    simpl in v. simpl. destruct (string_dec n0 n).
    trivial. apply IHt.
  Qed.
  Proof.
    induction t; intros n1 p1 n2 p2 r v neq.
    contradiction (empty_field_in p1).
    destruct a as [n0 ft0]. destruct r as [v0 r'].
    simpl in v. simpl.
    destruct (string_dec n0 n2); destruct (string_dec n0 n1);
      subst; trivial.
    contradiction neq. auto.
    apply IHt. assumption.
  Qed.
  Proof.
    einduction ft using type_rect_nest; simpl.
    reflexivity.
    induction n.
    auto.
    intro w. simpl in *. rewrite IHn. rewrite IHt. apply combine_split.
    apply IHt.
    intro w. rewrite word0. trivial.
    simpl. intro w.
    rewrite IHt. rewrite IHt0. apply combine_split.
  Qed.
  Proof.
    einduction ft using type_rect_nest.
    reflexivity.
    induction n; intros v H; simpl in v.
    destruct H. destruct v; try discriminate. reflexivity.
    simpl in *. destruct H. destruct v; try discriminate.
    rewrite split1_combine. rewrite split2_combine.
    inversion H0. subst. rewrite IHt by assumption. rewrite IHn by auto. trivial.
    2: instantiate (1 := fun rt => forall v,
      (fix well_formed' {rt : rectype} : data (RecF rt) -> Prop :=
        match rt as rt return (data (RecF rt) -> Prop) with
        | [] => fun _ => True
        | (_, ft) :: t' => fun r =>
          let (r0, r') := r in well_formed r0 /\ well_formed' r'
        end) rt v ->
      (fix word2rec (t : rectype) (w : word (len (RecF t))) : recdata t :=
        match t as t return word (len (RecF t)) -> recdata t with
        | nil => fun _ => tt
        | (_, ft) :: t' => fun w =>
          (of_word (split1 (len ft) (len (RecF t')) w),
           word2rec t' (split2 (len ft) (len (RecF t')) w))
        end w)
        rt
        ((fix rec2word {t : rectype} (r : recdata t) : word (len (RecF t)) :=
          match t as t return recdata t -> word (len (RecF t)) with
          | nil => fun _ => WO
          | (_, _) :: _ => fun r =>
            let (v, r') := r in combine (to_word v) (rec2word r')
          end r) rt v) = v).
    apply IHt.
    simpl. intros v t. destruct v. trivial.
    simpl. intro v. destruct v. intro Hrl. destruct Hrl.
    rewrite split1_combine. rewrite split2_combine.
    rewrite IHt0 by assumption. rewrite IHt by assumption. trivial.
  Qed.
  Proof.
    intros.
    rewrite <- Rec.of_to_id with (v := a) by auto.
    rewrite <- Rec.of_to_id with (v := b) by auto.
    congruence.
  Qed.
  Proof.
    intros.
    rewrite <- Rec.to_of_id with (w := a).
    rewrite <- Rec.to_of_id with (w := b).
    congruence.
  Qed.
  Proof.
    intros.
    generalize w.
    rewrite H.
    intros.
    simpl in w0.
    apply length_nil.
    reflexivity.
  Qed.
  Proof.
    einduction ft using type_rect_nest.
    simpl. trivial.
    simpl. induction n.
    split; trivial.
    intro w.
    edestruct IHn.
    split. simpl. rewrite H. trivial.
    simpl. constructor. apply IHt. assumption.
    apply IHt.
    simpl. trivial.
    simpl. intro w. split.
    apply IHt. apply IHt0.
  Qed.
  Proof.
    apply of_word_length.
  Qed.
  Proof.
    induction n; intros; simpl.
    reflexivity.
    f_equal.
    apply IHn.
  Qed.
  Proof.
    simpl.
    induction l; simpl; induction n; intros; auto; try omega.
    f_equal.
    apply IHl.
    omega.
  Qed.
  Proof.
    simpl.
    induction l; simpl; induction n; intros; auto.
    + induction m; simpl; auto.
      induction n; try rewrite IHn;
      apply combine_wzero.
    + f_equal.
      apply IHl.
  Qed.
  Proof.
    intros.
    rewrite plus_assoc.
    rewrite Nat.add_sub_assoc.
    rewrite <- plus_assoc.
    rewrite plus_comm.
    rewrite <- Nat.add_sub_assoc by omega.
    rewrite Nat.sub_diag; rewrite <- plus_n_O.
    rewrite Nat.add_sub_assoc.
    rewrite plus_comm.
    rewrite <- Nat.add_sub_assoc by omega.
    rewrite Nat.sub_diag; rewrite <- plus_n_O.
    reflexivity.
    replace (lenft) with (1 * lenft) at 1 by omega.
    apply Nat.mul_le_mono_r; omega.
    replace (lenft) with (1 * lenft) at 3 by omega.
    rewrite <- Nat.mul_sub_distr_r.
    apply Nat.mul_le_mono_r; omega.
  Qed.
  Proof.
    induction l; intros; try omega.
    unfold of_word in *; fold (@of_word ft) in *.
    destruct idx; simpl.
    - f_equal. clear IHl.
      unfold word_selN, middle.

      destruct (lt_dec 0 (S l)); [|omega].
      generalize (word_selN_helper (len ft) l0).
      replace (S l * len ft - len ft - 0 * len ft) with (l * len ft) by lia.
      simpl; intros.
      erewrite <- eq_rect_eq.
      reflexivity.

    - rewrite <- IHl by omega; clear IHl.
      f_equal.
      unfold word_selN.
      destruct (lt_dec (S idx) (S l)); try omega.
      destruct (lt_dec idx l); try omega.

      unfold middle.

      generalize (word_selN_helper (len ft) l0).
      generalize (word_selN_helper (len ft) l1).
      replace (S l * len ft - len ft - S idx * len ft)
        with (l * len ft - len ft - idx * len ft) by lia.
      generalize (l * len ft - len ft - idx * len ft).

      intros.
      fold len. fold Init.Nat.mul.
      f_equal.
      generalize dependent e0.
      generalize dependent e.
      generalize (len ft + n); clear n.
      generalize dependent w; simpl.
      generalize (idx * len ft).
      generalize (l * len ft); clear H l0 l1 l def idx.
      generalize (len ft); clear ft.
      intros.

      assert (n + n0 = n + (n1 + n2)) as e0' by omega.
      replace ((eq_rect (n + n0) (fun n => word n) w (n + n1 + n2) e0))
        with (match plus_assoc _ _ _ in _ = N return word N with
              | refl_equal => (eq_rect (n+n0) (fun n => word n) w (n+(n1+n2)) e0')
              end).

      rewrite <- split2_iter.
      f_equal.
      generalize dependent e0'; clear e0.
      rewrite <- e; intros.
      repeat rewrite <- eq_rect_eq.
      reflexivity.

      destruct (Nat.add_assoc n n1 n2).
      destruct e0.
      repeat rewrite <- eq_rect_eq.
      reflexivity.
  Qed.
  Proof.
    intros.

    rewrite Nat.add_sub_assoc. rewrite plus_comm. rewrite <- Nat.add_sub_assoc by omega.
    rewrite Nat.sub_diag. omega.

    rewrite <- Nat.mul_sub_distr_r. replace (lenft) with (1 * lenft) at 1 by omega.
    apply Nat.mul_le_mono_r; omega.
  Qed.
  Proof.
    intros.

    rewrite Nat.add_sub_assoc. rewrite plus_comm. rewrite <- Nat.add_sub_assoc by omega.
    rewrite Nat.sub_diag. omega.

    apply Nat.mul_le_mono_r; omega.
  Qed.
  Proof.
    unfold word_updN; simpl; intros.
    destruct (lt_dec idx l); auto.
    exfalso; omega.
  Qed.
  Proof.
    simpl; intros.
    unfold word_updN.
    destruct (lt_dec idx l); try omega; clear H.

    unfold eq_rec_r, eq_rec.
    rewrite eq_rect_word_offset.
    repeat rewrite eq_rect_nat_double.

    generalize (word_updN_helper1 (len ft) l0).
    generalize (word_updN_helper2 (len ft) l0).

    generalize dependent l.
    induction idx; simpl; intros.
    - destruct l; try omega.
      unfold of_word; fold (@of_word ft).
      unfold to_word; fold (@to_word ft).
      replace ((fix word2arrayf (n : nat) (w0 : word (n * len ft)) {struct n} : 
         list (data ft) :=
           match n as n0 return (word (len (ArrayF ft n0)) -> data (ArrayF ft n0)) with
           | 0 => fun _ : word (len (ArrayF ft 0)) => []
           | S n' =>
               fun w1 : word (len (ArrayF ft (S n'))) =>
               of_word (split1 (len ft) (n' * len ft) w1)
               :: word2arrayf n' (split2 (len ft) (n' * len ft) w1)
           end w0) l (split2 (len ft) (l * len ft) w))
        with (@of_word (ArrayF ft l) (split2 (len ft) (l * len ft) w)) by reflexivity.
      simpl.

      repeat rewrite eq_rect_nat_double.
      rewrite eq_rect_combine.
      f_equal.
      rewrite eq_rect_split2.
      rewrite eq_rect_nat_double.
      rewrite <- (eq_rect_eq_dec eq_nat_dec).
      match goal with
      | [ |- _ = ?r ] =>
        replace (r)
          with (@to_word (ArrayF ft l) (of_word (split2 (len ft) (len (ArrayF ft l)) w)))
          by reflexivity
      end.
      rewrite to_of_id.
      reflexivity.

    - destruct l; try omega.
      unfold of_word; fold (@of_word ft). fold Init.Nat.mul. fold len.
      unfold to_word; fold (@to_word ft). fold Init.Nat.mul. fold len.
      fold recdata. fold data.
      match goal with
      | [ |- _ = match updN (_ :: ?x) _ _ with | nil => _ | v0 :: v' => _ end ] =>
        replace (x) with (@of_word (ArrayF ft l) (split2 (len ft) (l * len ft) w)) by reflexivity
      end.
      simpl.

      rewrite to_of_id.
      assert (idx < l) as Hidx by omega.
      specialize (IHidx l (split2 (len ft) (l * len ft) w) Hidx).
      clear l0.

      generalize dependent e; generalize dependent e0. simpl.
      replace (len ft + l * len ft - (len ft + idx * len ft))
        with (len ft + (l * len ft - len ft - idx * len ft)) by
        ( rewrite Nat.sub_add_distr;
          rewrite minus_plus;
          rewrite <- word_updN_helper1 by omega;
          lia ).
      intros.
      rewrite eq_rect_combine.
      rewrite eq_rect_split2.
      repeat rewrite eq_rect_nat_double.

      repeat match goal with
      | [ |- context[(eq_trans ?a ?b)] ] =>
        generalize (eq_trans a b); intros
      end.
      clear e0.

      rewrite <- combine_split with (sz1:=len ft) (sz2:=idx * len ft)
        (w:=(split1 (len ft + idx * len ft) (len ft + (l * len ft - len ft - idx * len ft))
        (eq_rect (len ft + l * len ft) (fun y : nat => word y) w
           (len ft + idx * len ft + (len ft + (l * len ft - len ft - idx * len ft))) 
           (eq_sym e)))).
      assert (len ft + (idx * len ft + (len ft + (l * len ft - len ft - idx * len ft))) =
              len ft + idx * len ft + (len ft + (l * len ft - len ft - idx * len ft)))
        as Hassoc by lia.
      rewrite (combine_assoc _ _ _ Hassoc).
      rewrite eq_rect_word_match.
      rewrite eq_rect_nat_double.
      rewrite eq_rect_combine.
      f_equal.

      rewrite split1_iter with (Heq:=eq_sym Hassoc).
      rewrite eq_rect_word_match.
      rewrite eq_rect_nat_double.
      generalize dependent (eq_trans (eq_sym e) (eq_sym Hassoc)).
      replace (idx * len ft + (len ft + (l * len ft - len ft - idx * len ft)))
        with (l * len ft) by lia.
      intros.
      rewrite <- (eq_rect_eq_dec eq_nat_dec). reflexivity.

      unfold to_word in IHidx; fold (@to_word ft) in IHidx; simpl in IHidx.
      fold data in IHidx. fold len in IHidx. fold Init.Nat.mul in IHidx.
      erewrite <- IHidx.

      repeat rewrite eq_rect_split2.
      assert (len ft + (idx * len ft + len ft + (l * len ft - idx * len ft - len ft)) =
        len ft + (idx * len ft + len ft) + (l * len ft - idx * len ft - len ft))
        as Hs2iter by lia.
      rewrite split2_iter with (Heq:=Hs2iter).
      rewrite eq_rect_word_match.
      rewrite eq_rect_nat_double.

      rewrite <- eq_rect_combine.
      rewrite eq_rect_nat_double.

      repeat match goal with
      | [ |- context[eq_sym ?a] ] => generalize (eq_sym a); intros
      | [ |- context[eq_trans ?a ?b] ] => generalize (eq_trans a b); intros
      | [ |- context[eq_rect_split2_helper ?a ?b] ] => generalize (eq_rect_split2_helper a b); intros
      end; clear.

      generalize dependent idx; intro idx.
      replace (l * len ft - idx * len ft - len ft)
        with (l * len ft - len ft - idx * len ft) by lia.
      intros.
      f_equal; clear.
      f_equal; clear.

      erewrite split1_split2.
      rewrite eq_rect_word_match.
      rewrite eq_rect_nat_double.
      f_equal; clear.

      assert (len ft + (l * len ft - len ft - idx * len ft) = l * len ft - idx * len ft)
        as Hr by lia.
      generalize dependent e0; generalize dependent e7.
      rewrite Hr.
      intros.
      f_equal; clear.
      f_equal; clear.
      apply UIP_dec; exact eq_nat_dec.

      f_equal; clear.
      generalize dependent idx; intro idx.
      replace (len ft + (idx * len ft + len ft))
        with (len ft + idx * len ft + len ft) by lia.
      intros.
      f_equal; clear.
      f_equal; clear.
      apply UIP_dec; exact eq_nat_dec.
      apply UIP_dec; exact eq_nat_dec.
      Grab Existential Variables.
      rewrite plus_assoc; reflexivity.
      lia.
      lia.
  Qed.
  Proof. intros. lia. Qed.

  Fact word_shift_helper2 : forall n l, l > 0 -> n + (l - 1) * n = l * n.
  Proof. intros. destruct l; simpl; try rewrite <- minus_n_O; omega. Qed.

  Fact word_shift_helper3 : forall a b c, a * c + (c + b * c) = (a + 1 + b) * c.
  Proof. intros. lia. Qed.

  Fact word_shift_helper4 : forall a b c, (a + 1 + b) * c = a * c + c + b * c.
  Proof. intros. lia. Qed.

  Theorem word_selN_shift_gt_0 : forall idx off n w,
    word_selN_shift (idx + 1 + off) n idx w = split1 n ((idx + off) * n)
      (eq_rect _ word (wrshift w (idx * n)) _ (eq_sym (word_shift_helper1 n idx off))).
  Proof.
    intros idx off n.
    assert (idx + 1 + off = S (idx + off)) as H by omega.
    generalize_proof.
    rewrite H.
    intros.
    eq_rect_simpl.
    reflexivity.
  Qed.
  Proof.
    intros.
    generalize dependent H1.
    generalize dependent w.
    generalize dependent H.
    intros H.
    rewrite <- H.
    intros.
    subst w' w''.
    eq_rect_simpl.
    unfold middle.
    rewrite <- combine_split with (w := w).
    repeat f_equal; rewrite combine_split; auto.
    erewrite <- eq_rect_word_match.
    rewrite combine_end.
    reflexivity.
  Qed.
  Proof. intros. subst. reflexivity. Qed.

  Theorem eq_rect_both : forall x y z (H1 : x = z) (H2 : y = z) wa wb,
    wa = eq_rect y word wb x (eq_rect_both_helper H1 H2) -> eq_rect x word wa z H1 = eq_rect y word wb z H2.
  Proof.
    intros. subst.
    eq_rect_simpl.
    reflexivity.
   Qed.
  Proof. intros. omega. Qed.

  Theorem split1_eq_rect_combine_partial : forall a b c d H (wa : word a) (wc : word c),
    split1 (a + b) d
      (eq_rect (a + c) word (combine wa wc) (a + b + d) H) =
        combine wa (split1 b d (eq_rect _ word wc _ (split1_eq_rect_combine_partial_helper a b c d H))).
  Proof.
    intros a b c d H.
    assert (c = b + d) by omega; subst c.
    intros.
    erewrite <- split1_combine; f_equal.
    eq_rect_simpl.
    erewrite combine_assoc.
    rewrite eq_rect_word_match.
    rewrite combine_split.
    reflexivity.
  Qed.
  Proof. intros. omega. Qed.

  Fact combine_eq_rect_combine : forall a b c d H (wa : word a) (wb : word b) (wa' : word d),
    combine (eq_rect (a + b) word (combine wa wb) c H) wa' =
    eq_rect _ word (combine wa (combine wb wa')) _ (combine_eq_rect_combine_helper a b d H).
  Proof.
    intros a b c d H.
    subst c.
    intros.
    eq_rect_simpl.
    erewrite combine_assoc, eq_rect_word_match.
    reflexivity.
  Qed.
  Proof.
    intros a b c H.
    assert (c = b) by omega; subst.
    intros.
    eq_rect_simpl.
    apply split2_combine.
  Qed.
  Proof.
    intros.
    eq_rect_simpl.
    rewrite word_selN_shift_gt_0.
    generalize_proof.
    replace ((idx + off) * n) with (idx * n + off * n) by lia.
    intros HH.
    unfold wrshift.
    eq_rect_simpl.
    erewrite combine_eq_rect2.
    rewrite eq_rect_combine_dist3 with (w := w); eq_rect_simpl.
    erewrite combine_eq_rect_combine; eq_rect_simpl.
    erewrite split2_eq_rect_combine; eq_rect_simpl.
    repeat erewrite combine_assoc, eq_rect_word_match; eq_rect_simpl.
    unfold middle.
    repeat progress (rewrite eq_rect_combine ||
                     rewrite split1_combine  ||
                     rewrite split2_combine).
    reflexivity.
    Grab Existential Variables.
    all : lia.
  Qed.
  Proof.
    intros.
    generalize dependent w.
    remember (l - idx - 1) as off.
    assert (l = (idx + 1+ off)) by omega.
    subst l.
    intros w.
    unfold word_selN.
    destruct lt_dec; try omega.
    erewrite word_selN_shift_eq_middle.
    generalize dependent (word_selN_helper (len ft) l).
    replace ((idx + 1 + off) * len ft - len ft - idx * len ft) with (off * len ft) by lia.
    intros HH.
    f_equal.
    apply eq_rect_both; eq_rect_simpl.
    reflexivity.
  Qed.
  Proof.
    intros.
    unfold word_selN'.
    rewrite <- word_selN_shift_equiv; auto.
    apply word_selN_equiv; auto.
  Qed.
  Proof.
    unfold word_updN_shift.
    intros idx off n.
    generalize dependent (word_shift_helper1 n idx off).
    replace (idx + 1 + off) with (S (idx + off)) by omega.
    intros.
    eq_rect_simpl.
    f_equal.
    f_equal.
    apply mult_comm.
  Qed.
  Proof.
    unfold word_mask; destruct l; auto; intros.
    erewrite combine_eq_rect2.
    repeat f_equal.
    generalize_proof.
    intros HH; rewrite HH; auto.
    Grab Existential Variables.
    simpl; rewrite <- minus_n_O.
    reflexivity.
  Qed.
  Proof.
    intros off n idx.
    generalize dependent (word_shift_helper3 idx off n).
    replace (idx + 1 + off) with (S (idx + off)) by omega.
    intros H.
    unfold word_mask.
    rewrite wnot_wlshift.
    eq_rect_simpl.
    erewrite split1_eq_rect_eq1; f_equal.
    eq_rect_simpl.
    rewrite split1_eq_rect_combine_partial; f_equal.
    rewrite wnot_combine, wnot_ones.
    rewrite split1_eq_rect_combine_partial; f_equal.
    erewrite wzero_dist, wzero_rev, <- combine_wzero.
    repeat rewrite wnot_eq_rect.
    eq_rect_simpl.
    rewrite wnot_combine, split1_combine.
    apply wnot_zero.
    Grab Existential Variables.
    all : lia.
  Qed.
  Proof.
    intros.
    erewrite eq_rect_combine_dist3 with (w := w).
    erewrite wnot_word_mask_l_gt_0 by omega.
    unfold wand.
    unfold eq_rec.
    erewrite <- eq_rect_bitwp'; f_equal.
    repeat erewrite <- combine_bitwp; f_equal.
    - rewrite wand_comm, wand_wones.
      reflexivity.
    - rewrite wand_comm, wand_wzero.
      rewrite wand_comm, wand_wones.
      reflexivity.
  Qed.
  Proof.
    intros.
    assert ((idx + 1 + off) * n = idx * n + n + off * n) as Hc by lia.
    erewrite eq_rect_combine_dist3 with (w := w).
    erewrite word_updN_shift_l_gt_0.
    erewrite wand_wnot_word_mask_w.
    unfold wlshift, zext.
    eq_rect_simpl.
    rewrite split1_combine.
    rewrite eq_rect_combine_assoc'.
    rewrite split2_combine.
    unfold wor.
    rewrite eq_rect_bitwp_1.
    f_equal.
    replace (eq_rect ((idx + 1 + off) *n) word (split1 _ (idx * n) _) _ _)
      with (combine (wzero (idx * n)) (combine v (wzero (off * n)))).
    - repeat rewrite <- combine_bitwp.
      repeat rewrite wor_wzero.
      repeat try (rewrite wor_comm, wor_wzero).
      reflexivity.
    - erewrite split1_eq_rect_eq1.
      repeat (eq_rect_simpl; erewrite split1_eq_rect_combine_partial; f_equal).
      erewrite wzero_dist, wzero_rev, <- combine_wzero.
      eq_rect_simpl.
      symmetry; apply split1_combine.
    Grab Existential Variables.
    all : lia.
  Qed.
  Proof. intros. omega. Qed.

  Theorem word_updN_abs : forall idx off ft w v,
    let H := word_shift_helper3 idx off (len ft) in
    let H1 := word_shift_helper4 idx off (len ft) in
    let w' := eq_rec _ word w _ (eq_sym H) in
    let w'' := eq_rec _ word w _ H1 in
    @word_updN ft (idx + 1 + off) idx w v = eq_rec _ word (
      combine (split1 (idx * len ft) (len ft + off * len ft) w')
        (combine v (split2 (idx * len ft + len ft) (off * len ft) w''))) _ H.
  Proof.
    unfold word_updN; simpl.
    intros.
    destruct lt_dec; try omega.
    repeat eexists.
    eq_rect_simpl; apply eq_rect_both.
    rewrite eq_rect_word_offset; eq_rect_simpl.
    rewrite eq_rect_combine; f_equal.
    + erewrite eq_rect_split1_eq2.
      eq_rect_simpl; f_equal.
      apply eq_rect_both.
      eq_rect_simpl; reflexivity.
    + apply eq_rect_both.
      rewrite eq_rect_combine.
      rewrite eq_rect_split2.
      eq_rect_simpl.
      repeat (try reflexivity; f_equal; eq_rect_simpl; try apply eq_rect_both).
    Grab Existential Variables.
    all : simpl; lia.
  Qed.
  Proof.
    intros l idx ft w v H.
    remember (l - idx - 1) as off.
    assert (l = idx + 1 + off) by omega.
    subst l.
    erewrite word_updN_shift_abs by auto.
    erewrite word_updN_abs.
    repeat f_equal.
  Qed.
  Proof.
    intros.
    unfold word_updN'.
    rewrite word_updN_shift_equiv; auto.
    apply word_updN_equiv; auto.
  Qed.
  Proof.
    destruct ft.
    - exact ($ 0).
    - apply repeat.
      apply reczero.
      exact n.
    - induction l; cbn.
      exact tt.
      destruct a.
      constructor; eauto.
  Defined.
  Proof.
    induction n; simpl; auto.
    rewrite <- IHn; clear IHn.
    unfold of_word at 1 3.
    rewrite split1_zero.
    rewrite split2_zero.
    reflexivity.
  Qed.
  Proof.
    intros.
    induction ft; cbn.
    auto.
    destruct a; cbn.
    rewrite <- IHft; clear IHft.
    unfold of_word at 1 3.
    rewrite split1_zero.
    rewrite split2_zero.
    reflexivity.
  Qed.
  Proof.
    intros.
    einduction ft using type_rect_nest.
    auto.
    rewrite of_word_zero_list.
    rewrite IHt.
    eauto.
    rewrite of_word_zero_rec.
    apply IHt.
    cbn; auto.
    cbn. f_equal; auto.
  Qed.
  Proof.
    intros.
    simpl.
    nia.
  Qed.
  Proof.
    intros.
    shatterer.
  Qed.
  Proof.
    intros.
    reflexivity.
  Qed.
  Proof.
    intros.
    induction n.
    simpl.
    rewrite <- (eq_rect_eq_dec eq_nat_dec).
    rewrite combine_0; reflexivity.
    simpl len in *.
    rewrite of_word_cons.
    simpl.
    erewrite IHn.
    rewrite of_word_cons.

    rewrite <- combine_split with (sz1:=len t) (sz2:=n * len t) (w := v).
    f_equal.
    rewrite split1_combine.
    erewrite combine_assoc.
    rewrite eq_rect_word_match.
    unfold eq_rec.
    rewrite eq_rect_nat_double.
    rewrite eq_rect_combine.
    rewrite split1_combine.
    reflexivity.

    rewrite split2_combine.
    erewrite combine_assoc.
    rewrite eq_rect_word_match.
    unfold eq_rec.
    rewrite eq_rect_nat_double.
    rewrite eq_rect_combine.
    rewrite split2_combine.
    f_equal.

    Grab Existential Variables.
    all: omega.
  Qed.
  Proof.
    intros.
    unfold len_add.
    apply combine_app'.
  Qed.
  Proof.
    intros.
    inversion t; auto.
  Qed.
  Proof.
    intros.
    induction n.
    simpl.
    reflexivity.

    simpl plus in *.
    rewrite of_word_cons.
    simpl.
    rewrite of_word_cons.
    unfold eq_rec_r in *.
    f_equal.
    erewrite split1_iter.
    rewrite eq_rect_word_match.
    rewrite eq_rect_nat_double.
    simpl in *.
    f_equal.
    erewrite eq_rect_split1_eq2.
    f_equal.
    erewrite IHn.
    rewrite eq_rect_split2.
    erewrite split1_split2.
    repeat f_equal.
    rewrite eq_rect_word_match.
    rewrite eq_rect_nat_double.
    unfold eq_rec.
    f_equal.
    apply proof_irrelevance.

    Grab Existential Variables.
    all: try omega.
    simpl.
    nia.
  Qed.
  Proof.
    intros.
    induction n.
    simpl.
    unfold eq_rec_r.
    rewrite <- (eq_rect_eq_dec eq_nat_dec).
    reflexivity.

    simpl plus in *.
    rewrite of_word_cons.
    simpl.

    unfold eq_rec_r in *.
    erewrite IHn.
    rewrite eq_rect_split2.
    erewrite split2_iter.
    rewrite eq_rect_word_match.
    rewrite eq_rect_nat_double.
    unfold eq_rec.
    repeat f_equal.
    apply proof_irrelevance.

    Grab Existential Variables.
    omega.
    simpl; nia.
  Qed.