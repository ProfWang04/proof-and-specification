Proof.
  intros n0 n1;
  destruct (lt_eq_lt_dec n0 n1) as [ [_lt | _eq] | _lt ];
  [ constructor 1; constructor 1  | constructor 1; constructor 2 | constructor 2 ];
  split;
  autorewrite_nat_compare;
  intuition.
Defined.
  Proof.
    intros; subst; auto.
  Qed.
  Proof.
    intros a b; split; intro H;
    [ apply (f_equal ascii_of_nat) in H;
      repeat rewrite ascii_nat_embedding in H
    | apply (f_equal nat_of_ascii) in H ]; trivial.
  Qed.
  Proof.
    induction x;
      destruct y;
      simpl;
      first [ discriminate
            | intros;
              f_equal;
              destruct_comparisons;
              autorewrite_nat_compare;
              rewrite nat_of_ascii_injective in *
            | idtac ];
      intuition.
  Qed.
  Proof.
    intros; split; eauto using eq_Eq, Eq_eq.
  Qed.
  Proof.
    intros x y z;
    generalize x z;
    clear x z;

    induction y;
    destruct x;
    destruct z;
      intros;
      unfold lt in *;
      simpl in *;
      first [ discriminate
            | destruct_comparisons; comparisons_minicrush
            | trivial ]; intuition.
  Qed.
  Proof.
    unfold lt, not in *;
    intros;
    rewrite Eq_eq_iff in *;
    exfalso_from_equalities.
  Qed.
  Proof.
    intros x;
    induction x as [ | x0 x' Hind ];
      intros y;
      destruct y as [ | y0 y' ];

      simpl;
      split;
      first [ discriminate | trivial ];

      destruct (nat_compare_consistent
                  (nat_of_ascii x0)
                  (nat_of_ascii y0))
          as [ [ (H1, H2) | (H1, H2) ] | (H1, H2) ];
        rewrite H1, H2;
        try rewrite Hind;
        auto.
  Qed.
  Proof.
    destruct (string_compare x y) eqn:comp;
      unfold lt;
      [ constructor 2; apply Eq_eq
      | constructor 1
      | constructor 3; apply Lt_Gt];
      trivial.
  Defined.
  Proof.
    exact string_dec.
  Defined.