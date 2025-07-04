Require Import Ascii String Omega OrderedTypeEx.


(**** String_as_OT borrowed from Fiat *)

Lemma nat_compare_eq_refl : forall x, Nat.compare x x = Eq.
  intros; apply Nat.compare_eq_iff; trivial.

Hint Rewrite <- nat_compare_lt : nat_comp_hints.
Hint Rewrite <- nat_compare_gt : nat_comp_hints.
Hint Rewrite    Nat.compare_eq_iff : nat_comp_hints.
Hint Rewrite <- Nat.compare_eq_iff : nat_comp_hints.
Hint Rewrite    nat_compare_eq_refl : nat_comp_hints.

Ltac autorewrite_nat_compare :=
  autorewrite with nat_comp_hints in *.

Lemma nat_compare_consistent :
  forall n0 n1,
    { Nat.compare n0 n1 = Lt /\ Nat.compare n1 n0 = Gt }
    + { Nat.compare n0 n1 = Eq /\ Nat.compare n1 n0 = Eq }
    + { Nat.compare n0 n1 = Gt /\ Nat.compare n1 n0 = Lt }.

Module String_as_OT <: UsualOrderedType.
  Definition t := string.

  Fixpoint string_compare str1 str2 :=
    match str1, str2 with
      | EmptyString, EmptyString => Eq
      | EmptyString, _           => Lt
      | _, EmptyString           => Gt
      | String char1 tail1, String char2 tail2 =>
        match Nat.compare (nat_of_ascii char1) (nat_of_ascii char2) with
          | Eq => string_compare tail1 tail2
          | Lt => Lt
          | Gt => Gt
        end
    end.

  Lemma string_compare_eq_refl : forall x, string_compare x x = Eq.
    intro x;
    induction x;
      simpl; trivial;
      autorewrite_nat_compare.
      trivial.

  Ltac comparisons_minicrush :=
    autorewrite_nat_compare;
    match goal with
      | [ |- context [Nat.compare ?a ?b] ] =>
        let H := fresh in
        first [
            assert (Nat.compare a b = Eq) as H by (autorewrite_nat_compare; omega) |
            assert (Nat.compare a b = Lt) as H by (autorewrite_nat_compare; omega) |
            assert (Nat.compare a b = Gt) as H by (autorewrite_nat_compare; omega)
        ]; rewrite H; intuition
    end.

  Ltac destruct_comparisons :=
    repeat match goal with
             | [ H: match ?pred ?a ?b with
                      | Lt => _ | Gt => _ | Eq => _ end = _
                 |- _] =>
               let H := fresh in
               destruct (pred a b) eqn:H;
                 try discriminate
           end.

  Ltac exfalso_from_equalities :=
    match goal with
      | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] => assert (b = c) by congruence; discriminate
    end.

  Definition eq := @eq string.

  Hint Resolve string_compare_eq_refl.

  Lemma eq_Eq : forall x y, x = y -> string_compare x y = Eq.

  Lemma nat_of_ascii_injective :
    forall a b, nat_of_ascii a = nat_of_ascii b <-> a = b.

  Lemma Eq_eq : forall x y, string_compare x y = Eq -> x = y.

  Lemma Eq_eq_iff : forall x y, x = y <-> string_compare x y = Eq.

  Definition eq_refl := @eq_refl string.

  Definition eq_sym := @eq_sym string.

  Definition eq_trans := @eq_trans string.

  Definition lt x y :=
    string_compare x y = Lt.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.

  Lemma lt_not_eq : forall x y, lt x y -> ~ eq x y.

  Lemma Lt_Gt : forall x y, string_compare x y = Gt <-> string_compare y x = Lt.

  Definition compare x y : OrderedType.Compare lt eq x y.

  Definition eq_dec : forall (x y: string), { x = y } + { x <> y }.

End String_as_OT.