Require Import Arith Omega NArith Nomega Word.


Ltac set_evars :=
  repeat match goal with
              | [ |- context[?e] ] => is_evar e; let H := fresh in set (H := e)
            end.

Ltac subst_evars :=
  repeat match goal with
              | [ H := ?e |- _ ] => is_evar e; subst H
            end.

Ltac set_evars_in H :=
  repeat match type of H with
              | context[?e] => is_evar e; let E := fresh in set (E := e) in H
            end.



Theorem f_neq : forall {A B : Type} (f : A -> B) x y, f x <> f y -> x <> y.

Create HintDb W2Nat discriminated. (* Straightforward simplifications *)

Hint Rewrite Npow2_nat : W2Nat.

Lemma N2Nat_word : forall sz n, (n < Npow2 sz)%N -> wordToNat (NToWord sz n) = N.to_nat n.

Lemma N2Nat_word'
   : forall sz n, goodSize sz (N.to_nat n) -> wordToNat (NToWord sz n) = N.to_nat n.
Hint Rewrite NToWord_nat : W2Nat.

Lemma wordToNat_N : forall sz (w:word sz), N.to_nat (wordToN w) = wordToNat w.
Hint Rewrite wordToNat_N : W2Nat.

Hint Rewrite natToWord_wordToNat : W2Nat.

Theorem plus_ovf_l : forall sz x y, $ (wordToNat (natToWord sz x) + y) = natToWord sz (x + y).

Theorem plus_ovf_r : forall sz x y, $ (x + wordToNat (natToWord sz y)) = natToWord sz (x + y).

Theorem plus_ovf_lN : forall sz x y, NToWord sz (wordToN (NToWord sz x) + y) = NToWord sz (x + y).

Theorem plus_ovf_rN : forall sz x y, NToWord sz (x + wordToN (NToWord sz y)) = NToWord sz (x + y).

Hint Rewrite plus_ovf_l plus_ovf_r : W2Nat.

Theorem mul_ovf_l : forall sz x y, $ (wordToNat (natToWord sz x) * y) = natToWord sz (x * y).

Theorem mul_ovf_r : forall sz x y, $ (x * wordToNat (natToWord sz y)) = natToWord sz (x * y).

Theorem mul_ovf_lN : forall sz x y, NToWord sz (wordToN (NToWord sz x) * y) = NToWord sz (x * y).

Theorem mul_ovf_rN : forall sz x y, NToWord sz (x * wordToN (NToWord sz y)) = NToWord sz (x * y).

Hint Rewrite mul_ovf_l mul_ovf_r : W2Nat.

(* XXX subtraction *)

Theorem Wneq_out : forall sz (n m:word sz),
  n <> m -> wordToNat n <> wordToNat m.

Lemma divmod_Ndiv_eucl :
  forall a b Sb,
    Pos.to_nat Sb = S b ->
    N.to_nat (fst (N.pos_div_eucl a (N.pos Sb))) =
    fst (Nat.divmod (Pos.to_nat a) b 0 b) /\
    N.to_nat (snd (N.pos_div_eucl a (N.pos Sb))) =
    b - snd (Nat.divmod (Pos.to_nat a) b 0 b).

(* The standard library should really define this... *)
Lemma Ninj_div : forall a a' : N, N.to_nat (a / a') = N.to_nat a / N.to_nat a'.

Lemma Ninj_mod : forall a a' : N, N.to_nat a' <> 0 ->
  N.to_nat (a mod a') = (N.to_nat a) mod (N.to_nat a').

Hint Rewrite Ninj_div N2Nat.inj_mul N2Nat.inj_add N2Nat.inj_sub : W2Nat.

Lemma wordToNat_mult : forall sz (n m:word sz),
  NToWord sz (wordToN n * wordToN m)%N = $ (wordToNat n * wordToNat m).

Hint Rewrite wordToNat_mult : W2Nat.

Lemma div_le : forall a b, b <> 0 -> a / b <= a.



Theorem wordToNat_div : forall sz (a b : word sz), wordToNat b <> 0 ->
  wordToNat (NToWord sz (wordToN a / wordToN b)) = wordToNat a / wordToNat b.


Lemma lt_ovf : forall sz x y, x < wordToNat (natToWord sz y) -> x < y /\ goodSize sz x.


Ltac autorewrite_fast_goal_w2nat :=
  set_evars; (rewrite_strat (topdown (hints W2Nat))); subst_evars;
  try autorewrite_fast_goal_w2nat.

Ltac autorewrite_fast_w2nat :=
  match goal with
  | [ H: _ |- _ ] =>
    set_evars_in H; (rewrite_strat (topdown (hints W2Nat)) in H); subst_evars;
    [ try autorewrite_fast_w2nat | try autorewrite_fast_goal_w2nat .. ]
  | [ |- _ ] => autorewrite_fast_goal_w2nat
  end.

(* Do some substitutions [subst] won't. XXX: this doesn't seem very principled; I should think it through *)
Ltac nat_subst :=
  repeat match goal with
  | [ H: # _ = # _ |- _ ] => idtac
  | [ H: # _ = _ |- _ ] => rewrite H
  | [ H: _ = # _ |- _ ] => rewrite <- H
  end.

Ltac goodsizes := idtac;
  repeat match goal with
  | [ w: word ?sz |- _ ] =>
    match goal with
    | [ H: goodSize sz (wordToNat w) |- _ ] => fail 1
    | _ => idtac
    end;
    assert (goodSize sz (wordToNat w)) by (apply wordToNat_bound)
  end.

Ltac word2nat_simpl :=
  try (apply nat_of_N_eq || apply Nneq_in || apply Nlt_in || apply Nge_in || apply N2Nat.inj || apply wordToNat_inj); (* XXX still causes hangs: simpl; *)
  unfold wplus, wminus, wmult, wdiv, wmod, wordBin in *;
  repeat match goal with
  | [ H : _ <> _ |- _ ] => (apply Nneq_out in H || apply Wneq_out in H); nsimp H
  | [ H : _ = _ -> False |- _ ] => (apply Nneq_out in H || apply Wneq_out in H); nsimp H
  | [ H : _ |- _ ] => (apply (f_equal nat_of_N) in H || apply (f_equal (@wordToNat _)) in H
             || apply Nlt_out in H || apply Nge_out in H); nsimp H
  end;
  try autorewrite_fast_w2nat;
  repeat match goal with
  | [ H : _ < _ |- _ ] => apply lt_ovf in H; destruct H
  end;
  nat_subst;
  goodsizes.

Ltac word2nat_solve := unfold goodSize in *; subst;
  (omega ||
   congruence ||
   (apply f_equal; word2nat_solve) ||
   ((apply div_le; [| word2nat_auto] ||
     apply zero_lt_pow2 ||
     apply wordToNat_bound || apply wordToNat_good ||
     apply Nat.mod_upper_bound ||
     idtac
    ); solve [auto]
   ) ||
   (apply Nat.div_lt_upper_bound; solve [word2nat_auto]) ||
   (eapply le_lt_trans; [(apply div_le || apply Nat.mod_le) |]; solve [word2nat_auto])
  )

(* XXX does this actually rewrite from the inside out? *)
with word2nat_rewrites :=
  repeat ((match goal with
  | H : context[wordToNat (natToWord ?sz ?n)] |- _ =>
    rewrite (@wordToNat_natToWord_idempotent' sz n) in H; [|clear H]
  | H : context[wordToNat (NToWord ?sz ?n)] |- _ =>
    rewrite (@N2Nat_word' sz n) in H; [|clear H]
  | H : context[wordToNat (NToWord ?sz (wordToN ?a / wordToN ?b))] |- _ =>
    rewrite (@wordToNat_div sz a b); [|clear H]
  | H : context[N.to_nat (?a mod ?b)] |- _ =>
    rewrite (Ninj_mod a b); [|clear H]
  end
  || rewrite wordToNat_natToWord_idempotent'
  || rewrite N2Nat_word'
  || rewrite wordToNat_div
  || rewrite Ninj_mod); word2nat_simpl)

with word2nat_auto :=
  intros; word2nat_simpl; word2nat_rewrites; try word2nat_solve;
  repeat match goal with
  | [ H : _ |- _ ] => apply wordToNat_inj in H
  end.

Lemma wdiv_lt_upper_bound :
  forall sz (a b c:word sz), b <> $0 -> (a < b ^* c)%word -> (a ^/ b < c)%word.

Lemma wmod_upper_bound :
  forall sz (a b:word sz), b <> $0 -> (a ^% b < b)%word.

Lemma wlt_mult_inj : forall sz (a b c:word sz),
  (a < b ^* c)%word -> wordToNat a < wordToNat b * wordToNat c.

Lemma test_1: forall sz (a: word sz), a = a ^+ $ 0.