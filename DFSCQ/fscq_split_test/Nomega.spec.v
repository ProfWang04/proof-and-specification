(* Make [omega] work for [N] *)

Require Import Arith Omega NArith.

Local Open Scope N_scope.

Hint Rewrite Nplus_0_r nat_of_Nsucc nat_of_Nplus nat_of_Nminus
  N_of_nat_of_N nat_of_N_of_nat
  nat_of_P_o_P_of_succ_nat_eq_succ nat_of_P_succ_morphism : N.

Theorem nat_of_N_eq : forall n m,
  nat_of_N n = nat_of_N m
  -> n = m.

Theorem Nneq_in : forall n m,
  nat_of_N n <> nat_of_N m
  -> n <> m.

Theorem Nneq_out : forall n m,
  n <> m
  -> nat_of_N n <> nat_of_N m.

Theorem Nlt_out : forall n m, n < m
  -> (nat_of_N n < nat_of_N m)%nat.

Theorem Nlt_in : forall n m, (nat_of_N n < nat_of_N m)%nat
  -> n < m.

Theorem Nge_out : forall n m, n >= m
  -> (nat_of_N n >= nat_of_N m)%nat.

Theorem Nge_in : forall n m, (nat_of_N n >= nat_of_N m)%nat
  -> n >= m.

Ltac nsimp H := simpl in H; repeat progress (autorewrite with N in H; simpl in H).

Ltac pre_nomega :=
  try (apply nat_of_N_eq || apply Nneq_in || apply Nlt_in || apply Nge_in); simpl;
    repeat (progress autorewrite with N; simpl);
    repeat match goal with
             | [ H : _ <> _ |- _ ] => apply Nneq_out in H; nsimp H
             | [ H : _ = _ -> False |- _ ] => apply Nneq_out in H; nsimp H
             | [ H : _ |- _ ] => (apply (f_equal nat_of_N) in H
               || apply Nlt_out in H || apply Nge_out in H); nsimp H
           end.

Ltac nomega := pre_nomega; omega || (unfold nat_of_P in *; simpl in *; omega).