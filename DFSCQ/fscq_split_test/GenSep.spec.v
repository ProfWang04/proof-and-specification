Require Import Mem.
Require Import Prog.
Require Import List.
Require Import Array.
Require Import Pred.
Require Import FunctionalExtensionality.
Require Import Word.
Require Import WordAuto.
Require Import Omega.
Require Import Ring.
Require Import SepAuto.
Require Import ListPred.
Require Import AsyncDisk.
Require Import ListUtils.

Set Implicit Arguments.

(**
 * This module is meant to generalize separation logic to arbitrary functions
 * from some address-like thing to some value-like thing.  The motivating use
 * case is in files: we want to think of the disk as a mapping from inode numbers
 * to file objects, where each file object includes metadata and the entire file
 * contents.  Current separation logic is not quite good enough, because we want
 * to have values that are bigger than a 512-byte block.
 *)

(**
 * list2mem is meant to convert a list representation of files into a memory-like
 * object that maps inode numbers (list positions) into files (or None, if the
 * inode number is too big).  For now, this always uses [addr] as the index.
 *)
Definition list2mem (A: Type) (l: list A) : @mem addr addr_eq_dec A :=
  fun a => selN (map (@Some A) l) a None.

Theorem list2mem_ptsto_bounds: forall A F (l: list A) i x,
  (F * i |-> x)%pred (list2mem l) -> wordToNat i < length l.


Theorem list2mem_oob : forall A (l : list A) i,
  wordToNat i >= length l
  -> (list2mem l) i = None.


Theorem list2mem_inbound: forall A F (l : list A) i x,
  (F * i |-> x)%pred (list2mem l)
  -> wordToNat i < length l.


Theorem list2mem_sel: forall A F (l: list A) i x def,
  (F * i |-> x)%pred (list2mem l)
  -> x = sel l i def.


Lemma listupd_memupd: forall A l i (v : A),
  wordToNat i < length l
  -> list2mem (upd l i v) = Mem.upd (list2mem l) i v.

Theorem list2mem_upd: forall A F (l: list A) i x y,
  (F * i |-> x)%pred (list2mem l)
  -> (F * i |-> y)%pred (list2mem (upd l i y)).


Theorem listapp_memupd: forall A l (a : A) (b : addr),
  length l <= wordToNat b
  -> list2mem (l ++ a :: nil) = Mem.upd (list2mem l) $ (length l) a.


Theorem list2mem_app: forall A (F : @pred addr (@weq addrlen) A) l a (b : addr),
  length l <= wordToNat b
  -> F (list2mem l)
  -> (F * $ (length l) |-> a)%pred (list2mem (l ++ a :: nil)).


Theorem list2mem_removelast_is : forall A l (def : A) (b : addr),
  l <> nil -> length l <= wordToNat b
  -> list2mem (removelast l) =
     fun i => if (wlt_dec i $ (length l - 1)) then Some (sel l i def) else None.


Theorem list2mem_removelast_list2mem : forall A (l : list A) (b : addr),
  l <> nil -> length l <= wordToNat b
  -> list2mem (removelast l) =
     fun i => if (weq i $ (length l - 1)) then None else (list2mem l) i.


Theorem list2mem_removelast: forall A F (l : list A) v (b : addr),
  l <> nil -> length l <= wordToNat b
  -> (F * $ (length l - 1) |-> v)%pred (list2mem l)
  -> F (list2mem (removelast l)).


Theorem list2mem_array: forall  A (l : list A) (b : addr),
  length l <= wordToNat b
  -> array $0 l $1 (list2mem l).


(* Alternative variants of [list2mem] that are more induction-friendly *)
Definition list2mem_off (A: Type) (start : nat) (l: list A) : (addr -> option A) :=
  fun a => if lt_dec (wordToNat a) start then None
                                         else selN (map (@Some A) l) (wordToNat a - start) None.

Theorem list2mem_off_eq : forall A (l : list A), list2mem l = list2mem_off 0 l.

Fixpoint list2mem_fix (A : Type) (start : nat) (l : list A) : (addr -> option A) :=
  match l with
  | nil => fun a => None
  | h :: l' => fun a => if eq_nat_dec (wordToNat a) start then Some h else list2mem_fix (S start) l' a
  end.

Lemma list2mem_fix_below : forall (A : Type) (l : list A) start a,
  wordToNat a < start -> list2mem_fix start l a = None.

Theorem list2mem_fix_off_eq : forall A (l : list A) n (b : addr),
  length l + n <= wordToNat b -> list2mem_off n l = list2mem_fix n l.

Theorem list2mem_fix_eq : forall A (l : list A) (b : addr),
  length l <= wordToNat b -> list2mem l = list2mem_fix 0 l.

Local Opaque pow2.

Theorem list2mem_fix_off_eq' : forall A (l : list A) n sz,
  length l + n <= pow2 sz -> sz = addrlen -> list2mem_off n l = list2mem_fix n l.

Theorem list2mem_fix_eq' : forall A (l : list A) sz,
  length l <= pow2 sz -> sz = addrlen -> list2mem l = list2mem_fix 0 l.


Lemma list2mem_nil_array : forall A (l : list A) start,
  array $ start l $1 (list2mem nil) -> l = nil.

Lemma list2mem_array_nil : forall A (l : list A) start (b : addr),
  start <= wordToNat b -> array $ start nil $1 (list2mem_fix start l) -> l = nil.

Theorem list2mem_array_eq': forall A (l' l : list A) (b : addr) start,
  array $ start l $1 (list2mem_fix start l')
  -> length l + start <= wordToNat b
  -> length l' + start <= wordToNat b
  -> l' = l.

Theorem list2mem_array_eq: forall A (l' l : list A) (b : addr),
  array $0 l $1 (list2mem l')
  -> length l <= wordToNat b
  -> length l' <= wordToNat b
  -> l' = l.


Theorem list2mem_array_app_eq: forall A V (F : @pred addr (@weq addrlen) V) (l l' : list A) a (b : addr),
  length l < wordToNat b
  -> length l' <= wordToNat b
  -> (array $0 l $1 * $ (length l) |-> a)%pred (list2mem l')
  -> l' = (l ++ a :: nil).


Definition array_ex A (vs : list A) i :=
  ( array $0 (firstn (wordToNat i) vs) $1 *
    array (i ^+ $1) (skipn (S (wordToNat i)) vs) $1)%pred.


Theorem array_except : forall V vs (def : V) (i : addr),
  wordToNat i < length vs
  -> array $0 vs $1 <=p=> (array_ex vs i) * (i |-> sel vs i def).


Theorem array_except_upd : forall V vs (v : V) (i : addr),
  wordToNat i < length vs
  -> array $0 (upd vs i v) $1 <=p=> (array_ex vs i) * (i |-> v).


Theorem list2mem_array_pick : forall V l (def : V) (i b : addr),
  length l <= wordToNat b
  -> wordToNat i < length l
  -> (array_ex l i * i |-> sel l i def)%pred (list2mem l).

Theorem list2mem_array_upd : forall V ol nl (v : V) (i b : addr),
  (array_ex ol i * i |-> v)%pred (list2mem nl)
  -> length ol <= wordToNat b
  -> length nl <= wordToNat b
  -> wordToNat i < length ol
  -> nl = upd ol i v.

Theorem list2mem_array_updN : forall V ol nl (v : V) (i b : addr),
  (array_ex ol i * i |-> v)%pred (list2mem nl)
  -> length ol <= wordToNat b
  -> length nl <= wordToNat b
  -> wordToNat i < length ol
  -> updN ol (wordToNat i) v = nl.

Theorem list2mem_array_removelast_eq : forall V (nl ol : list V) (b : addr),
  (array_ex ol $ (length ol - 1))%pred (list2mem nl)
  -> length ol <= wordToNat b
  -> length nl <= wordToNat b
  -> length ol > 0
  -> nl = removelast ol.


Theorem list2mem_array_exis : forall V l (def : V) i,
  (array_ex l i * i |-> sel l i def)%pred (list2mem l)
  -> (array_ex l i * i |->?)%pred (list2mem l).

Theorem list2mem_inj' : forall V (a b : list V) off sz,
  length a + off <= pow2 sz ->
  length b + off <= pow2 sz ->
  sz = addrlen ->
  list2mem_fix off a = list2mem_fix off b ->
  a = b.

Theorem list2mem_inj : forall V (a b : list V),
  goodSizeEq addrlen (length a) ->
  goodSizeEq addrlen (length b) ->
  list2mem a = list2mem b ->
  a = b.


(* Ltacs *)

Ltac rewrite_list2mem_pred_bound H :=
  let Hi := fresh in
  eapply list2mem_inbound in H as Hi.

Ltac rewrite_list2mem_pred_sel H :=
  let Hx := fresh in
  eapply list2mem_sel in H as Hx;
  try autorewrite with defaults in Hx;
  unfold sel in Hx.

Ltac rewrite_list2mem_pred_upd H:=
  let Hx := fresh in
  eapply list2mem_array_upd in H as Hx;
  [ unfold upd in Hx | .. ].

Ltac rewrite_list2mem_pred :=
  match goal with
  | [ H : (?prd * ?ix |-> ?v)%pred (list2mem ?l) |- _ ] =>
    rewrite_list2mem_pred_bound H;
    first [
      is_var v; rewrite_list2mem_pred_sel H; subst v |
      match prd with
      | array_ex ?ol ix =>
        is_var l; rewrite_list2mem_pred_upd H;
        [ subst l | clear H .. ]
      end ]
  end.

Ltac list2mem_ptsto_cancel :=
  match goal with
  | [ |- (_ * ?p |-> ?a)%pred (list2mem ?l) ] =>
    let Hx := fresh in
    assert (array $0 l $1 (list2mem l)) as Hx;
      [ eapply list2mem_array; eauto; try omega |
        pred_apply; erewrite array_except; unfold sel; clear Hx;
        try autorewrite with defaults; eauto ]
  end.

Ltac destruct_listmatch :=
  match goal with
    | [  H : context [ listmatch ?prd ?a _ ],
        H2 : ?p%pred (list2mem ?a) |- _ ] =>
      match p with
        | context [ (?ix |-> _)%pred ] =>
            let Hb := fresh in
            apply list2mem_inbound in H2 as Hb;
            extract_listmatch_at ix;
            clear Hb
      end
  end.

Ltac list2mem_cancel :=
    repeat rewrite_list2mem_pred;
    repeat destruct_listmatch;
    subst; eauto;
    try list2mem_ptsto_cancel; eauto.


Ltac list2mem_bound :=
   match goal with
    | [ H : ( _ * ?p |-> ?i)%pred (list2mem ?l) |- wordToNat ?p < length ?l' ] =>
          let Ha := fresh in assert (length l = length l') by solve_length_eq;
          let Hb := fresh in apply list2mem_inbound in H as Hb;
          eauto; (omega || setoid_rewrite <- Ha; omega); clear Hb Ha
  end.