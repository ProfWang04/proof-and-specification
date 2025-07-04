Require Import Word.
Require Import Arith.
Require Import Eqdep_dec.
Require Import AsyncDisk.
Require Import List ListUtils.
Require Import Omega.
Require Import FunctionalExtensionality.
Import EqNotations.

Set Implicit Arguments.



Definition byte := word 8.
Definition bytes n := word (n * 8).

Definition word2bytes nbits nbytes (H : nbits = nbytes * 8) (w : word nbits) : bytes nbytes :=
  eq_rect nbits word w (nbytes*8) H.
  
Definition byte0 := natToWord 8 0.
Definition bytes0 := (word2bytes 0 eq_refl WO).
  
Definition byte2bytes (b: byte) : bytes 1 := word2bytes 1 eq_refl b.

Definition bcombine (sz1 : nat) (bs1 : bytes sz1) (sz2 : nat) (bs2 : bytes sz2) : bytes (sz1 + sz2).
  unfold bytes in *.
  rewrite Nat.mul_add_distr_r in *.
  exact (Word.combine bs1 bs2).

Definition bsplit1 (sz1 sz2 : nat) (bs : bytes (sz1 + sz2)) : bytes sz1.
  unfold bytes in *.
  rewrite Nat.mul_add_distr_r in *.
  exact (split1 _ _ bs).

Definition bsplit2 (sz1 sz2 : nat) (bs : bytes (sz1 + sz2)) : bytes sz2.
  unfold bytes in *.
  rewrite Nat.mul_add_distr_r in *.
  exact (split2 _ _ bs).

Definition bsplit1_dep sz sz1 sz2 (v : bytes sz) (H : sz = sz1 + sz2) : bytes sz1 :=
  bsplit1 sz1 sz2 (eq_rect sz bytes v _ H).

Definition bsplit2_dep sz sz1 sz2 (v : bytes sz) (H : sz = sz1 + sz2) : bytes sz2 :=
  bsplit2 sz1 sz2 (eq_rect sz bytes v _ H).

Hint Rewrite Word.combine_split : bytehints.
Hint Rewrite split1_combine : bytehints.
Hint Rewrite split2_combine : bytehints.
Hint Rewrite eq_rect_nat_double : bytehints.
Hint Rewrite <- (eq_rect_eq_dec eq_nat_dec) : bytehints.

Theorem bcombine_bsplit : forall sz1 sz2 (bs : bytes (sz1 + sz2)),
  bcombine (bsplit1 sz1 sz2 bs) (bsplit2 sz1 sz2 bs) = bs.

Theorem bsplit1_bcombine : forall sz1 sz2 (bs : bytes sz1) (z : bytes sz2),
  bsplit1 sz1 sz2 (bcombine bs z) = bs.

Theorem bsplit2_bcombine : forall sz1 sz2 (bs : bytes sz1) (z : bytes sz2),
  bsplit2 sz1 sz2 (bcombine bs z) = z.

Program Fixpoint bsplit_list sz (w: bytes sz) : list byte :=
    match sz with
    | O => nil
    | S sz => bsplit1_dep 1 sz w _ :: bsplit_list (bsplit2_dep 1 sz w _)
    end.

Program Fixpoint bcombine_list (l: list byte): bytes (length l) :=
match l with
 | nil => bytes0
 | h::l' => bcombine (byte2bytes h) (bcombine_list l')
end.

Theorem list2bytes2list: forall (l: list byte), bsplit_list (bcombine_list l) = l.

Lemma bsplit_list_len: forall sz (b: bytes sz), length (bsplit_list b) = sz.

Lemma bsplit_list_preserve: forall sz (b1 b2: bytes sz), b1 = b2 -> bsplit_list b1 = bsplit_list b2.
Theorem bytes2list2bytes: forall sz (b: bytes sz) H, 
bcombine_list (bsplit_list b) = rew H in b.

Notation "'valubytes'" := (Valulen.valubytes).
Notation "'valubytes_is'" := (Valulen.valubytes_is).

Definition valu2bytes (v : valu) : bytes valubytes.
  refine (@word2bytes valulen valubytes _ v).
  rewrite valulen_is. rewrite valubytes_is. reflexivity.

Definition bytes2valu (v : bytes valubytes) : valu.
  rewrite valulen_is.
  unfold bytes in *.
  rewrite valubytes_is in *.
  exact v.

Theorem bytes2valu2bytes : forall v, valu2bytes (bytes2valu v) = v.

Theorem valu2bytes2valu : forall v, bytes2valu (valu2bytes v) = v.

Lemma valu2bytes_preserve: forall v1 v2, v1 = v2 -> valu2bytes v1 = valu2bytes v2.
Lemma bcombine_list_contr: forall a l, 
bcombine (byte2bytes a) (bcombine_list l) = bcombine_list (a::l).
Lemma selN_O_bsplit_list: forall sz (bs: bytes (1 + sz)) def,
selN (bsplit_list bs) 0 def = bsplit1 1 sz bs.

Lemma byte2bytes_eq: forall b,
byte2bytes b = b.
  