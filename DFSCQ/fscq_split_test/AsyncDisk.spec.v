Require Import Arith.
Require Import Word.
Require Import List.
Require Import Mem.
Require Import Eqdep_dec.
Require Import FunctionalExtensionality.
Require Import String.
Require HexString.

Set Implicit Arguments.

(* Disk value and address types  *)

Notation "'valubytes_real'" := (HexString.to_nat "0x1000"). (* 4KB *)
Notation "'valulen_real'" := (valubytes_real * 8)%nat.

Module Type VALULEN.
  Parameter valulen : nat.
  Parameter valubytes : nat.
  Axiom valulen_is : valulen = valulen_real.
  Axiom valubytes_is : valubytes = valubytes_real.
End VALULEN.

Module Valulen : VALULEN.
  Definition valulen := valulen_real.
  Definition valubytes := valubytes_real.
  Theorem valulen_is: valulen = valulen_real.
  Theorem valubytes_is: valubytes = valubytes_real.
End Valulen.

Definition addrlen := 64.
Notation "'valulen'" := (Valulen.valulen).
Notation "'valulen_is'" := (Valulen.valulen_is).
Notation "'valu'" := (word valulen).

Theorem valulen_nonzero : valulen <> 0.

Theorem valulen_gt_0 : valulen > 0.

Theorem valulen_wordToNat_natToWord : # (natToWord addrlen valulen) = valulen.

(* tight bound for valulen *)
Theorem valulen_bound : valulen < pow2 16.


Notation "'addr'" := nat.
Notation "'waddr'" := (word addrlen).

Definition addr_eq_dec := Nat.eq_dec.
Definition waddr_eq_dec := @weq addrlen.

Definition waddrring := wring addrlen.
Add Ring waddrring : waddrring (decidable (weqb_sound addrlen), constants [wcst]).

Notation "'valuset'" := (valu * list valu)%type.

(* Async-disk *)
Definition rawdisk := @mem addr addr_eq_dec valuset.
Definition vsmerge (vs : valuset) : list valu := fst vs :: snd vs.


(* Hashing *)
Definition hashlen := 32.
Parameter hash_fwd : forall sz, word sz -> word hashlen.
Definition default_valu : valu := $0.
Definition default_hash := hash_fwd default_valu.

(* A hashmap holds all keys that Hash has been called on, maps hash values to keys. *)
Inductive hashmap : Type :=
  | empty_hashmap : hashmap
  | upd_hashmap : hashmap -> word hashlen -> { sz : nat & word sz } -> hashmap.

Definition upd_hashmap' hm h sz k : hashmap :=
  upd_hashmap hm h (existT _ sz k).

Fixpoint hashmap_get hm h : option {sz : nat & word sz} :=
  if (weq h default_hash)
    then Some (existT _ _ default_valu) else
    (match hm with
    | empty_hashmap => None
    | upd_hashmap hm' h' k' =>  if (weq h' h)
                                then Some k'
                                else hashmap_get hm' h
    end).


Lemma upd_hashmap_eq : forall hm h k,
  h <> default_hash ->
  hashmap_get (upd_hashmap hm h k) h = Some k.

Lemma upd_hashmap'_eq : forall hm h sz k,
  h <> default_hash ->
  hashmap_get (upd_hashmap' hm h k) h = Some (existT _ sz k).

Hint Rewrite upd_hashmap_eq.


Definition hash_safe hm h sz (k : word sz) :=
  hashmap_get hm h = None \/ hashmap_get hm h = Some (existT _ _ k).

(* Converting between hash and valu.*)
Lemma hashlen_valulen: hashlen + (valulen - hashlen) = valulen.

Definition hash_to_valu (h: word hashlen) : valu.
  set (zext h (valulen-hashlen)) as r.
  rewrite hashlen_valulen in r.
  apply r.

Lemma hash_to_valu_inj : forall a b,
  hash_to_valu a = hash_to_valu b ->
  a = b.
  unfold hash_to_valu.
  unfold eq_rec_r, eq_rec.
  rewrite <- hashlen_valulen.
  intros.
  rewrite <- (eq_rect_eq_dec eq_nat_dec) in H.
  rewrite <- (eq_rect_eq_dec eq_nat_dec) in H.
  unfold zext in *.
  apply combine_inj in H.
  intuition.


Definition sync_mem AT AEQ (m : @mem AT AEQ valuset) : @mem AT AEQ valuset :=
  fun a => match m a with
    | None => None
    | Some (v, _) => Some (v, nil)
    end.

Definition sync_addr AT AEQ (m : @mem AT AEQ valuset) a : @mem AT AEQ valuset :=
  fun a' => if AEQ a a' then
    match m a with
    | None => None
    | Some (v, _) => Some (v, nil)
    end else m a'.

Lemma sync_addr_ne : forall AT AEQ (m : @mem AT AEQ valuset) a a',
  a <> a' ->
  (sync_addr m a) a' = m a'.

Lemma sync_addr_eq : forall AT AEQ (m : @mem AT AEQ valuset) a a' vs,
  a = a' ->
  m a' = Some vs ->
  (sync_addr m a) a' = Some (fst vs, nil).
