Require Import Min.
Require Import Arith.
Require Import Word.
Require Import Prog ProgMonad.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Log.
Require Import Array.
Require Import List ListUtils.
Require Import Bool.
Require Import Setoid.
Require Import Rec.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import WordAuto.
Require Import RecArrayUtils LogRecArray.
Require Import GenSepN.
Require Import Balloc.
Require Import ListPred.
Require Import FSLayout.
Require Import AsyncDisk.
Require Import Inode.
Require Import GenSepAuto.
Require Import DiskSet.
Require Import DirTreeDef.
Require Import Bytes.
Require Import VBConv.
Require Import Fscq.Hashmap.
Require Import Errno.
Require Import PeanoNat.
Require Import Pred PredCrash.
Require Import Rounding.

Set Implicit Arguments.


(* Definitions *)
Definition attr := INODE.iattr.
Definition attr0 := INODE.iattr0.

Record proto_bytefile := mk_proto_bytefile {
  PByFData : list (list byteset)
}.
Definition proto_bytefile0 := mk_proto_bytefile nil.

Record unified_bytefile := mk_unified_bytefile {
  UByFData : list byteset
}.
Definition unified_bytefile0 := mk_unified_bytefile nil.

Record bytefile := mk_bytefile {
  ByFData : list byteset;
  ByFAttr : INODE.iattr
}.
Definition bytefile0 := mk_bytefile nil attr0.

Definition bfiledata2protobytefile fd : proto_bytefile :=
mk_proto_bytefile (map valuset2bytesets fd).

Definition protobytefile2unifiedbytefile pfy : unified_bytefile :=
mk_unified_bytefile (concat (PByFData pfy)). 

Definition unifiedbytefile2bytefiledata ufy len: list byteset :=
(firstn len (UByFData ufy)).

Definition unifiedbytefile2bytefile ufy len iattr: bytefile :=
mk_bytefile (firstn len (UByFData ufy)) iattr.

Definition bfiledata2bytefiledata fd len: list byteset:=
unifiedbytefile2bytefiledata (protobytefile2unifiedbytefile (bfiledata2protobytefile fd)) len.

Definition bfile2bytefile f len: bytefile:=
unifiedbytefile2bytefile (protobytefile2unifiedbytefile (bfiledata2protobytefile (DFData f))) len (DFAttr f).

Fixpoint upd_range {V} (m : @Mem.mem addr addr_eq_dec V) (a : addr) (l : list V) : @Mem.mem addr _ V :=
match l with
| nil => m
| h::t => upd_range (Mem.upd m a h) (a+1) t
end.


(* Definition ext_opt T (ov: option T) def :=
match ov with
| None => def
| Some v => v
end.
 *)
 
Definition some_strip {V} (o: option V) def: V :=
match o with
	| None => def
	| Some v => v
end.

Ltac split_hypothesis_helper:=
  match goal with
  | [ H: exists _, _ |- _ ] => destruct H
  | [ H: _ /\ _ |- _] => destruct H
  end.
  
Ltac split_hypothesis:= repeat split_hypothesis_helper. 


(* rep invariants *)
Definition proto_bytefile_valid f pfy: Prop :=
(PByFData pfy) = map valuset2bytesets (DFData f).

Definition unified_bytefile_valid pfy ufy: Prop := 
UByFData ufy = concat (PByFData pfy).

Definition bytefile_valid ufy fy: Prop :=
ByFData fy = firstn (length(ByFData fy)) (UByFData ufy).
  
Definition rep (f:dirfile) (fy:bytefile) :=
  exists pfy ufy,
    proto_bytefile_valid f pfy /\
    unified_bytefile_valid pfy ufy /\
    bytefile_valid ufy fy /\ 
    ByFAttr fy = DFAttr f /\
    #(INODE.ABytes (ByFAttr fy)) = length (ByFData fy) /\
    (roundup (length (ByFData fy)) valubytes = (length (DFData f)) * valubytes)%nat.

(* Definition byte_belong_to_file ilist byn inum:=
    (exists bn, BFILE.block_belong_to_file ilist bn inum (byn/valubytes)) /\
    byn < #(INODE.ABytes (INODE.IAttr (selN ilist inum INODE.inode0))). *)

(* Definition ptsto_subset_b {AT AEQ} (a : AT) (bs : byteset) : @pred AT AEQ byteset :=
(exists old, a |-> (fst bs, old) * [[incl (fst bs :: old) (fst bs :: snd bs)]])%pred. *)

(* Definition isSubset (bsl bsl': @Mem.mem addr addr_eq_dec byteset):= (forall a, bsl' a = bsl a \/ 
		(bsl a <> None /\ bsl' a = Some (fst (some_strip (bsl a) byteset0), fst (some_strip (bsl a) byteset0)::snd(some_strip (bsl a) byteset0)))).

Definition subset_invariant_bs (p: pred) : Prop :=
forall (bsl bsl': @Mem.mem addr addr_eq_dec byteset), bsl <> bsl' -> isSubset bsl bsl' -> p bsl -> p bsl'.
 *)
