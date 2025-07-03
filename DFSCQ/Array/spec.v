Require Import Mem.
Require Import ListUtils.
Require Import List Omega Ring Word Pred PredCrash.
Require Import Prog Hoare SepAuto BasicProg.
Require Import FunctionalExtensionality.
Require Import WordAuto.
Require Import AsyncDisk.

Import ListNotations.

Set Implicit Arguments.
Set Default Proof Using "Type".


(** * A generic array predicate: a sequence of consecutive points-to facts *)

Section GenArray.

  Variable V VP : Type.
  Variable pts : addr -> V -> @pred addr addr_eq_dec VP.

  Infix "|-?->" := pts (at level 35) : pred_scope.

  Fixpoint arrayN (a : addr) (vs : list V) : @pred _ addr_eq_dec _ :=
    match vs with
      | nil => emp
      | v :: vs' => a |-?-> v * arrayN (S a) vs'
    end%pred.
