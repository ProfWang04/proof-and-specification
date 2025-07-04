Require Import List.
Require Import FMapFacts.
Require Import Omega.
Require Import ListUtils.
Require Import OrderedTypeEx.
Require Import MapUtils.
Require Import Mem.
Require Import Pred.
Require Import FunctionalExtensionality.

Module MapMem (OT : UsualOrderedType) (M : S with Module E := OT).

  Module Map := M.
  Module Defs := MapDefs OT.

  Section MapMemSec.

    Variable V : Type.
    Definition mem_type := @mem Map.key OT.eq_dec V.

    Definition mm (m : Map.t V) : mem_type := fun a => Map.find a m.

    Lemma find_add_eq : forall m a (v : V),
      Map.find a (Map.add a v m) = Some v.

    Lemma find_add_ne : forall m a a' (v : V),
      a <> a' -> Map.find a (Map.add a' v m) = Map.find a m.

    Lemma find_remove_eq : forall m a,
      @Map.find V a (Map.remove a m) = None.

    Lemma find_remove_ne : forall m a a',
      a <> a' -> @Map.find V a (Map.remove a' m) = Map.find a m.

    Theorem mm_init :
      @emp _ OT.eq_dec _ (mm (Map.empty _)).

    Theorem mm_add : forall m (F : @pred Map.key OT.eq_dec V) a v,
      Map.find a m = None ->
      F (mm m) ->
      (F * a |-> v)%pred (mm (Map.add a v m)).

    Theorem mm_replace : forall m (F : @pred Map.key OT.eq_dec V) a v0 v,
      (a |-> v0 * F)%pred (mm m) ->
      (a |-> v * F)%pred (mm (Map.add a v m)).

    Theorem mm_remove : forall m (F : @pred Map.key OT.eq_dec V) a v,
      (a |-> v * F)%pred (mm m) ->
      F (mm (Map.remove a m)).

    Theorem mm_remove_none : forall m (F : @pred Map.key OT.eq_dec V) a,
      Map.find a m = None ->
      F (mm m) ->
      F (mm (Map.remove a m)).

    Theorem mm_find : forall m (F : @pred Map.key OT.eq_dec V) a v,
      (a |-> v * F)%pred (mm m) ->
      Map.find a m = Some v.

    Theorem mm_add_upd: forall k v m,
    mm (Map.add k v m) = Mem.upd (mm m) k v.

  End MapMemSec.

End MapMem.