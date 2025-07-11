Require Import Arith.
Require Import Bool.
Require Import List.
Require Import FMapInterface.
Require Import FMapFacts.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import Log.
Require Import Pred.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Word.
Require Import WordAuto.
Require Import Rec.
Require Import Array.
Require Import Eqdep_dec.
Require Import GenSep.

Set Implicit Arguments.
Import List.ListNotations.

(* XXX parameterize by length and stick in Word.v *)
Module addr_as_OT <: UsualOrderedType.
  Definition WIDTH:=addrlen.
  Definition t := word WIDTH.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition lt := @wlt WIDTH.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.

  Definition compare x y : Compare lt eq x y.

  Definition eq_dec := @weq WIDTH.
End addr_as_OT.

Module LOG (Map:FMapInterface.WSfun addr_as_OT).
  Definition memstate := Map.t valu.
  Definition ms_empty := Map.empty valu : memstate.
  Definition diskstate := list valu.
  Module MapFacts := WFacts_fun addr_as_OT Map.
  Module MapProperties := WProperties_fun addr_as_OT Map.

  Inductive logstate :=
  | NoTransaction (cur : diskstate)
  (* Don't touch the disk directly in this state. *)
  | ActiveTxn (old : diskstate) (cur : diskstate)
  (* A transaction is in progress.
   * It started from the first memory and has evolved into the second.
   * It has not committed yet. *)
  | FlushedTxn (old : diskstate) (cur : diskstate)
  (* A transaction has been flushed to the log, but not committed yet. *)
  | CommittedTxn (cur : diskstate)
  (* A transaction has committed but the log has not been applied yet. *).

  Record xparams := {
    (* The actual data region is everything that's not described here *)
    LogHeader : word addrlen; (* Store the header here *)
    LogCommit : word addrlen; (* Store true to apply after crash. *)

    LogStart : word addrlen; (* Start of log region on disk *)
    LogLen : word addrlen  (* Maximum number of entries in log; length but still use addr type *)
  }.

  Definition header_type := Rec.RecF ([("length", Rec.WordF addrlen)]).
  Definition header := Rec.data header_type.
  Definition mk_header (len : nat) : header := ($ len, tt).

(*
  Theorem header_sz_ok : Rec.len header_type <= valulen.

  Theorem plus_minus_header : Rec.len header_type + (valulen - Rec.len header_type) = valulen.

  Definition header_to_valu (h : header) : valu.
    set (zext (Rec.to_word h) (valulen - Rec.len header_type)) as r.
    rewrite plus_minus_header in r.
    refine r.
  Arguments header_to_valu : simpl never.

  Definition valu_to_header (v : valu) : header.
    apply Rec.of_word.
    rewrite <- plus_minus_header in v.
    refine (split1 _ _ v).

  Definition header_valu_id : forall h,
    valu_to_header (header_to_valu h) = h.

  Definition addr_per_block := valulen / addrlen.
  Definition descriptor_type := Rec.ArrayF (Rec.WordF addrlen) addr_per_block.
  Definition descriptor := Rec.data descriptor_type.
  Theorem descriptor_sz_ok : valulen = Rec.len descriptor_type.
    simpl. unfold addr_per_block. rewrite valulen_is. reflexivity.

  Definition descriptor_to_valu (d : descriptor) : valu.
    rewrite descriptor_sz_ok.
    apply Rec.to_word; auto.
  Arguments descriptor_to_valu : simpl never.

  Definition valu_to_descriptor (v : valu) : descriptor.
    rewrite descriptor_sz_ok in v.
    apply Rec.of_word; auto.

  Theorem valu_descriptor_id : forall v,
    descriptor_to_valu (valu_to_descriptor v) = v.
*)

  Definition indomain' (a : addr) (m : diskstate) := wordToNat a < length m.

  (* Check that the state is well-formed *)
  Definition valid_entries m (ms : memstate) :=
    forall a v, Map.MapsTo a v ms -> indomain' a m.

  Definition valid_size xp (ms : memstate) :=
    Map.cardinal ms <= wordToNat (LogLen xp).

  (* Replay the state in memory *)
  Definition replay' V (l : list (addr * V)) (m : list V) : list V :=
    fold_right (fun p m' => upd m' (fst p) (snd p)) m l.

  Definition replay (ms : memstate) (m : diskstate) : diskstate :=
    replay' (Map.elements ms) m.

  Definition data_rep (old : diskstate) : pred :=
    diskIs (list2mem old).

  Definition cur_rep (old : diskstate) (ms : memstate) (cur : diskstate) : @pred valu :=
    [[ cur = replay ms old ]]%pred.

  Theorem firstn_map : forall A B n l (f: A -> B),
    firstn n (map f l) = map f (firstn n l).

  Definition KIn V := InA (@Map.eq_key V).
  Definition KNoDup V := NoDupA (@Map.eq_key V).

  Lemma replay_sel_other : forall a ms m def,
    ~ Map.In a ms -> selN (replay ms m) (wordToNat a) def = selN m (wordToNat a) def.

  Lemma replay'_length : forall V (l:list (addr * V)) (m:list V),
      length m = length (replay' l m).
    induction l; [trivial|]; intro.
    unfold replay'; simpl.
    rewrite length_upd.
    eapply IHl.

  Lemma InA_NotInA_neq : forall T eq, Equivalence eq -> forall l (x y:T),
      InA eq x l -> ~ (InA eq y l) -> ~ eq x y.
    intros until 0; intros Eqeq; intros until 0; intros HIn HnotIn.
    rewrite InA_altdef, Exists_exists in *.
    intro Hcontra; apply HnotIn; clear HnotIn.
    elim HIn; clear HIn; intros until 0; intros HIn.
    destruct HIn as [HIn Heq_x_x0].
    exists x0. split; [apply HIn|].
    etransitivity; eauto; symmetry; auto.

  Lemma replay'_sel : forall V a (v: V) l m def,
    KNoDup l -> In (a, v) l -> wordToNat a < length m -> sel (replay' l m) a def = v.

  Lemma InA_eqke_In : forall V a v l,
    InA (Map.eq_key_elt (elt:=V)) (a, v) l -> In (a, v) l.

  Lemma mapsto_In : forall V a (v: V) ms,
    Map.MapsTo a v ms -> In (a, v) (Map.elements ms).

  Lemma replay_sel_in : forall a v ms m def,
    Map.MapsTo a v ms -> selN (replay ms m) (wordToNat a) def = v.

  Lemma replay_sel_invalid : forall a ms m def,
    ~ goodSize addrlen a -> selN (replay ms m) a def = selN m a def.

  Lemma replay'_len : forall V l m,
    length (@replay' V l m) = length m.

  Lemma replay_len : forall ms m,
    length (replay ms m) = length m.
  
  Lemma replay_add : forall a v ms m,
    replay (Map.add a v ms) m = upd (replay ms m) a v.


  Lemma valid_entries_add : forall a v ms m,
    valid_entries m ms -> indomain' a m -> valid_entries m (Map.add a v ms).


(* Testing.. *)

Definition do_two_writes a1 a2 v1 v2 rx :=
  Write a1 v1 ;; Write a2 v2 ;; rx tt.

Example two_writes: forall a1 a2 v1 v2 rx rec,
  {{ exists v1' v2' F,
     a1 |-> v1' * a2 |-> v2' * F
   * [[{{ a1 |-> v1 * a2 |-> v2 * F }} rx tt >> rec]]
   * [[{{ (a1 |-> v1' * a2 |-> v2' * F) \/
          (a1 |-> v1 * a2 |-> v2' * F) \/
          (a1 |-> v1 * a2 |-> v2 * F) }} rec >> rec]]
  }} do_two_writes a1 a2 v1 v2 rx >> rec.

Hint Extern 1 ({{_}} progseq (do_two_writes _ _ _ _) _ >> _) => apply two_writes : prog.

Example read_write: forall a v rx rec,
  {{ exists v' F,
     a |-> v' * F
   * [[{{ a |-> v * F }} (rx v) >> rec]]
   * [[{{ (a |-> v' * F)
       \/ (a |-> v * F) }} rec >> rec]]
  }} Write a v ;; x <- Read a ; rx x >> rec.

Example four_writes: forall a1 a2 v1 v2 rx rec,
  {{ exists v1' v2' F,
     a1 |-> v1' * a2 |-> v2' * F
   * [[{{ a1 |-> v1 * a2 |-> v2 * F }} rx >> rec]]
   * [[{{ (a1 |-> v1' * a2 |-> v2' * F)
       \/ (a1 |-> v1 * a2 |-> v2' * F)
       \/ (a1 |-> v1 * a2 |-> v2 * F) }} rec >> rec]]
  }} do_two_writes a1 a2 v1 v2 ;; do_two_writes a1 a2 v1 v2 ;; rx >> rec.

Example inc_up_to_5: forall a rx rec,
  {{ exists v F,
     a |-> v * F
   * [[{{ [[v < 5]] * a |-> (S v) * F
       \/ [[v >= 5]] * a |-> v * F }} rx >> rec]]
   * [[{{ a |-> v * F
       \/ a |-> S v * F }} rec >> rec]]
  }} x <- !a;
  If (lt_dec x 5) {
    a <-- (S x) ;; rx
  } else {
    rx
  } >> rec.

Example count_up: forall (n:nat) rx rec F,
  {{ F
   * [[ {{ F }} (rx n) >> rec ]]
   * [[ {{ F }} rec >> rec ]]
  }} r <- For i < n
     Loopvar l <- 0
     Continuation lrx
     Invariant
       F * [[ l=i ]]
         * [[ {{ F }} rx n >> rec ]]
         * [[ {{ F }} rec >> rec ]]
     OnCrash
       any
     Begin
       lrx (S l)
     Rof; rx r
  >> rec.


Require Import Log.

Inductive onestate :=
| One (a: nat).

Module Type ONEINT.
  (* Methods *)
  Parameter read : xparams -> prog nat.
  Parameter write : xparams -> nat -> prog unit.

  Parameter rep : xparams -> onestate -> pred.

  Axiom read_ok : forall xp v,
    {{rep xp (One v) /\
      [DataStart xp <= 3 < DataStart xp + DataLen xp]}}
    (read xp)
    {{r, rep xp (One v)
      /\ [r = Crashed \/ r = Halted v]}}.

  Axiom write_ok : forall xp v0 v,
    {{rep xp (One v0) /\
      [DataStart xp <= 3 < DataStart xp + DataLen xp]}}
    (write xp v)
    {{r, rep xp (One v)
      \/ ([r = Crashed] /\ rep xp (One v0))}}.
End ONEINT.

Module Oneint : ONEINT.
  Definition read xp := $(mem:
    (Call (fun m : mem => Log.begin_ok xp m));;
    x <- (Call (fun m : mem => Log.read_ok xp 3 (m, m)));
    (Call (fun m : mem => Log.commit_ok xp m m));;
    (Halt x)
  ).

  Definition write xp v := $(mem:
    (Call (fun m : mem => Log.begin_ok xp m));;
    (Call (fun m : mem => Log.write_ok xp 3 v (m, upd m 3 v)));;
    (Call (fun m : mem => Log.commit_ok xp m (upd m 3 v)))
  ).

  Definition rep xp (os: onestate) :=
    match os with
    | One a => exists lm,
      Log.rep xp (NoTransaction lm) /\
      [lm (DataStart xp + 3) = a]
    end%pred.

  Theorem read_ok : forall xp a (m:mem),
    {{rep xp (One a) /\
      [DataStart xp <= 3 < DataStart xp + DataLen xp]}}
    (read xp)
    {{r, rep xp (One a)
      /\ [r = Crashed \/ r = Halted a]}}.