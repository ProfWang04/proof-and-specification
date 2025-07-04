Require Import Prog.
Require Import Mem Pred.
Require Import Word.
Require Import PredCrash.
Require Import AsyncDisk.

Set Implicit Arguments.

Hint Constructors fail_step step exec.

Definition buf_ne sz1 (buf1: word sz1) sz2 (buf2: word sz2)
  := forall (H: sz1 = sz2), eq_rect _ _ buf1 _ H <> buf2.

Lemma buf_ne_sz_same : forall sz (buf1 buf2: word sz),
    buf1 <> buf2 ->
    buf_ne buf1 buf2.

Lemma buf_ne_sz_neq : forall sz1 sz2 (buf1: word sz1) (buf2: word sz2),
    sz1 <> sz2 ->
    buf_ne buf1 buf2.

Hint Resolve buf_ne_sz_same buf_ne_sz_neq.

Lemma possible_sync_refl : forall A AEQ (m: @mem A AEQ valuset),
    possible_sync m m.

Hint Resolve possible_sync_refl.

Definition hash_safe_dec hm h sz (buf: word sz) : {hash_safe hm h buf} + {~hash_safe hm h buf}.

Inductive hashmap_wf : hashmap -> Prop :=
| empty_hashmap_wf : hashmap_wf empty_hashmap
| upd_hashmap_wf : forall hm sz (buf: word sz),
    hashmap_wf hm ->
    hashmap_wf (upd_hashmap hm (hash_fwd buf) (existT _ _ buf)).

Lemma hashmap_wf_get : forall hm sz1 (buf1: word sz1) sz2 (buf2: word sz2),
    hashmap_wf hm ->
    hashmap_get hm (hash_fwd buf1) = Some (existT _ _ buf2) ->
    hash_fwd buf1 = hash_fwd buf2.

Lemma de_morgan : forall (P Q:Prop),
    ~(P \/ Q) ->
    ~P /\ ~Q.

Theorem not_hash_safe_conflict : forall hm sz (buf: word sz),
    hashmap_wf hm ->
    ~hash_safe hm (hash_fwd buf) buf ->
    exists sz' (buf': word sz'),
      buf_ne buf buf' /\
      hash_fwd buf = hash_fwd buf'.

Hint Constructors hashmap_wf.

Theorem exec_preserves_hashmap_wf : forall T (p: prog T) d vm hm d' vm' hm' v,
    hashmap_wf hm ->
    exec d vm hm p (Finished d' vm' hm' v) ->
    hashmap_wf hm'.

Hint Resolve exec_preserves_hashmap_wf.
Hint Resolve tt.

(**
 * XXX [exec_progress] is no longer true because type equality is not
 * decidable for [VarGet].
 *)

(*
Theorem exec_progress : forall T (p: prog T) d hm,
    hashmap_wf hm ->
    (exists d' hm' v', exec d hm p (Finished d' hm' v')) \/
    (exec d hm p (Failed T)) \/
    (exists sz1 (buf1: word sz1) sz2 (buf2: word sz2),
        buf_ne buf1 buf2 /\
        hash_fwd buf1 = hash_fwd buf2).
*)