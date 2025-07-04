Require Import AsyncDisk.
Require Import Prog.
Require Import Pred.
Require Import PredCrash.
Require Import Hoare.
Require Import Word.
Require Import Idempotent.
Require Import SepAuto.
Require Import Lock.

Set Implicit Arguments.

Parameter work : forall {T} (rx : unit -> prog T), prog T.
Parameter recover : forall {T} (rx : unit -> prog T), prog T.
Parameter rep : bool -> nat -> hashmap -> rawpred.
Axiom rep_xform : forall b n hm, crash_xform (rep b n hm) =p=> rep b n hm.

Theorem work_ok :
  {< v,
  PRE:hm          rep true v hm
  POST:hm' RET:r  rep true (v+1) hm'
  CRASH:hm'       rep true v hm' \/ rep false (v+1) hm' \/ rep true (v+1) hm'
  >} work.

Theorem recover_ok :
  {< v x,
  PRE:hm          rep x v hm
  POST:hm' RET:r  rep true v hm'
  CRASH:hm'       rep x v hm'
  >} recover.

Hint Extern 0 (okToUnify (rep _ _ _) (rep _ _ _)) => constructor : okToUnify.
Hint Extern 1 ({{_}} progseq work _) => apply work_ok : prog.
Hint Extern 1 ({{_}} progseq recover _) => apply recover_ok : prog.

Lemma instantiate_crash : forall idemcrash (F_ : rawpred) (hm_crash : hashmap),
  (fun hm => F_ * idemcrash hm) hm_crash =p=> F_ * idemcrash hm_crash.

Theorem work_recover_ok :
  {X<< v,
  PRE:hm          rep true v hm
  POST:hm' RET:r  rep true (v+1) hm'
  REC:hm' RET:r   rep true v hm' \/ rep true (v+1) hm'
  >>X} work >> recover.