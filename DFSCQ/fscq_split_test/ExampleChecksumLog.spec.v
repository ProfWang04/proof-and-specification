Require Import Hashmap.
Require Import Prog.
Require Import BasicProg.
Require Import Word.
Require Import Pred.
Require Import PredCrash.
Require Import Mem.
Require Import Cache.
Require Import List.
Require Import Hoare.
Require Import SepAuto.
Require Import HashmapProg.

Set Implicit Arguments.


Definition block1 : addr := $0.
Definition block2 : addr := $1.
Definition hash_block : addr := $2.

(* Representations for an example with two log blocks. *)
(* block1 and block2 are synced, hash_block has some valid hash *)
Definition any_hash_rep (a b a' b' : valu) (d : @mem addr (@weq addrlen) valuset) hm :
    @pred addr (@weq addrlen) valuset :=
  (exists hv,
    [[ (block1 |-> (a, nil) *
     block2 |-> (b, nil) *
     hash_block |-> (hash_to_valu hv, nil))%pred d ]] *
    [[ hash_list_rep (b' :: a' :: nil) hv hm ]])%pred.

(* hash_block has the valid hash of block1 and block2 values *)
Definition rep a b (d : @mem addr (@weq addrlen) valuset) hm :
    @pred addr (@weq addrlen) valuset :=
  any_hash_rep a b a b d hm.

(* After a crash:
  - block1 and block2 can be anything
  - hash_block can be one of:
    - hash of old values
    - hash of new values but unsynced
    - hash of new values and synced *)
Definition crep (a b a' b' : valu) hm :
    @pred addr (@weq addrlen) valuset :=
  (exists hv hv',
    block1 |->? *
    block2 |->? *
    ( hash_block |-> (hash_to_valu hv, nil) *
        [[ hash_list_rep (b :: a :: nil) hv hm ]] \/
      hash_block |-> (hash_to_valu hv', hash_to_valu hv :: nil) *
        [[ hash_list_rep (b :: a :: nil) hv hm /\ hash_list_rep (b' :: a' :: nil) hv' hm ]] \/
      hash_block |-> (hash_to_valu hv', nil) *
        [[ hash_list_rep (b' :: a' :: nil) hv' hm ]]))%pred.


(* Example "log" implementation using checksums *)
Definition put T cs d1 d2 rx : prog T :=
  cs <- BUFCACHE.write block1 d1 cs;
  cs <- BUFCACHE.write block2 d2 cs;
  h <- hash_list (d1 :: d2 :: nil);
  cs <- BUFCACHE.write hash_block (hash_to_valu h) cs;
  cs <- BUFCACHE.sync block1 cs;
  cs <- BUFCACHE.sync block2 cs;
  cs <- BUFCACHE.sync hash_block cs;
  rx cs.

Definition get T cs rx : prog T :=
  let^ (cs, d1) <- BUFCACHE.read block1 cs;
  let^ (cs, d2) <- BUFCACHE.read block2 cs;
  rx ^(d1, d2).

Definition recover T cs rx : prog T :=
  let^ (cs, d1) <- BUFCACHE.read block1 cs;
  let^ (cs, d2) <- BUFCACHE.read block2 cs;
  let^ (cs, diskh) <- BUFCACHE.read hash_block cs;
  h <- hash_list (d1 :: d2 :: nil);
  If (weq diskh (hash_to_valu h)) {
    rx cs
  } else {
    cs <- put cs default_valu default_valu;
    rx cs
  }.


Theorem put_ok : forall cs d1 d2,
  {< d d1_old d2_old d1_old' d2_old',
  PRE:hm
    BUFCACHE.rep cs d *
    any_hash_rep d1_old d2_old d1_old' d2_old' d hm
  POST:hm' RET:cs'
    exists d',
      BUFCACHE.rep cs' d' *
      rep d1 d2 d' hm'
  CRASH:hm_crash
    exists cs' d',
      BUFCACHE.rep cs' d' *
      [[ (crep d1_old' d2_old' d1 d2 hm_crash)%pred d' ]]
  >} put cs d1 d2.

Hint Extern 1 ({{_}} progseq (put _ _ _) _) => apply put_ok : prog.


Theorem get_ok : forall cs,
  {< d d1 d2,
  PRE:hm
    BUFCACHE.rep cs d *
    rep d1 d2 d hm
  POST:hm' RET:^(d1', d2')
    exists cs', BUFCACHE.rep cs' d *
    rep d1 d2 d hm' *
    [[ d1 = d1' /\ d2 = d2' ]]
  CRASH:hm'
    exists cs', BUFCACHE.rep cs' d *
    rep d1 d2 d hm'
  >} get cs.

(* block1 and block2 get some value, and hash_block points to a valid hash of  *)
Definition after_crash_pred (v1 v2 : valu) hm :
    @pred addr (@weq addrlen) valuset :=
  (exists a b hv,
      block1 |-> (a, nil) *
      block2 |-> (b, nil) *
      hash_block |-> (hash_to_valu hv, nil) *
    [[ hash_list_rep (v2 :: v1 :: nil) hv hm ]])%pred.

Lemma crash_xform_would_recover_either_pred : forall v1 v2 v1' v2' hm,
  crash_xform (crep v1 v2 v1' v2' hm) =p=>
    after_crash_pred v1 v2 hm \/
    after_crash_pred v1' v2' hm.

Hint Rewrite crash_xform_would_recover_either_pred : crash_xform.


Theorem recover_ok : forall cs,
  {< d1_old d2_old d1 d2,
  PRE:hm
    exists d,
      BUFCACHE.rep cs d *
      [[ crash_xform (crep d1_old d2_old d1 d2 hm)%pred d ]]
  POST:hm' RET:cs'
    exists d',
      BUFCACHE.rep cs' d' *
      (rep d1_old d2_old d' hm' \/
       rep d1 d2 d' hm' \/
       rep default_valu default_valu d' hm')
  CRASH:hm'
    exists cs' d',
      (BUFCACHE.rep cs' d' *
       [[ (crep d1_old d2_old default_valu default_valu hm')%pred d' ]]) \/
      (BUFCACHE.rep cs' d' *
       [[ (crep d1 d2 default_valu default_valu hm')%pred d' ]])
  >} recover cs.