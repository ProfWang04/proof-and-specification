Require Import Prog.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Omega.
Require Import BasicProg.
Require Import Bool.
Require Import Pred PredCrash.
Require Import DirName.
Require Import Hoare.
Require Import GenSepN.
Require Import ListPred.
Require Import SepAuto.
Require Import Idempotent.
Require Import Inode.
Require Import List.
Require Import Balloc.
Require Import Bytes.
Require Import DirTree.
Require Import Rec.
Require Import Arith.
Require Import Array.
Require Import FSLayout.
Require Import Cache.
Require Import Errno.
Require Import AsyncDisk.
Require Import GroupLog.
Require Import SuperBlock.
Require Import DiskSet.

Set Implicit Arguments.
Import ListNotations.

Hint Extern 0 (okToUnify (LOG.rep_inner _ _ _) (LOG.rep_inner _ _ _)) => constructor : okToUnify.


Definition recover {T} rx : prog T :=
  cs <- BUFCACHE.init_recover 10;
  let^ (cs, fsxp) <- SB.load cs;
  mscs <- LOG.recover (FSXPLog fsxp) cs;
  rx ^(mscs, fsxp).


Theorem recover_ok :
  {< fsxp cs ds,
   PRE
     LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs
   POST RET:^(ms, fsxp')
     [[ fsxp' = fsxp ]] * exists d n, [[ n <= length (snd ds) ]] *
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) ms *
     [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
   CRASH exists cs',
     LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs'
   >} recover.


Definition update_block_d T lxp a v ms rx : prog T :=
  ms <- LOG.begin lxp ms;
  ms <- LOG.dwrite lxp a v ms;
  ms <- LOG.commit_ro lxp ms;
  rx ms.

Theorem update_block_d_ok : forall fsxp a v ms,
  {< m F v0,
  PRE
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (m, nil)) ms *
      [[[ m ::: (F * a |-> v0) ]]]
  POST RET:ms
      exists m',
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (m', nil)) ms *
      [[[ m' ::: (F * a |-> (v, vsmerge v0)) ]]]
  CRASH
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (m, nil) \/
      exists m', [[[ m' ::: (F * a |-> (v, vsmerge v0)) ]]] *
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (m', nil)
  >} update_block_d (FSXPLog fsxp) a v ms.



Ltac recover_ro_ok := intros;
  repeat match goal with
    | [ |- forall_helper _ ] => idtac "forall"; unfold forall_helper; intros; eexists; intros
    | [ |- corr3 ?pre' _ _ ] => idtac "corr3 pre"; eapply corr3_from_corr2_rx; eauto with prog
    | [ |- corr3 _ _ _ ] => idtac "corr3"; eapply pimpl_ok3; intros
    | [ |- corr2 _ _ ] => idtac "corr2"; step
    | [ H: crash_xform ?x =p=> ?x |- context [ crash_xform ?x ] ] => rewrite H
    | [ H: diskIs _ _ |- _ ] => idtac "unfold"; unfold diskIs in *
    | [ |- pimpl (crash_xform _) _ ] => idtac "crash_xform"; progress autorewrite with crash_xform
  end.


Hint Extern 0 (okToUnify (LOG.idempred _ _ _) (LOG.idempred _ _ _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (LOG.after_crash _ _ _ _) (LOG.after_crash _ _ _ _)) => constructor : okToUnify.

Theorem update_block_d_recover_ok : forall fsxp a v ms,
  {<< m F v0,
  PRE
    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (m, nil)) ms *
    [[[ m ::: (F * a |-> v0) ]]]
  POST RET:ms  exists m',
    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (m', nil)) ms *
    [[[ m' ::: (F * a |-> (v, vsmerge v0)) ]]]
  REC RET:^(ms, fsxp) exists m',
    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (m', nil)) ms *
    [[[ m' ::: (exists v', crash_xform F * a |=> v' *
                [[ In v' (v :: (vsmerge v0)) ]]) ]]]
  >>} update_block_d (FSXPLog fsxp) a v ms >> recover.



Definition update_block_d2 T lxp a v ms rx : prog T :=
  ms <- LOG.begin lxp ms;
  ms <- LOG.dwrite lxp a v ms;
  let^ (ms, r) <- LOG.commit lxp ms;
  rx ^(ms, r).


Theorem update_block_d2_ok : forall fsxp a v ms,
  {< F ds v0,
  PRE
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) ms *
      [[[ ds!! ::: (F * a |-> v0) ]]]
  POST RET:^(ms, r)
      ([[ r = false ]] * exists m',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (m', nil)) ms)
  \/  ([[ r = true  ]] * exists ds',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') ms *
        [[[ ds'!! ::: (F * a |-> (v, vsmerge v0)) ]]])
  CRASH
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds \/
      exists m', [[[ m' ::: (F * a |-> (v, vsmerge v0)) ]]] *
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (m', nil)
  >} update_block_d2 (FSXPLog fsxp) a v ms.


Theorem update_block_d2_recover_ok : forall fsxp a v ms,
  {<< ds F v0,
  PRE
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) ms *
      [[[ ds!! ::: (F * a |-> v0) ]]]
  POST RET:^(ms, r)
      ([[ r = false ]] * exists m',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (m', nil)) ms)
  \/  ([[ r = true  ]] * exists ds',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') ms *
        [[[ ds'!! ::: (F * a |-> (v, vsmerge v0)) ]]])
  REC RET:^(ms, fsxp) exists m',
    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (m', nil)) ms *
    ((exists n, [[ n <= length (snd ds) ]] *
    [[[ m' ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]) \/
    [[[ m' ::: (exists v', crash_xform F * a |=> v' *
                [[ In v' (v :: (vsmerge v0)) ]]) ]]])
  >>} update_block_d2 (FSXPLog fsxp) a v ms >> recover.


