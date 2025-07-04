Require Import Prog ProgMonad.
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
Require Import String.
Require Import ListPred.
Require Import SepAuto.
Require Import Idempotent.
Require Import Inode.
Require Import List ListUtils.
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
Require Import DiskLogHash.
Require Import SuperBlock.
Require Import DiskSet.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import VBConv.
Require Import AsyncFS.
Require Import AByteFile.
Require Import TreeCrash.
Require Import TreeSeq.
Require Import DirSep.
Require Import Rounding.
Require Import BACHelper.
Require Import DirTreeDef.
Require Import DirTreeNames.
Require Import AtomicCp.
Require Import BytefileSpecs.

Import DIRTREE.
Import TREESEQ.
Import ATOMICCP.
Import ListNotations.

Set Implicit Arguments.

Notation tree_rep := ATOMICCP.tree_rep.

Hint Resolve valubytes_ne_O.
Hint Resolve valubytes_ge_O.
  

(* ---------------------------------------------------- *)
 (** Specs and proofs **)

  Opaque LOG.idempred.
  Opaque crash_xform.
  
    Lemma treeseq_tree_rep_sync_after_create: forall x0 (F: pred) dummy1 dummy5 srcinum dummy6 dummy4 dstbase
           dstname dummy9 temp_fn x a6 dummy3 a4 a5_1 a5_2,
  treeseq_pred
        (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4 dstbase
           dstname dummy9) dummy3 ->
  TStree dummy3 !! = TreeDir the_dnum x ->
  (F ✶ [temp_fn]%list |-> Nothing)%pred (dir2flatmem2 (TStree dummy3 !!)) ->
  (((((dstbase ++ [dstname])%list |-> File x0 dummy9
          ✶ dummy5 |-> File srcinum dummy6) ✶ [] |-> Dir the_dnum) ✶ dummy1)
       ✶ [temp_fn]%list |-> File a6 dirfile0)%pred
        (dir2flatmem2
           (tree_graft the_dnum x [] temp_fn (TreeFile a6 dirfile0)
              (TStree dummy3 !!))) ->
  treeseq_pred
  (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 a6 dstbase dstname
     dummy9)
  ({|
   TStree := tree_graft the_dnum x [] temp_fn (TreeFile a6 dirfile0)
               (TStree dummy3 !!);
   TSilist := a4;
   TSfree := (a5_1, a5_2) |}, []).
  
   
Definition atomic_cp fsxp src_inum dstbase dstname mscs :=
    let^ (mscs, r) <- AFS.create fsxp the_dnum temp_fn mscs;
    match r with
      | Err e => Ret ^(mscs, Err e)
      | OK tinum =>
        let^ (mscs) <- AFS.tree_sync fsxp mscs;   (* sync blocks *)
        let^ (mscs, ok) <- BytefileSpecs.copy_and_rename fsxp src_inum tinum dstbase dstname mscs;
        Ret ^(mscs, ok)
    end.

Theorem atomic_cp_ok : forall fsxp srcinum (dstbase: list string) (dstname:string) mscs,
    {< Fm Ftop Ftree ds ts sm tinum srcpath file fy copy_data dstfile,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe [temp_fn] (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_src Ftree srcpath [temp_fn] srcinum file dstbase dstname dstfile
          %pred (dir2flatmem2 (TStree ts!!)) ]] *
      [[ rep file fy ]] *
      [[[ (ByFData fy) ::: (arrayN (ptsto (V:= byteset)) 0 copy_data) ]]] *
      [[ length copy_data > 0 ]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts' sm',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       
      ([[ isError r ]] *
        
        (([[ treeseq_in_ds Fm Ftop fsxp sm' mscs ts' ds' ]] * 
        [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum
           file tinum dstbase dstname dstfile) ts' ]] * 
         [[ tree_with_src Ftree srcpath [temp_fn] srcinum
           file dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]]) \/
          (exists tinum tfile dfile, [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
          [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum
               file tinum dstbase dstname dfile) ts' ]] * 
           [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum
                       file tinum tfile dstbase dstname dfile (dir2flatmem2 (TStree ts'!!))]]))
       \/
       ([[ r = OK tt ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] * 
          exists dfile dfy tinum,
            [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dfile) ts' ]] *
            [[ tree_with_src Ftree srcpath [temp_fn] srcinum
               file dstbase dstname dfile %pred (dir2flatmem2 (TStree ts'!!)) ]] *
            [[ rep dfile dfy ]] *
            [[[ (ByFData dfy) ::: (arrayN (ptsto (V:= byteset)) 0 (synced_bdata copy_data)) ]]]))
    XCRASH:hm'
       exists mscs' ds' ts' sm' tinum dstfile,
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       ((exists t, [[ ts' = (t, nil) ]] * 
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts']] )
       \/ (exists t ts'' dfile tinum', [[ ts' = pushd t ts'' ]] * 
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dfile t ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum' dstbase dstname dstfile) ts'' ]] ))
    >} atomic_cp fsxp srcinum dstbase dstname mscs.

  
  
  