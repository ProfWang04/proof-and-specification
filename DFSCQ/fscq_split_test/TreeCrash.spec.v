Require Import DirName.
Require Import Balloc.
Require Import Prog.
Require Import BasicProg.
Require Import Bool.
Require Import Word.
Require Import BFile Bytes Rec Inode.
Require Import String.
Require Import FSLayout.
Require Import Pred PredCrash.
Require Import Arith.
Require Import GenSepN.
Require Import List ListUtils.
Require Import Hoare.
Require Import Log.
Require Import SepAuto.
Require Import Array.
Require Import FunctionalExtensionality.
Require Import AsyncDisk.
Require Import DiskSet.
Require Import SyncedMem.
Require Import GenSepAuto.
Require Import BFileCrash.
Require Import Omega.
Require Import DirTreeDef.
Require Import DirTreeRep.
Require Import DirTreePred.
Require Import DirTreeNames.
Require Import DirTreeInodes.

Import ListNotations.

Module SDIR := DirCache.CacheOneDir.

Set Implicit Arguments.

Module DTCrash.

  Definition file_crash (f f' : dirfile) : Prop :=
    exists c c',
    BFILE.file_crash (BFILE.mk_bfile (DFData f) (DFAttr f) c)
                     (BFILE.mk_bfile (DFData f') (DFAttr f') c').

  Inductive tree_crash : dirtree -> dirtree -> Prop :=
    | TCFile : forall inum f f',
               file_crash f f' ->
               tree_crash (TreeFile inum f) (TreeFile inum f')
    | TCDir  : forall inum st st',
               map fst st = map fst st' ->
               Forall2 tree_crash (map snd st) (map snd st') ->
               tree_crash (TreeDir inum st) (TreeDir inum st').

  Theorem tree_crash_trans : forall t1 t2 t3,
    tree_crash t1 t2 ->
    tree_crash t2 t3 ->
    tree_crash t1 t3.

  Lemma flist_crash_xform_dirlist_pred : forall tree_ents p,
    Forall
      (fun t => flist_crash_xform (p t) =p=> exists t', [[ tree_crash t t' ]] * p t')
      (map snd tree_ents) ->
    flist_crash_xform (dirlist_pred p tree_ents) =p=>
      exists tree_ents',
      [[ Forall2 tree_crash (map snd tree_ents) (map snd tree_ents') ]] *
      [[ map fst tree_ents = map fst tree_ents' ]] *
      dirlist_pred p tree_ents'.

  Lemma tree_dir_names_pred'_unchanged : forall tree_ents tree_ents',
    map fst tree_ents = map fst tree_ents' ->
    map (fun e => dirtree_inum e) (map snd tree_ents) = map (fun e => dirtree_inum e) (map snd tree_ents') ->
    map (fun e => dirtree_isdir e) (map snd tree_ents) = map (fun e => dirtree_isdir e) (map snd tree_ents') ->
    tree_dir_names_pred' tree_ents =p=> tree_dir_names_pred' tree_ents'.

  Lemma flist_crash_xform_tree_dir_names_pred : forall tree_ents tree_ents' xp inum,
    map fst tree_ents = map fst tree_ents' ->
    map (fun e => dirtree_inum e) (map snd tree_ents) = map (fun e => dirtree_inum e) (map snd tree_ents') ->
    map (fun e => dirtree_isdir e) (map snd tree_ents) = map (fun e => dirtree_isdir e) (map snd tree_ents') ->
    flist_crash_xform (tree_dir_names_pred xp inum tree_ents) =p=>
      tree_dir_names_pred xp inum tree_ents'.

  Lemma tree_crash_preserves_dirtree_inum : forall t t',
    tree_crash t t' ->
    dirtree_inum t = dirtree_inum t'.

  Lemma tree_crash_preserves_dirtree_isdir : forall t t',
    tree_crash t t' ->
    dirtree_isdir t = dirtree_isdir t'.

  Lemma flist_crash_xform_tree_pred : forall xp t,
    flist_crash_xform (tree_pred xp t) =p=> exists t', [[ tree_crash t t' ]] * tree_pred xp t'.

  Lemma flist_crash_xform_freelist : forall (FP : BFILE.bfile -> Prop) xp frees freepred ms,
    (forall f f', BFILE.file_crash f f' -> FP f -> FP f') ->
    IAlloc.Alloc.rep FP xp frees freepred ms =p=>
      IAlloc.Alloc.rep FP xp frees freepred ms *
      [[ flist_crash_xform freepred =p=> freepred ]].

  Lemma xform_tree_rep : forall xp F t ilist frees ms msll' sm,
     crash_xform (rep xp F t ilist frees ms sm) =p=>
     exists t',
      [[ tree_crash t t' ]] * 
      rep xp (flist_crash_xform F) t' ilist frees (BFILE.ms_empty msll') sm_synced.

  Theorem tree_crash_find_name :
    forall fnlist t t' subtree,
    tree_crash t t' ->
    find_subtree fnlist t = Some subtree ->
    exists subtree',
    find_subtree fnlist t' = Some subtree' /\
    tree_crash subtree subtree'.

  Theorem tree_crash_find_none :
    forall fnlist t t',
    tree_crash t t' ->
    find_subtree fnlist t = None ->
    find_subtree fnlist t' = None.

  Lemma tree_crash_find_subtree_root: forall t t' inum,
    tree_crash t t' ->
    (exists elem, find_subtree [] t = Some (TreeDir inum elem)) ->
    (exists elem', find_subtree [] t' = Some (TreeDir inum elem')).

  Lemma tree_crash_find_name_root: forall t t' inum,
    tree_crash t t' ->
    find_name [] t = Some (inum, true) ->
    find_name [] t' = Some (inum, true).

  Theorem file_crash_exists : forall file, exists file',
    BFILE.file_crash file file'.

  Theorem tree_crash_exists : forall tree, exists tree',
    tree_crash tree tree'.

  Theorem tree_crash_update_subtree' :
    forall pn tree subtree tree' subtree',
    tree_crash tree tree' ->
    tree_crash subtree subtree' ->
    tree_crash (update_subtree pn subtree tree) (update_subtree pn subtree' tree').

  Theorem tree_crash_tree_names_distinct : forall t t',
    tree_crash t t' ->
    tree_names_distinct t ->
    tree_names_distinct t'.

  Theorem tree_crash_tree_inodes_permutation : forall t t',
    tree_crash t t' ->
    permutation addr_eq_dec (tree_inodes t) (tree_inodes t').

  Theorem tree_crash_tree_inodes_distinct : forall t t',
    tree_crash t t' ->
    tree_inodes_distinct t ->
    tree_inodes_distinct t'.

  Theorem tree_crash_update_subtree :
    forall pn tree subtree updated_tree_crashed,
    tree_names_distinct tree ->
    tree_crash (update_subtree pn subtree tree) updated_tree_crashed ->
    exists tree_crashed subtree_crashed,
    tree_crash tree tree_crashed /\
    tree_crash subtree subtree_crashed /\
    updated_tree_crashed = update_subtree pn subtree_crashed tree_crashed.

  Lemma file_crash_data_length : forall f f',
    file_crash f f' -> length (DFData f) = length (DFData f').

  Lemma file_crash_synced : forall f f',
    file_crash (synced_dirfile f) f' ->
    f' = synced_dirfile f.

  Lemma dirfile_crash_exists : forall f, exists f',
    file_crash f f'.

End DTCrash.