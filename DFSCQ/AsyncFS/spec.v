Require Import Coq.Strings.String.
Require Import Prog ProgMonad.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Omega.
Require Import BasicProg.
Require Import Bool.
Require Import Pred PredCrash.
Require Import DirCache.
Require Import Hoare.
Require Import GenSepN.
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
Require Import SyncedMem.
Require Import GroupLog.
Require Import DiskLogHash.
Require Import SuperBlock.
Require Import DiskSet.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import DirTreeDef.
Require Import DirTreeRep.
Require Import DirTreePred.
Require Import DirTreeInodes.
Require Import DirTreeSafe.

Set Implicit Arguments.
Import DirTree.
Import ListNotations.

Module AFS.

  (* Programs *)

  Definition compute_xparams (data_bitmaps inode_bitmaps log_descr_blocks : addr) :=
    (**
     * Block 0 stores the superblock (layout information).
     * The other block numbers, except for Log, are relative to
     * the Log data area, which starts at $1.
     * To account for this, we bump [log_base] by $1, to ensure that
     * the data area does not run into the logging structures.
     *)

    (**
     * File system layout:
     * +--------+--------+--------+-------+-------+-------+--------+-------+------+
     * | Super- |  Data  | Inode  | Inode | Data1 | Data2 |  Log   | Log   | Log  |
     * | block  | blocks | blocks | alloc | alloc | alloc | header | descr | data |
     * +--------+--------+--------+-------+-------+-------+--------+-------+------+
     **)

    (* XXX: not quite right, fix later *)
    let data_blocks := data_bitmaps * valulen in
    let inode_blocks := inode_bitmaps * valulen / INODE.IRecSig.items_per_val in
    let inode_base := data_blocks in
    let balloc_base1 := inode_base + inode_blocks + inode_bitmaps in
    let balloc_base2 := balloc_base1 + data_bitmaps in
    let log_hdr := 1 + balloc_base2 + data_bitmaps in
    let log_descr := log_hdr + 1 in
    let log_data := log_descr + log_descr_blocks in
    let log_data_size := log_descr_blocks * PaddedLog.DescSig.items_per_val in
    let max_addr := log_data + log_data_size in
    (Build_fs_xparams
     (Build_log_xparams 1 log_hdr log_descr log_descr_blocks log_data log_data_size)
     (Build_inode_xparams inode_base inode_blocks)
     (Build_balloc_xparams balloc_base1 data_bitmaps)
     (Build_balloc_xparams balloc_base2 data_bitmaps)
     (Build_balloc_xparams (inode_base + inode_blocks) inode_bitmaps)
     1
     max_addr).

Notation MSLL := BFILE.MSLL.
  Notation MSAllocC := BFILE.MSAllocC.
  Notation MSIAllocC := BFILE.MSIAllocC.
  Notation MSICache := BFILE.MSICache.
  Notation MSAlloc := BFILE.MSAlloc.
  Notation MSDBlocks := BFILE.MSDBlocks.

  Import DIRTREE.

  Definition mkfs cachesize data_bitmaps inode_bitmaps log_descr_blocks :=
    let fsxp := compute_xparams data_bitmaps inode_bitmaps log_descr_blocks SB.magic_number in
    cs <- BUFCACHE.init_load cachesize;
    cs <- SB.init fsxp cs;
    mscs <- LOG.init (FSXPLog fsxp) cs;
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    ms <- BFILE.init (FSXPLog fsxp) (FSXPBlockAlloc1 fsxp, FSXPBlockAlloc2 fsxp) fsxp (FSXPInode fsxp) mscs;
    let^ (ialloc_ms, r) <- IAlloc.alloc (FSXPLog fsxp) fsxp (BFILE.MSIAlloc ms);
    let mscs := IAlloc.MSLog ialloc_ms in
    match r with
    | None =>
      mscs <- LOG.abort (FSXPLog fsxp) mscs;
      Ret (Err ENOSPCINODE)
    | Some inum =>
      (**
       * We should write a new fsxp back to the superblock with the new root
       * inode number.
       * In practice, the root inode is always the same, so it doesn't matter.
       *)
      If (eq_nat_dec inum (FSXPRootInum fsxp)) {
        let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
        If (bool_dec ok true) {
          mscs <- LOG.flushsync (FSXPLog fsxp) mscs;
          Ret (OK ((BFILE.mk_memstate (MSAlloc ms) mscs (MSAllocC ms) (IAlloc.MSCache ialloc_ms) (MSICache ms) (MSCache ms) (MSDBlocks ms)), fsxp))
        } else {
          Ret (Err ELOGOVERFLOW)
        }
      } else {
        mscs <- LOG.abort (FSXPLog fsxp) mscs;
        Ret (Err ELOGOVERFLOW)
      }
    end.

Definition recover cachesize :=
    cs <- BUFCACHE.init_recover cachesize;
    let^ (cs, fsxp) <- SB.load cs;
    If (addr_eq_dec (FSXPMagic fsxp) SB.magic_number) {
      mscs <- LOG.recover (FSXPLog fsxp) cs;
      mscs <- BFILE.recover mscs;
      Ret (OK (mscs, fsxp))
    } else {
      Ret (Err EINVAL)
    }.

  Definition file_get_attr fsxp inum ams :=
    t1 <- Rdtsc ;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, attr) <- DIRTREE.getattr fsxp inum (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
    r <- Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), attr);
    t2 <- Rdtsc ;
    Debug "get_attr" (t2-t1) ;;
    Ret r.

  Definition file_get_sz fsxp inum ams :=
    t1 <- Rdtsc ;
    let^ (ams, attr) <- file_get_attr fsxp inum ams;
    t2 <- Rdtsc ;
    Debug "file_get_sz" (t2-t1) ;;
    Ret ^(ams, INODE.ABytes attr).

  Definition file_set_attr fsxp inum attr ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    ams' <- DIRTREE.setattr fsxp inum attr (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    let^ (ms', ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams');
    If (bool_dec ok true) {
      Ret ^((BFILE.mk_memstate (MSAlloc ams') ms' (MSAllocC ams') (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams')), OK tt)
    } else {
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms' (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
    }.

  (* note that file_set_sz is not the same as ftruncate - it does not allocate
  new blocks, but merely sets the size in the inode to the specified sz (in
  bytes) *)
  Definition file_set_sz fsxp inum sz ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    ams <- DIRTREE.updattr fsxp inum (INODE.UBytes sz) (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);
    If (bool_dec ok true) {
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), OK tt)
    } else {
      Ret ^(ams, Err ELOGOVERFLOW)
    }.

  Definition read_fblock fsxp inum off ams :=
    t1 <- Rdtsc ;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, b) <- DIRTREE.read fsxp inum off (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
    r <- Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), b);
    t2 <- Rdtsc ;
    Debug "read_fblock" (t2-t1) ;;
    Ret r.

  (* note that file_truncate takes sz in blocks *)
  Definition file_truncate fsxp inum sz ams :=
    t1 <- Rdtsc ;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams', ok) <- DIRTREE.truncate fsxp inum sz (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    r <- match ok with
    | Err e =>
        ms <- LOG.abort (FSXPLog fsxp) (MSLL ams');
        Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
    | OK _ =>
      let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams');
      If (bool_dec ok true) {
        Ret ^((BFILE.mk_memstate (MSAlloc ams') ms (MSAllocC ams') (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams')), OK tt)
      } else {
        Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
      }
    end;
    t2 <- Rdtsc ;
    Debug "truncate" (t2-t1) ;;
    Ret r.

  (* ftruncate is an _unverified_ implementation of the ftruncate system call
  (it is similar to the verified file_truncate code, but has some adjustments to
  work in terms of bytes) *)
  (* TODO: this code is not verified, although its core (DIRTREE.truncate and
  DIRTREE.updattr) are, as well as [file_truncate]. *)
  Definition ftruncate fsxp inum sz ams :=
    t1 <- Rdtsc ;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let sz_blocks := (sz + valulen - 1) / valulen in
    let^ (ams', ok) <- DIRTREE.truncate fsxp inum sz_blocks (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    r <- match ok with
    | Err e =>
        ms <- LOG.abort (FSXPLog fsxp) (MSLL ams');
        Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
    | OK _ =>
      ams' <- DIRTREE.updattr fsxp inum (INODE.UBytes (addr2w sz)) (BFILE.mk_memstate (MSAlloc ams') ms (MSAllocC ams') (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams'));
      let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams');
      If (bool_dec ok true) {
        Ret ^((BFILE.mk_memstate (MSAlloc ams') ms (MSAllocC ams') (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams')), OK tt)
      } else {
        Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)),
              Err ELOGOVERFLOW)
      }
    end;
    t2 <- Rdtsc ;
    Debug "ftruncate" (t2-t1) ;;
    Ret r.

  (* update an existing block of an *existing* file with bypassing the log *)
  Definition update_fblock_d fsxp inum off v ams :=
    t1 <- Rdtsc ;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    ams <- DIRTREE.dwrite fsxp inum off v (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
    r <- Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)));
    t2 <- Rdtsc ;
    Debug "update_fblock_d" (t2-t1) ;;
    Ret r.

  Definition update_fblock fsxp inum off v ams :=
    t1 <- Rdtsc ;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    ams <- DIRTREE.write fsxp inum off v (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);
    r <- Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), ok);
    t2 <- Rdtsc ;
    Debug "update_fblock" (t2-t1) ;;
    Ret r.

  (* sync only data blocks of a file. *)
  Definition file_sync fsxp inum ams :=
    t1 <- Rdtsc ;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    ams <- DIRTREE.datasync fsxp inum (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
    r <- Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)));
    t2 <- Rdtsc ;
    Debug "file_sync" (t2-t1) ;;
    Ret r.

  Definition readdir fsxp dnum ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, files) <- SDIR.readdir (FSXPLog fsxp) (FSXPInode fsxp) dnum (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
    Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), files).

  Definition create fsxp dnum name ams :=
    t1 <- Rdtsc ;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams', oi) <- DIRTREE.mkfile fsxp dnum name (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    r <- match oi with
      | Err e =>
          ms <- LOG.abort (FSXPLog fsxp) (MSLL ams');
          Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
      | OK inum =>
        let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams');
        match ok with
          | true => Ret ^((BFILE.mk_memstate (MSAlloc ams') ms (MSAllocC ams') (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams')), OK inum)
          | false => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
        end
     end;
     t2 <- Rdtsc ;
     Debug "create" (t2-t1) ;;
     Ret r.

  Definition mksock fsxp dnum name ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, oi) <- DIRTREE.mkfile fsxp dnum name (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    match oi with
      | Err e =>
        ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);
        Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
      | OK inum =>
        ams <- BFILE.updattr (FSXPLog fsxp) (FSXPInode fsxp) inum (INODE.UType $1) ams;
        let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);
        match ok with
          | true => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), OK inum)
          | false => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
        end
    end.

  Definition mkdir fsxp dnum name ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, oi) <- DIRTREE.mkdir fsxp dnum name (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    match oi with
      | Err e =>
        ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);
          Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
      | OK inum =>
        let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);
        match ok with
          | true => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), OK inum)
          | false => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
        end
    end.

  Definition delete fsxp dnum name ams :=
    t1 <- Rdtsc;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams', ok) <- DIRTREE.delete fsxp dnum name (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    res <- match ok with
    | OK _ =>
       let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams');
       match ok with
       | true => Ret ^((BFILE.mk_memstate (MSAlloc ams') ms (MSAllocC ams') (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams')), OK tt)
       | false => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
       end
    | Err e =>
      ms <- LOG.abort (FSXPLog fsxp) (MSLL ams');
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
    end;
    t2 <- Rdtsc;
    Debug "delete" (t2-t1);;
    Ret res.

  Definition lookup fsxp dnum names ams :=
    t1 <- Rdtsc ;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, r) <- DIRTREE.namei fsxp dnum names (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
    r <- Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), r);
    t2 <- Rdtsc ;
    Debug "lookup" (t2-t1) ;;
    Ret r.

  Definition rename fsxp dnum srcpath srcname dstpath dstname ams :=
    t1 <- Rdtsc;
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams', r) <- DIRTREE.rename fsxp dnum srcpath srcname dstpath dstname (BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams));
    res <- match r with
    | OK _ =>
      let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams');
      match ok with
      | true => Ret ^((BFILE.mk_memstate (MSAlloc ams') ms (MSAllocC ams') (MSIAllocC ams') (MSICache ams') (MSCache ams') (MSDBlocks ams')), OK tt)
      | false => Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err ELOGOVERFLOW)
      end
    | Err e =>
      ms <- LOG.abort (FSXPLog fsxp) (MSLL ams');
      Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), Err e)
    end;
    t2 <- Rdtsc;
    Debug "rename" (t2-t1);;
    Ret res.

  (* sync directory tree; will flush all outstanding changes to tree (but not dupdates to files) *)
  Definition tree_sync fsxp ams :=
    t1 <- Rdtsc ;
    ams <- DIRTREE.sync fsxp ams;
    t2 <- Rdtsc ;
    Debug "tree_sync" (t2-t1) ;;
    Ret ^(ams).

  Definition tree_sync_noop fsxp ams :=
    ams <- DIRTREE.sync_noop fsxp ams;
    Ret ^(ams).

  Definition umount fsxp ams :=
    ams <- DIRTREE.sync fsxp ams;
    ms <- LOG.sync_cache (FSXPLog fsxp) (MSLL ams);
    Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams))).

  Definition statfs fsxp ams :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    (*
    let^ (mscs, free_blocks) <- BALLOC.numfree (FSXPLog fsxp) (FSXPBlockAlloc fsxp) mscs;
    let^ (mscs, free_inodes) <- BALLOC.numfree (FSXPLog fsxp) (FSXPInodeAlloc fsxp) mscs;
     *)
    ms <- LOG.commit_ro (FSXPLog fsxp) ms;
    (* Ret ^(mscs, free_blocks, free_inodes).  *)
    Ret ^((BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) (MSIAllocC ams) (MSICache ams) (MSCache ams) (MSDBlocks ams)), 0, 0).

  (* Recover theorems *)

  Hint Extern 0 (okToUnify (LOG.rep_inner _ _ _ _) (LOG.rep_inner _ _ _ _)) => constructor : okToUnify.
 Definition rename_rep_inner d frees' ilist' tree' srcnum srcents subtree pruned dstnum dstents renamed mscs' sm Fm fsxp Ftop tree tree_elem ilist frees cwd dnum srcpath srcname dstpath dstname
    : @pred addr addr_eq_dec valuset :=
    ([[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
    [[ find_subtree srcpath (TreeDir dnum tree_elem) = Some (TreeDir srcnum srcents) ]] *
    [[ find_dirlist srcname srcents = Some subtree ]] *
    [[ pruned = tree_prune srcnum srcents srcpath srcname (TreeDir dnum tree_elem) ]] *
    [[ find_subtree dstpath pruned = Some (TreeDir dstnum dstents) ]] *
    [[ renamed = tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
    [[ tree' = update_subtree cwd renamed tree ]] *
    [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                    ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
    [[ forall inum' def', inum' <> srcnum -> inum' <> dstnum ->
       In inum' (tree_inodes tree') ->
       selN ilist inum' def' = selN ilist' inum' def' ]])%pred.

  Definition rename_rep ds mscs' sm Fm fsxp Ftop tree tree_elem ilist frees cwd dnum srcpath srcname dstpath dstname hm :=
    (exists d tree' srcnum srcents dstnum dstents subtree pruned renamed ilist' frees',
    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') sm hm *
    rename_rep_inner d frees' ilist' tree' srcnum srcents subtree pruned dstnum dstents renamed mscs' sm Fm fsxp Ftop tree tree_elem ilist frees cwd dnum srcpath srcname dstpath dstname
    )%pred.

  
