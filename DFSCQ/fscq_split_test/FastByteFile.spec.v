Require Import Mem.
Require Import Prog.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import BasicProg.
Require Import Bool.
Require Import Pred.
Require Import Hoare.
Require Import GenSepN.
Require Import SepAuto.
Require Import Idempotent.
Require Import Inode.
Require Import List.
Require Import Balloc.
Require Import Arith.
Require Import Array.
Require Import FSLayout.
Require Import Cache.
Require Import Rec.
Require Import FileRecArray RecArrayUtils LogRecArray.
Require Import Omega.
Require Import Eqdep_dec.
Require Import Bytes.
Require Import ProofIrrelevance.
Require Import Rounding.



Set Implicit Arguments.
Import ListNotations.

(** A byte-based interface to a BFileRec. Fast because it uses the range
update operation in BFileRec to do writes, and exposes an API that uses
[byte count]s rather than [list byte]s as inputs. *)
Module FASTBYTEFILE.

  Definition byte_type := Rec.WordF 8.
  Definition itemsz := Rec.len byte_type.
  Definition items_per_valu : addr := $ valubytes.
  Theorem itemsz_ok : valulen = wordToNat items_per_valu * itemsz.

  (* The bytes of a file are mapped onto a list of blocks:   *)
  (*   [ block 0 ... block n]                                *)
  (*   <-- allbytes      -->                                 *)
  (*   <-- bytes     -->                                     *)

  Definition bytes_rep f (allbytes : list byte) :=
    BFileRec.array_item_file byte_type items_per_valu itemsz_ok f allbytes /\
    # (natToWord addrlen (length allbytes)) = length allbytes.

  Definition rep (bytes : list byte) (f : BFILE.bfile) :=
    exists allbytes,
    bytes_rep f allbytes /\
    firstn (# (f.(BFILE.BFAttr).(INODE.ISize))) allbytes = bytes /\
    length bytes = (# (f.(BFILE.BFAttr).(INODE.ISize))) /\
    divup # (INODE.ISize (BFILE.BFAttr f)) valubytes * valubytes = length allbytes.

  Lemma block_items_ok : block_items items_per_valu = valubytes.

  (* roundup_ge specialized to valubytes *)
  Lemma roundup_valu_ge : forall n, n <= roundup n valubytes.

  Definition hidden (P : Prop) : Prop := P.
  Opaque hidden.

  Definition update_bytes T fsxp inum (off : nat) len (newbytes : bytes len) mscs rx : prog T :=
  If (lt_dec 0 len) {
    let^ (mscs) <- BFileRec.bf_update_range items_per_valu itemsz_ok
      fsxp inum off newbytes mscs;
    rx ^(mscs)
  } else {
    rx ^(mscs)
  }.

  Inductive byte_buf : Set :=
  | len_bytes : forall (len:nat), bytes len -> byte_buf.

  Definition buf_len (buf:byte_buf) : nat :=
  match buf with
  | @len_bytes len _ => len
  end.

  Definition buf_data (buf:byte_buf) : bytes (buf_len buf) :=
  match buf with
  | @len_bytes _ b => b
  end.

  Definition read_bytes T fsxp inum (off:nat) len mscs rx : prog T :=
  If (lt_dec 0 len) {
    let^ (mscs, attr) <- BFILE.bfgetattr (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    let flen := # (INODE.ISize attr) in
    If (lt_dec off flen) {
      If (lt_dec (off+len) flen) {
        let^ (mscs, data) <- BFileRec.bf_read_range items_per_valu itemsz_ok
          fsxp inum off len mscs;
        rx ^(mscs, len_bytes data)
      } else {
        let^ (mscs, data) <- BFileRec.bf_read_range items_per_valu itemsz_ok
          fsxp inum off (flen - off) mscs;
        rx ^(mscs, len_bytes data)
      }
   } else {
    (* reading starting at or past the end of the file *)
    rx ^(mscs, @len_bytes 0 (wzero _))
   }
  } else {
    (* reading zero bytes *)
    rx ^(mscs, @len_bytes 0 (wzero _))
  }.

  Implicit Arguments read_bytes [T].

  Lemma list2nmem_array_eq' : forall A (l l':list A),
    l = l' ->
    arrayN 0 l (list2nmem l').

  Lemma sep_star_abc_to_acb : forall AT AEQ AV (a b c : @pred AT AEQ AV),
    (a * b * c)%pred =p=> (a * c * b).

  Theorem read_bytes_ok: forall fsxp inum off len mscs,
  {< m mbase F Fm A flist f bytes,
  PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
      [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
      [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
      [[ rep bytes f ]]
   POST RET:^(mscs, b)
      exists Fx v,
      LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
      [[ (Fx * arrayN off v)%pred (list2nmem bytes) ]] *
      [[ @Rec.of_word (Rec.ArrayF byte_type (buf_len b))
        (buf_data b) = v ]] *
      (* non-error guarantee *)
      [[ 0 < len -> off < # (INODE.ISize (BFILE.BFAttr f)) ->
         0 < buf_len b ]]
   CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
   >} read_bytes fsxp inum off len mscs.

  Hint Extern 1 ({{_}} progseq (read_bytes _ _ _ _ _) _) => apply read_bytes_ok : prog.

  Theorem update_bytes_ok: forall fsxp inum off len (newbytes : bytes len) mscs,
      {< m mbase F Fm A flist f bytes olddata Fx,
       PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes f ]] *
           [[ (Fx * arrayN off olddata)%pred (list2nmem bytes) ]] *
           [[ length olddata = len ]]
      POST RET: ^(mscs)
           exists m' flist' f' bytes',
           LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ rep bytes' f' ]] *
           [[ let newdata := @Rec.of_word (Rec.ArrayF byte_type len) newbytes in
              (Fx * arrayN off newdata)%pred (list2nmem bytes') ]] *
           [[ hidden (BFILE.BFAttr f = BFILE.BFAttr f') ]]
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
      >} update_bytes fsxp inum off newbytes mscs.

  Hint Extern 1 ({{_}} progseq (update_bytes ?fsxp ?inum ?off ?newbytes _) _) =>
    apply update_bytes_ok with (fsxp:=fsxp) (inum:=inum) (off:=off) (newbytes:=newbytes) : prog.

   Definition grow_file T fsxp inum newlen mscs rx : prog T :=
    let^ (mscs, oldattr) <- BFILE.bfgetattr fsxp.(FSXPLog) fsxp.(FSXPInode) inum mscs;
    let oldlen := oldattr.(INODE.ISize) in
    If (wlt_dec oldlen ($ newlen)) {
      let^ (mscs, ok) <- bf_expand items_per_valu fsxp inum newlen mscs;
      If (bool_dec ok true) {
        let zeros := @natToWord ((roundup newlen valubytes-#oldlen)*8) 0 in
        let^ (mscs) <- bf_update_range items_per_valu itemsz_ok
           fsxp inum #oldlen zeros mscs;
         mscs <- BFILE.bfsetattr fsxp.(FSXPLog) fsxp.(FSXPInode) inum
                                (INODE.Build_iattr ($ newlen)
                                                   (INODE.IMTime oldattr)
                                                   (INODE.IType oldattr)) mscs;
        rx ^(mscs, true)
      } else {
        rx ^(mscs, false)
      }
    } else {
      rx ^(mscs, true)
    }.

  Definition filelen f := # (INODE.ISize (BFILE.BFAttr f)).

  Theorem grow_file_ok: forall fsxp inum newlen mscs,
    {< m mbase F Fm A flist f bytes,
      PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes f ]] *
           [[ goodSize addrlen newlen ]] *
           (* spec requires that file is growing, so that it can guarantee
              that the new size of the file is $newlen. *)
           [[ filelen f <= newlen ]]
      POST RET:^(mscs, ok)
           exists m', LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
           ([[ ok = false ]] \/
           [[ ok = true ]] * exists flist' f' bytes' fdata' attr,
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ bytes' = (bytes ++ (repeat $0 (newlen -  (# (INODE.ISize (BFILE.BFAttr f)))))) ]] *
           [[ rep bytes' f']] *
           [[ attr = INODE.Build_iattr ($ newlen) (f.(BFILE.BFAttr).(INODE.IMTime)) (f.(BFILE.BFAttr).(INODE.IType))]] *
           [[ f' = BFILE.Build_bfile fdata' attr]])
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
     >} grow_file fsxp inum newlen mscs.

  Hint Extern 1 ({{_}} progseq (grow_file _ _ _ _) _) => apply grow_file_ok : prog.

  (** Write bytes follows POSIX, which is overloaded to do two things:
  (1) if the write falls within the bounds of the file, update those bytes
  (2) otherwise, grow the file and update the new file (any grown bytes not
  updated are zeroed).

  We provide APIs for the two cases with separate specs: [update_bytes]
  and [overwrite_append]. *)
  Definition write_bytes T fsxp inum (off : nat) len (data : bytes len) mscs rx : prog T :=
    let newlen := off + len in
    let^ (mscs, oldattr) <- BFILE.bfgetattr fsxp.(FSXPLog) fsxp.(FSXPInode)
      inum mscs;
    let curlen := oldattr.(INODE.ISize) in
    (* should we grow the file? *)
    mscs <- IfRx irx (wlt_dec curlen ($ newlen)) {
      let^ (mscs, ok) <- grow_file fsxp inum newlen mscs;
      If (bool_dec ok true) {
        irx mscs
      } else {
        rx ^(mscs, false)
      }
    } else {
      irx mscs
    };
    let^ (mscs) <- update_bytes fsxp inum off data mscs;
    rx ^(mscs, true).

  (** Case (2) of [write_bytes] above, where the file must be grown.

  This is an alias for [write_bytes] since [write_bytes] already handles
  all the cases, but has its own idiosyncratic spec. *)
  Definition append T fsxp inum (off:nat) len (data : bytes len) mscs rx : prog T :=
    write_bytes fsxp inum off data mscs rx.

  Theorem append_ok: forall fsxp inum (off:nat) len (newbytes: bytes len) mscs,
    {< m mbase F Fm Fi A flist f bytes,
      PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes f ]] *
           [[ Fi (list2nmem bytes) ]] *
           [[ goodSize addrlen (off + len) ]] *
           (* makes this an append *)
           [[ filelen f <= off ]]
       POST RET:^(mscs, ok)
           exists m', LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
           ([[ ok = false ]] \/
           [[ ok = true ]] * exists flist' f' bytes' zeros,
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ rep bytes' f' ]] *
           [[ let newdata := @Rec.of_word (Rec.ArrayF byte_type len) newbytes in
              (Fi * zeros * arrayN off newdata)%pred (list2nmem bytes')]] *
           [[ zeros = arrayN (filelen f) (repeat $0 (off - (filelen f))) ]])
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
      >} append fsxp inum off newbytes mscs.

  Hint Extern 1 ({{_}} progseq (append _ _ _ _ _) _) => apply append_ok : prog.

End FASTBYTEFILE.