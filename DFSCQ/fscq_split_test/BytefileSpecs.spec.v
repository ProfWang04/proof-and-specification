Require Import String.
Require Import Hashmap.
Require Import Prog ProgMonad.
Require Import Log.
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
Require Import List ListUtils.
Require Import Balloc.
Require Import Bytes.
Require Import DirTree.
Require Import DirTreeDef.
Require Import DirTreeNames.
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
Require Import DirSep.
Require Import Rounding.
Require Import TreeSeq.
Require Import BACHelper.
Require Import AtomicCp.

Import DIRTREE.
Import DTCrash.
Import TREESEQ.
Import ATOMICCP.
Import ListNotations.

Set Implicit Arguments.


Notation tree_rep := ATOMICCP.tree_rep.
Notation rep := AByteFile.rep.

Hint Resolve valubytes_ne_O.
Hint Resolve valubytes_ge_O.

  Ltac proto_bytefile_rewrite:=
  match goal with
  | [H: proto_bytefile_valid _ ?pfy |- context[PByFData ?pfy] ] => rewrite H
  end.
    
  Ltac solve_rep:= unfold AByteFile.rep; repeat eexists; eauto.

	Ltac nlt_eq_0:=
  match goal with
   | [H: 0 < _ -> False |- _ ] => 
                apply Nat.nlt_ge in H; inversion H as [Hx | ]
   end.
   
   Ltac rewrite_0:= 
   match goal with
   | [H: _ = 0 |- _ ] => try rewrite H; simpl; try rewrite <- plus_n_O
   end.
   
   Ltac rewrite_nlt :=
   match goal with
   | [H: 0 < _ -> False |- _ ] => nlt_eq_0; rewrite_0
   end.
	
  Ltac xcrash_dwrite_to_block x0:= 
    match goal with | [H: (_, _) = _, H0: treeseq_in_ds _ _ _ _ (_, _) _ |- _ ] => 
          rewrite H in H0 end;
    match goal with | [H: MSAlloc ?a = _, H0: _ = MSAlloc ?a |- _ ] => 
          rewrite H in H0; clear H end;
    cancel;
    do 2 (rewrite crash_xform_exists_comm; cancel);
    rewrite crash_xform_exists_comm; unfold pimpl; intros;
    exists x0;
    pred_apply;
    repeat (rewrite crash_xform_sep_star_dist;
       rewrite crash_xform_lift_empty);
    safecancel;
    eauto.
    
  Ltac solve_ineq_dwrite_middle := 
    length_rewrite_l; auto;
    repeat match goal with | [H: ?a = _ |- context[?a] ] =>  rewrite H end;
    try apply Nat.le_add_le_sub_l;
    try rewrite <- Nat.mul_succ_l;
    try apply mult_le_compat_r;
    omega.
    
Ltac solve_dsupd_iter:=
    rewrite skipn_oob; [| solve_ineq_dwrite_middle];
    rewrite app_nil_r;
    eapply dsupd_iter_merge; eauto.

Ltac solve_tsupd_iter:=
    rewrite skipn_oob;  [| solve_ineq_dwrite_middle];
    rewrite app_nil_r;
    eapply tsupd_tsupd_iter_merge; eauto.

 Ltac solve_cancel_dwrite_middle block_off bnl :=
     rewrite <- plus_n_O;
     repeat rewrite Nat.mul_add_distr_r; simpl; 
     repeat rewrite Nat.add_assoc;
     rewrite skipn_skipn;
     replace (block_off * valubytes + valubytes + length bnl * valubytes)
      with  (block_off * valubytes + length bnl * valubytes + valubytes) by omega;
      cancel;
      rewrite sep_star_comm;
      unfold get_sublist;
      replace (valubytes + length bnl * valubytes)
        with(length bnl * valubytes + valubytes) by omega;
      rewrite arrayN_merge_bs_split_firstn; cancel.
   
  Lemma div_mod': forall x y,
    y <> 0 -> x / y * y + x mod y = x.
  
  Lemma mod_eq': forall a b,
    b <> 0 ->
    a - a / b * b = a mod b.
      
  Ltac solve_length_le_v:=
     length_rewrite_l;
     rewrite mod_eq'; auto;
    apply Nat.mod_upper_bound; auto.
  
  Ltac solve_length_le:=
    rewrite Nat.mul_comm; try match goal with | [H: length _ = length _ |- _ ] => rewrite H end; 
    apply Nat.mul_div_le; auto;
    solve_length_le_v.
  
    Ltac simpl_skipn_lt:=
      match goal with | [H: 0 < length (skipn _ _) |- _] =>
      rewrite skipn_length in H; rewrite Nat.mul_comm in H;
      rewrite <- Nat.mod_eq in H; auto end.

  Ltac unfold_rep:= 
    repeat match goal with | [H: rep _ _ |- _] => unfold AByteFile.rep in H end;
    split_hypothesis; auto.

  Ltac solve_min_dwrite_middle fy fy' data:=
    replace (length (ByFData fy')) with (length (ByFData fy));
    [ simpl_skipn_lt;
      match goal with | [H: min _ _ = _ |- _] => unfold hpad_length in H; simpl in * end;
      length_rewrite_l; repeat rewrite mod_eq'; auto;
      rewrite Nat.mul_add_distr_r; 
      rewrite <- Nat.add_assoc; rewrite div_mod'; auto;
      destruct (length data mod valubytes); omega | eapply bytefile_length_eq; eauto ].
      
        Ltac solve_cancel_dwrite_middle2:=
    pred_apply; repeat rewrite Nat.mul_add_distr_r;
    length_rewrite_l; rewrite <- Nat.add_assoc; rewrite <- le_plus_minus; eauto;
    [ cancel; rewrite sep_star_comm;
      rewrite <- arrayN_app';  
      [ rewrite <- merge_bs_app; repeat rewrite firstn_skipn; eauto | ];
   length_rewrite_l; solve_length_le | length_rewrite_l; solve_length_le ].
   
      Ltac solve_eq_dwrite_middle:= 
      length_rewrite_l; auto;
      try rewrite Nat.div_mul; auto; 
      try solve_length_le; auto.
      
   

  Lemma tree_with_src_the_dnum: forall Fm Ftop fsxp mscs Ftree srcpath tmppath srcinum file
      dstbase dstname dstfile ts ds sm,
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    tree_with_src Ftree srcpath tmppath srcinum file dstbase dstname dstfile%pred
          (dir2flatmem2 (TStree ts !!)) ->
    exists direlem, 
        find_subtree [] (TStree ts !!) = Some (TreeDir the_dnum direlem).
  
   
  Lemma crash_ts_split: forall dummy1 dummy5 temp_fn srcinum dummy6 dummy4 dstbase
           dstname dummy9 dummy3 dummy dummy0 fsxp mscs dummy2 sm,
  treeseq_pred
        (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4 dstbase
           dstname dummy9) dummy3 ->
  treeseq_in_ds dummy dummy0 fsxp sm mscs dummy3 dummy2 ->
  emp
⇨⇨ crash_xform
     (exists t : treeseq_one,
        (⟦⟦ dummy3 = (t, []) ⟧⟧
         ✶ ⟦⟦ treeseq_in_ds dummy dummy0 fsxp sm mscs dummy3 dummy2 ⟧⟧)
        ✶ ⟦⟦ treeseq_pred
               (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4 dstbase
                  dstname dummy9) dummy3 ⟧⟧)
   ⋁ crash_xform
       (exists
          (t : treeseq_one) (ts'' : nelist treeseq_one) (dfile : dirfile),
          ((⟦⟦ dummy3 = pushd t ts'' ⟧⟧
            ✶ ⟦⟦ treeseq_in_ds dummy dummy0 fsxp sm mscs dummy3 dummy2 ⟧⟧)
           ✶ ⟦⟦ tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4 dstbase
                  dstname dfile t ⟧⟧)
          ✶ ⟦⟦ treeseq_pred
                 (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4 dstbase
                    dstname dummy9) ts'' ⟧⟧).
  
  
    Lemma crash_ts_split': forall dummy1 dummy5 temp_fn srcinum dummy6 dummy4 dstbase
           dstname dummy9 dummy3 dummy dummy0 fsxp mscs dummy2 sm,
  treeseq_pred
        (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4 dstbase
           dstname dummy9) dummy3 ->
  treeseq_in_ds dummy dummy0 fsxp sm mscs dummy3 dummy2 ->
  emp
⇨⇨ crash_xform
     (exists t : treeseq_one,
        (⟦⟦ dummy3 = (t, []) ⟧⟧
         ✶ ⟦⟦ treeseq_in_ds dummy dummy0 fsxp sm mscs dummy3 dummy2 ⟧⟧)
        ✶ ⟦⟦ treeseq_pred
               (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4 dstbase
                  dstname dummy9) dummy3 ⟧⟧)
   ⋁ crash_xform
       (exists
          (t : treeseq_one) (ts'' : nelist treeseq_one) (dfile : dirfile) dummy4',
          ((⟦⟦ dummy3 = pushd t ts'' ⟧⟧
            ✶ ⟦⟦ treeseq_in_ds dummy dummy0 fsxp sm mscs dummy3 dummy2 ⟧⟧)
           ✶ ⟦⟦ tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4 dstbase
                  dstname dfile t ⟧⟧)
          ✶ ⟦⟦ treeseq_pred
                 (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4' dstbase
                    dstname dummy9) ts'' ⟧⟧).
  
	   Lemma proto_bytefile_nonnil: forall f pfy ufy fy block_off byte_off data F,
	      proto_bytefile_valid f pfy ->
	      unified_bytefile_valid pfy ufy ->
	      rep f fy ->
	      (F * arrayN (ptsto (V:=byteset)) (block_off * valubytes + byte_off) data)%pred
       (list2nmem (ByFData fy)) -> 
       length data > 0 ->
       byte_off < valubytes ->
	      selN (PByFData pfy) block_off nil <> [].
  
    Lemma length_le_middle: forall a b c,
  a = b * valubytes ->
  c < b ->
  valubytes <= a - c * valubytes.
  
    Lemma map_app_firstn_skipn: forall {A B} (data: list (A * B)) m,
  (map fst (firstn (m * valubytes) data) ++
   map fst (firstn valubytes (skipn (m * valubytes) data)))%list =
   map fst (firstn (valubytes + m * valubytes) data).
  
          
    Lemma bound_le_exfalso: forall F f fy off data,
        rep f fy ->
        (off < # (INODE.ABytes (DFAttr f)) -> False) ->
        (F * arrayN (ptsto (V:=byteset)) off data)%pred
       (list2nmem (ByFData fy)) -> 
       0 < length data ->
       False.
  
  Lemma arrayN_app_merge: forall Fd a head_data old_data tail_data,
(((Fd ✶ arrayN (ptsto (V:=byteset)) (a) head_data)
      ✶ arrayN (ptsto (V:=byteset)) (a + length head_data) old_data)
      ✶ arrayN (ptsto (V:=byteset)) (a + length head_data + length old_data) tail_data) 
      =p=> Fd ✶ arrayN (ptsto (V:=byteset)) (a) (head_data ++ old_data ++ tail_data).
        
Lemma list2nmem_arrayN_bound_app_middle: forall Fd a head_data old_data tail_data l,
  length old_data > 0 ->
  (Fd ✶ arrayN (ptsto (V:=byteset)) a 
    (head_data ++ old_data ++ tail_data))%pred (list2nmem l) ->
  a + (length head_data + (length old_data + length tail_data)) <= length l.

Lemma rep_modified_exists: forall f f' pfy ufy fy block_off head_data data old_data tail_data Fd,
  proto_bytefile_valid f pfy ->
  unified_bytefile_valid pfy ufy ->
  bytefile_valid ufy fy ->
  ByFAttr fy = DFAttr f ->
  # (INODE.ABytes (ByFAttr fy)) = length (ByFData fy) ->
  roundup (length (ByFData fy)) valubytes =
      length (DFData f) * valubytes ->
  length old_data = length data ->
  length data > 0 ->
  length head_data + length data <= valubytes ->
  DFAttr f' = DFAttr f ->
      (((Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) head_data)
✶ arrayN (ptsto (V:=byteset))
    (block_off * valubytes + length head_data) old_data)
✶ arrayN (ptsto (V:=byteset))
   (block_off * valubytes + length head_data +
    length old_data) tail_data)%pred (list2nmem (ByFData fy)) ->
  (diskIs (mem_except (list2nmem (DFData f)) block_off)
✶ block_off
 |-> (list2valu
        (firstn (length head_data)
           (valu2list (fst (selN (DFData f) block_off valuset0))) ++
         data ++
         skipn (length head_data + length data)
           (valu2list (fst (selN (DFData f) block_off valuset0)))),
     vsmerge (selN (DFData f) block_off valuset0)))%pred (list2nmem (DFData f')) ->
 rep f' {| ByFData:= firstn (length (ByFData fy)) (concat (updN (PByFData pfy) block_off 
                                  (valuset2bytesets ((list2valu
                                    (firstn (length head_data) 
                                    (valu2list (fst (selN (DFData f) block_off valuset0))) ++
                                    data ++
                                     skipn (length head_data + length data)
                                       (valu2list (fst (selN (DFData f) block_off valuset0)))%list),
                                 vsmerge (selN (DFData f) block_off valuset0))))));
                     ByFAttr:= ByFAttr fy |}.


  
Lemma dsupd_dsupd_iter_dwrite_middle: forall inum Ftree ts pathname fy ds bnl data f bn f' block_off Fd tail_data old_data,
  rep f fy ->
  length data > 0 ->
  length old_data = length data ->
  ((Fd
   ✶ (arrayN (ptsto (V:=byteset)) (block_off * valubytes)
        (firstn (length data / valubytes * valubytes) old_data)
      ✶ arrayN (ptsto (V:=byteset))
          ((block_off + length data / valubytes) * valubytes)
          (skipn (length data / valubytes * valubytes) old_data)))
  ✶ arrayN (ptsto (V:=byteset))
      (block_off * valubytes + length old_data) tail_data)%pred
   (list2nmem (ByFData fy)) ->
  0 < length (skipn (length data / valubytes * valubytes) data) ->
  length bnl = length data / valubytes ->
  (Ftree ✶ pathname |-> File inum f')%pred
    (dir2flatmem2
       (TStree
          (tsupd_iter ts pathname block_off
             (combine
                (map list2valu
                   (list_split_chunk (length data / valubytes)
                      valubytes
                      (firstn
                         (length data / valubytes * valubytes)
                         data)))
                (map vsmerge
                   (get_sublist (DFData f) block_off
                      (length data / valubytes))))) !!)) ->
  (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) ->
  tree_names_distinct (TStree ts !!) ->
  0 < length data / valubytes ->
  dsupd
    (dsupd_iter ds bnl
       (combine
          (map list2valu
             (list_split_chunk (length data / valubytes) valubytes
                (firstn (length data / valubytes * valubytes) data)))
          (map vsmerge
             (get_sublist (DFData f) block_off
                (length data / valubytes))))) bn
    (list2valu
       (skipn (length data / valubytes * valubytes) data ++
        skipn
          (length
             (skipn (length data / valubytes * valubytes) data))
          (valu2list
             (fst (selN (DFData f') (block_off + length data / valubytes) valuset0)))),
    vsmerge (selN (DFData f') (block_off + length data / valubytes) valuset0)) =
  dsupd_iter ds (bnl ++ [bn])
    (combine
       (map list2valu
          (list_split_chunk
             (roundup (length data) valubytes / valubytes) valubytes
             (data ++
              skipn (length data mod valubytes)
                (valu2list
                   (fst
                      (selN (DFData f) (block_off + length data / valubytes) valuset0))))))
       (map vsmerge
          (firstn (roundup (length data) valubytes / valubytes)
             (skipn block_off (DFData f))))).
    
 Lemma dsupd_dsupd_iter_dwrite_middle2: forall x inum Ftree ts pathname fy ds bnl data f f' block_off Fd tail_data old_data,
  rep f fy ->
  length data > 0 ->
  length old_data = length data ->
  ((Fd
   ✶ (arrayN (ptsto (V:=byteset)) (block_off * valubytes)
        (firstn (length data / valubytes * valubytes) old_data)
      ✶ arrayN (ptsto (V:=byteset))
          ((block_off + length data / valubytes) * valubytes)
          (skipn (length data / valubytes * valubytes) old_data)))
  ✶ arrayN (ptsto (V:=byteset))
      (block_off * valubytes + length old_data) tail_data)%pred
   (list2nmem (ByFData fy)) ->
  0 < length (skipn (length data / valubytes * valubytes) data) ->
  length bnl = length data / valubytes ->
  (Ftree ✶ pathname |-> File inum f')%pred
    (dir2flatmem2
       (TStree
          (tsupd_iter ts pathname block_off
             (combine
                (map list2valu
                   (list_split_chunk (length data / valubytes)
                      valubytes
                      (firstn
                         (length data / valubytes * valubytes)
                         data)))
                (map vsmerge
                   (get_sublist (DFData f) block_off
                      (length data / valubytes))))) !!)) ->
  (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) ->
  tree_names_distinct (TStree ts !!) ->
  0 < length data / valubytes ->
  dsupd
  (dsupd_iter ds bnl
     (combine
        (map list2valu
           (list_split_chunk (length data / valubytes) valubytes
              (firstn (length data / valubytes * valubytes) data)))
        (map vsmerge
           (get_sublist (DFData f) block_off
              (length data / valubytes))))) x
  (list2valu
     (skipn (length data / valubytes * valubytes) data ++
      skipn
        (length
           (skipn (length data / valubytes * valubytes) data))
        (valu2list
           (fst (selN (DFData f') (block_off + length data / valubytes) valuset0)))),
  vsmerge (selN (DFData f') (block_off + length data / valubytes) valuset0)) =
dsupd_iter ds (bnl ++ [x])%list
  (combine
     (map list2valu
        (list_split_chunk  (S (length data / valubytes)) valubytes
           (firstn ( (S (length data / valubytes)) * valubytes)
              (data ++
               skipn (length data mod valubytes)
                 (valu2list
                    (fst
                       (selN (DFData f) (block_off + length data / valubytes) valuset0)))))))
     (map vsmerge (get_sublist (DFData f) block_off  (S (length data / valubytes))))).
 
   Lemma tsupd_tsupd_iter_dwrite_middle2: forall Ftree inum Fd old_data tail_data ts pathname block_off data f fy f' fy',
   rep f fy ->
   rep f' fy' ->
   0 < length (skipn (length data / valubytes * valubytes) data) ->
   length old_data = length data ->
   tree_names_distinct (TStree ts !!) ->
   length data > 0 ->
   0 < length data / valubytes ->
   ((Fd
       ✶ (arrayN (ptsto (V:=byteset)) (block_off * valubytes)
            (firstn (length data / valubytes * valubytes) old_data)
          ✶ arrayN (ptsto (V:=byteset))
              ((block_off + length data / valubytes) * valubytes)
              (skipn (length data / valubytes * valubytes) old_data)))
      ✶ arrayN (ptsto (V:=byteset))
          (block_off * valubytes + length old_data) tail_data)%pred
       (list2nmem (ByFData fy)) ->
   min (length (ByFData fy) - (block_off * valubytes + length data))
       (hpad_length (length data)) = length tail_data ->
    (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) ->
    (Ftree ✶ pathname |-> File inum f')%pred
        (dir2flatmem2
           (TStree
              (tsupd_iter ts pathname block_off
                 (combine
                    (map list2valu
                       (list_split_chunk (length data / valubytes)
                          valubytes
                          (firstn
                             (length data / valubytes * valubytes)
                             data)))
                    (map vsmerge
                       (get_sublist (DFData f) block_off
                          (length data / valubytes))))) !!)) ->
   tsupd
  (tsupd_iter ts pathname block_off
     (combine
        (map list2valu
           (list_split_chunk (length data / valubytes) valubytes
              (firstn (length data / valubytes * valubytes) data)))
        (map vsmerge
           (get_sublist (DFData f) block_off
              (length data / valubytes))))) pathname
  (block_off + length data / valubytes)
  (list2valu
     (skipn (length data / valubytes * valubytes) data ++
      skipn
        (length
           (skipn (length data / valubytes * valubytes) data))
        (valu2list
           (fst (selN (DFData f') (block_off + length data / valubytes ) valuset0))))%list,
  vsmerge (selN (DFData f') (block_off + length data / valubytes ) valuset0)) =
tsupd_iter ts pathname block_off
  (combine
     (map list2valu
        (list_split_chunk (S (length data / valubytes)) valubytes
           (firstn (S (length data / valubytes) * valubytes)
              (data ++
               skipn (length data mod valubytes)
                 (valu2list
                    (fst (selN (DFData f) (block_off + length data / valubytes ) valuset0)))))))
     (map vsmerge
        (get_sublist (DFData f) block_off
           (S (length data / valubytes))))).
   
  
Ltac simpl_skipn_zero:=
match goal with
  | [H: 0 < length (skipn _ _) -> False |- _] =>
  apply Nat.nlt_ge in H;
  rewrite skipn_length in H; rewrite Nat.mul_comm in H;
  rewrite <- Nat.mod_eq in H; auto; inversion H
end.


Ltac simpl_min_zero:=
match goal with
  | [H: min _ _ = _,
      H0 : _ = 0 |- _] =>
  unfold hpad_length in H;
  rewrite H0 in H; simpl in H;
  rewrite Nat.min_0_r in H; symmetry in H;
  apply length_zero_iff_nil in H
end.
      
Lemma dsupd_eq_dwrite_middle:  forall ts Fd pathname inum Ftree old_data tail_data ds bn data f fy block_off,
        rep f fy ->
         length old_data = length data ->
         length data > 0 ->
         length data / valubytes = 0 ->
        ((Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) old_data)
      ✶ arrayN (ptsto (V:=byteset))
          (block_off * valubytes + length old_data) tail_data)%pred
       (list2nmem (ByFData fy)) ->
         min (length (ByFData fy) - (block_off * valubytes + length data))
             (hpad_length (length data)) = length tail_data ->
          (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) ->

              dsupd ds bn
                  (list2valu
                     (data ++
                      skipn (length data)
                        (valu2list (fst (selN (DFData f) block_off valuset0)))),
                  vsmerge (selN (DFData f) block_off valuset0)) =
                match
                  combine
                    (map list2valu
                       (list_split_chunk
                          (roundup (length data) valubytes / valubytes) valubytes
                          (data ++
                           skipn (length data mod valubytes)
                             (valu2list (fst (selN (DFData f) block_off valuset0))))))
                    (map vsmerge
                       (firstn (roundup (length data) valubytes / valubytes)
                          (skipn block_off (DFData f))))
                with
                | [] => ds
                | [h] => dsupd ds bn h
                | h :: _ :: _ => dsupd ds bn h
                end.
      
            Lemma tsupd_eq_dwrite_middle:  forall ts Fd pathname inum Ftree old_data tail_data data f fy block_off,
        rep f fy ->
         length old_data = length data ->
         length data > 0 ->
         length data / valubytes = 0 ->
        ((Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) old_data)
      ✶ arrayN (ptsto (V:=byteset))
          (block_off * valubytes + length old_data) tail_data)%pred
       (list2nmem (ByFData fy)) ->
         min (length (ByFData fy) - (block_off * valubytes + length data))
             (hpad_length (length data)) = length tail_data ->
          (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) ->

            tsupd ts pathname block_off
  (list2valu
     (data ++
      skipn (length data)
        (valu2list (fst (selN (DFData f)  block_off  valuset0)))),
  vsmerge (selN (DFData f)  block_off  valuset0)) =
tsupd_iter ts pathname block_off
  (combine
     (map list2valu
        (list_split_chunk
           (roundup (length data) valubytes / valubytes) valubytes
           (data ++
            skipn (length data mod valubytes)
              (valu2list
                 (fst
                    (selN (DFData f)
                    ( block_off + length data / valubytes ) valuset0))))))
     (map vsmerge
        (firstn (roundup (length data) valubytes / valubytes)
           (skipn block_off (DFData f))))).
      
Lemma skipn_not_nil': forall Fd f fy (data: list byte) 
               head_data old_data tail_data block_off,
    length head_data < valubytes
    -> length old_data = length data
    -> length data > 0
    -> rep f fy
    -> (((Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) head_data)
        ✶ arrayN (ptsto (V:=byteset))
          (block_off * valubytes + length head_data) old_data)
        ✶ arrayN (ptsto (V:=byteset))
          (block_off * valubytes + length head_data + length data) 
          tail_data)%pred (list2nmem (ByFData fy))
    -> skipn block_off (DFData f) <> [].
  
  
  
  
  
Lemma dsupd_dsupd_iter_eq_dwrite_first: forall Fd 
            (old_data tail_data head_data: list byteset) (data: list byte)
                   ds bn block_off f fy,
  length head_data < valubytes
  -> length old_data = length data
  -> length data > 0
  -> rep f fy
  -> (((Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) head_data)
      ✶ arrayN (ptsto (V:=byteset))
        (block_off * valubytes + length head_data) old_data)
      ✶ arrayN (ptsto (V:=byteset))
        (block_off * valubytes + length head_data + length data) 
        tail_data)%pred (list2nmem (ByFData fy))
  -> length data <= valubytes - length head_data
  -> dsupd ds bn (list2valu
           (firstn (length head_data) (valu2list 
              (fst (selN (DFData f) block_off valuset0))) ++
            data ++
            skipn (length head_data + length data)
              (valu2list (fst (selN (DFData f) block_off valuset0)))),
        vsmerge (selN (DFData f) block_off valuset0)) =
      dsupd_iter ds [bn]
        (combine (map list2valu (list_split_chunk 
          (roundup (length (firstn (length head_data)
                (valu2list (fst (selN (DFData f) block_off valuset0)))) +
                 length data) valubytes / valubytes) valubytes
           (firstn (length head_data)
              (valu2list (fst (selN (DFData f) block_off valuset0))) ++
            data ++
            skipn (tpad_length (length head_data + length data))
              (valu2list (fst (selN (DFData f)
                    (block_off + (length head_data + length data) / valubytes)
                    valuset0))))))
     (map vsmerge (firstn (roundup (length (firstn (length head_data)
                (valu2list (fst (selN (DFData f) block_off valuset0)))) +
                 length data) valubytes / valubytes) (skipn block_off (DFData f))))).

Lemma tsupd_tsupd_iter_eq_dwrite_first: forall ts Fd pathname
            (old_data tail_data head_data: list byteset) (data: list byte)
                   block_off f fy,
  length head_data < valubytes
  -> length old_data = length data
  -> length data > 0
  -> rep f fy
  -> (((Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) head_data)
      ✶ arrayN (ptsto (V:=byteset))
        (block_off * valubytes + length head_data) old_data)
      ✶ arrayN (ptsto (V:=byteset))
        (block_off * valubytes + length head_data + length data) 
        tail_data)%pred (list2nmem (ByFData fy))
  -> length data <= valubytes - length head_data
  -> tsupd ts pathname block_off (list2valu
           (firstn (length head_data) (valu2list 
              (fst (selN (DFData f) block_off valuset0))) ++
            data ++
            skipn (length head_data + length data)
              (valu2list (fst (selN (DFData f) block_off valuset0)))),
        vsmerge (selN (DFData f) block_off valuset0)) =
      tsupd_iter ts pathname block_off
        (combine (map list2valu (list_split_chunk 
          (roundup (length (firstn (length head_data)
                (valu2list (fst (selN (DFData f) block_off valuset0)))) +
                 length data) valubytes / valubytes) valubytes
           (firstn (length head_data)
              (valu2list (fst (selN (DFData f) block_off valuset0))) ++
            data ++
            skipn (tpad_length (length head_data + length data))
              (valu2list (fst (selN (DFData f)
                    (block_off + (length head_data + length data) / valubytes)
                    valuset0))))))
     (map vsmerge (firstn (roundup (length (firstn (length head_data)
                (valu2list (fst (selN (DFData f) block_off valuset0)))) +
                 length data) valubytes / valubytes) (skipn block_off (DFData f))))).


Lemma crash_dwrite_first1: forall Fd Fm Ftop fsxp 
                ds ts sm realcrash F_ hm' crash pathname mscs hm0 l
                (old_data tail_data head_data: list byteset) (data: list byte)
                 block_off f fy,
length head_data < valubytes
-> length old_data = length data
-> length data > 0
-> rep f fy
-> (((Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) head_data)
    ✶ arrayN (ptsto (V:=byteset))
      (block_off * valubytes + length head_data) old_data)
    ✶ arrayN (ptsto (V:=byteset))
      (block_off * valubytes + length head_data + length data) 
      tail_data)%pred (list2nmem (ByFData fy))
-> length data <= valubytes - length head_data
-> treeseq_in_ds Fm Ftop fsxp sm mscs ts ds
-> hashmap_subset l hm0 hm'
-> (forall (realcrash : rawpred) (hm' : hashmap),
   crash_xform realcrash
   =p=> crash_xform
        (exists (i : addr) (ds' : diskset) 
              (ts' : treeseq) (mscs' : BFile.BFILE.memstate) sm' (bnl : list addr),
           (((((LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm'
    ✶ ⟦⟦ i <= roundup (length (firstn (length head_data)
                 (valu2list (fst (selN (DFData f) block_off valuset0)))) + 
                 length data) valubytes / valubytes ⟧⟧)
   ✶ ⟦⟦ ds' = dsupd_iter ds bnl
          (combine (map list2valu (list_split_chunk i valubytes
                   (firstn (i * valubytes) (firstn (length head_data)
                         (valu2list (fst (selN (DFData f) block_off valuset0))) ++
                       data ++
                       skipn (tpad_length
                            (length head_data + length data))
                         (valu2list (fst (selN (DFData f)
                                (block_off + (length head_data +
                                  length data) / valubytes) valuset0)))))))
             (map vsmerge (get_sublist (DFData f) block_off i))) ⟧⟧)
  ✶ ⟦⟦ ts' = tsupd_iter ts pathname block_off
         (combine (map list2valu (list_split_chunk i valubytes
                  (firstn (i * valubytes) (firstn (length head_data)
                        (valu2list (fst (selN (DFData f) block_off valuset0))) ++
                      data ++
                      skipn (tpad_length
                           (length head_data + length data))
                        (valu2list (fst (selN (DFData f)
                                (block_off + (length head_data +
                                  length data) / valubytes) valuset0)))))))
            (map vsmerge (get_sublist (DFData f) block_off i)))⟧⟧) 
  ✶ ⟦⟦ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ⟧⟧)
  ✶ ⟦⟦ length bnl = i ⟧⟧)
  ✶ ⟦⟦ MSAlloc mscs' = MSAlloc mscs ⟧⟧) ->
     (F_ ✶ realcrash) * ⟦⟦ exists l : list (word hashlen * {sz : addr & word sz}),
      hashmap_subset l hm0 hm' ⟧⟧  =p=> crash hm')
-> crash_xform realcrash
    =p=> crash_xform
       (LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
        ⋁ (exists (bn : addr) (ds' : diskset) (ts' : treeseq) (mscs' : BFile.BFILE.memstate) sm',
     (((LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm'
        ✶ ⟦⟦ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ⟧⟧)
       ✶ ⟦⟦ ds' = dsupd ds bn (list2valu
                 (firstn (length head_data) 
                    (valu2list (fst (selN (DFData f) block_off valuset0))) ++
                  data ++
                  skipn
                    (length head_data + length data)
                    (valu2list (fst (selN (DFData f) block_off valuset0)))),
              vsmerge (selN (DFData f) block_off valuset0)) ⟧⟧)
      ✶ ⟦⟦ ts' = tsupd ts pathname block_off (list2valu
                (firstn (length head_data)
                   (valu2list (fst (selN (DFData f) block_off valuset0))) ++
                 data ++
                 skipn (length head_data + length data)
                   (valu2list (fst (selN (DFData f) block_off valuset0)))),
             vsmerge (selN (DFData f) block_off valuset0)) ⟧⟧)
     ✶ ⟦⟦ MSAlloc mscs' = MSAlloc mscs ⟧⟧))
-> realcrash ✶ F_ ⇨⇨ crash hm'.


Lemma dsupd_iter_dsupd_dwrite_first: forall Ftree Fd (old_data tail_data head_data: list byteset) (data: list byte) ds bn bnl block_off f f' fy pathname inum ts,
    length head_data < valubytes
  -> length old_data = length data
  -> length data > 0
  -> (length data <= valubytes - length head_data -> False)
  -> rep f fy
  -> tree_names_distinct (TStree ts !!)
  -> (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!))
  -> (((Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) head_data)
      ✶ arrayN (ptsto (V:=byteset))
        (block_off * valubytes + length head_data) old_data)
      ✶ arrayN (ptsto (V:=byteset))
        (block_off * valubytes + length head_data + length data) 
        tail_data)%pred (list2nmem (ByFData fy))
  -> (Ftree ✶ pathname |-> File inum f')%pred
        (dir2flatmem2
           (TStree
              (tsupd ts pathname block_off
                 (list2valu
                    (firstn (length head_data)
                       (valu2list (fst (selN (DFData f) block_off valuset0))) ++
                     firstn (valubytes - length head_data) data ++
                     skipn
                       (length head_data +
                        length
                          (firstn (valubytes - length head_data)
                             data))
                       (valu2list (fst (selN (DFData f) block_off valuset0)))),
                 vsmerge (selN (DFData f) block_off valuset0))) !!))
  -> dsupd_iter
  (dsupd ds bn
     (list2valu
        (firstn (length head_data)
           (valu2list (fst (selN (DFData f) block_off valuset0))) ++
         firstn (valubytes - length head_data) data ++
         skipn
           (length head_data +
            (valubytes - length head_data))
           (valu2list (fst (selN (DFData f) block_off valuset0)))),
     vsmerge (selN (DFData f) block_off valuset0))) bnl
  (combine
     (map list2valu
        (list_split_chunk
           (roundup
              (length data -
               (valubytes - length head_data)) valubytes /
            valubytes) valubytes
           (skipn (valubytes - length head_data) data ++
            skipn
              ((length data -
                (valubytes - length head_data)) mod valubytes)
              (valu2list
                 (fst
                    (selN (DFData f') (block_off + 1 +
                      (length data -
                       (valubytes - length head_data)) / valubytes)
                    valuset0))))))
     (map vsmerge
        (firstn
           (roundup
              (length data -
               (valubytes - length head_data)) valubytes /
            valubytes) (skipn (block_off + 1) (DFData f'))))) =
dsupd_iter ds (bn :: bnl)
  (combine
     (map list2valu
        (list_split_chunk
           (roundup
              (length
                 (firstn (length head_data)
                    (valu2list (fst (selN (DFData f) block_off valuset0)))) +
               length data) valubytes / valubytes) valubytes
           (firstn (length head_data)
              (valu2list (fst (selN (DFData f) block_off valuset0))) ++
            data ++
            skipn
              (tpad_length
                 (length head_data + length data))
              (valu2list
                 (fst
                    (selN (DFData f)(block_off +
                      (length head_data + length data) /
                      valubytes) valuset0))))))
     (map vsmerge
        (firstn
           (roundup
              (length
                 (firstn (length head_data)
                    (valu2list (fst (selN (DFData f) block_off valuset0)))) +
               length data) valubytes / valubytes)
           (skipn block_off (DFData f))))).
  
  
  
Lemma tsupd_iter_tsupd_dwrite_first: forall Ftree Fd (old_data tail_data head_data: list byteset) (data: list byte) block_off f f' fy pathname inum ts,
    length head_data < valubytes
  -> length old_data = length data
  -> length data > 0
  -> (length data <= valubytes - length head_data -> False)
  -> rep f fy
  -> tree_names_distinct (TStree ts !!)
  -> (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!))
  -> (((Fd ✶ arrayN (ptsto (V:=byteset)) (block_off * valubytes) head_data)
      ✶ arrayN (ptsto (V:=byteset))
        (block_off * valubytes + length head_data) old_data)
      ✶ arrayN (ptsto (V:=byteset))
        (block_off * valubytes + length head_data + length data) 
        tail_data)%pred (list2nmem (ByFData fy))
  -> (Ftree ✶ pathname |-> File inum f')%pred
        (dir2flatmem2
           (TStree
              (tsupd ts pathname block_off
                 (list2valu
                    (firstn (length head_data)
                       (valu2list (fst (selN (DFData f) block_off valuset0))) ++
                     firstn (valubytes - length head_data) data ++
                     skipn
                       (length head_data +
                        length
                          (firstn (valubytes - length head_data)
                             data))
                       (valu2list (fst (selN (DFData f) block_off valuset0)))),
                 vsmerge (selN (DFData f) block_off valuset0))) !!))
  -> tsupd_iter
  (tsupd ts pathname block_off
     (list2valu
        (firstn (length head_data)
           (valu2list (fst (selN (DFData f) block_off valuset0))) ++
         firstn (valubytes - length head_data) data ++
         skipn
           (length head_data +
            (valubytes - length head_data))
           (valu2list (fst (selN (DFData f) block_off valuset0)))),
     vsmerge (selN (DFData f) block_off valuset0))) pathname (block_off + 1)
  (combine
     (map list2valu
        (list_split_chunk
           (roundup
              (length data -
               (valubytes - length head_data)) valubytes /
            valubytes) valubytes
           (skipn (valubytes - length head_data) data ++
            skipn
              ((length data -
                (valubytes - length head_data)) mod valubytes)
              (valu2list
                 (fst
                    (selN (DFData f')
                    ( block_off + 1 +
                      (length data -
                       (valubytes - length head_data)) / valubytes)
                    valuset0))))))
     (map vsmerge
        (firstn
           (roundup
              (length data -
               (valubytes - length head_data)) valubytes /
            valubytes) (skipn (block_off + 1) (DFData f'))))) =
tsupd_iter ts pathname block_off
  (combine
     (map list2valu
        (list_split_chunk
           (roundup
              (length
                 (firstn (length head_data)
                    (valu2list (fst (selN (DFData f) block_off valuset0)))) +
               length data) valubytes / valubytes) valubytes
           (firstn (length head_data)
              (valu2list (fst (selN (DFData f) block_off valuset0))) ++
            data ++
            skipn
              (tpad_length
                 (length head_data + length data))
              (valu2list
                 (fst
                    (selN (DFData f)
                    ( block_off +
                      (length head_data + length data) /
                      valubytes ) valuset0))))))
     (map vsmerge
        (firstn
           (roundup
              (length
                 (firstn (length head_data)
                    (valu2list (fst (selN (DFData f) block_off valuset0)))) +
               length data) valubytes / valubytes)
           (skipn block_off (DFData f))))).
    
    
(* XXX: Definitions *)
  
Definition read_from_block fsxp inum ams block_off byte_off read_length :=
      let^ (ms1, first_block) <- AFS.read_fblock fsxp inum block_off ams;
      let data_init := (get_sublist (valu2list first_block) byte_off read_length) in
      Ret ^(ms1, data_init).


Definition read_middle_blocks fsxp inum fms block_off num_of_full_blocks:=
let^ (ms, data) <- ForN i < num_of_full_blocks
        Hashmap hm 
        Ghost [crash Fm Ftop Fd ts ds fy sm data']
        Loopvar [ms' (data : list byte)]
        Invariant 
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL ms') sm hm *
        [[[ (ByFData fy) ::: Fd * arrayN (ptsto (V:= byteset)) (block_off * valubytes) data']]] *
        [[ data = map fst (firstn (i * valubytes) data')]] *
        [[ treeseq_in_ds Fm Ftop fsxp sm ms' ts ds ]] *
        [[ MSAlloc fms = MSAlloc ms' ]]
        OnCrash crash
        Begin (
          let^(fms', (list : list byte)) <- 
                read_from_block fsxp inum ms' (block_off + i) 0 valubytes;
          Ret ^(fms', data ++ list))%list Rof ^(fms, nil);
Ret ^(ms, data).



Definition read_last fsxp inum fms off n:=
If(lt_dec 0 n)
{
  let^ (ms1, data_last) <- read_from_block fsxp inum fms off 0 n;
  Ret ^(ms1, data_last)%list
}
else
{
  Ret ^(fms, nil)%list
}.



Definition read_middle fsxp inum fms block_off n:=
let num_of_full_blocks := (n / valubytes) in
let off_final := (block_off + num_of_full_blocks) in 
let len_final := n mod valubytes in 
If (lt_dec 0 num_of_full_blocks)
{
  let^ (ms1, data_middle) <- read_middle_blocks fsxp inum fms block_off num_of_full_blocks;
  If(lt_dec 0 len_final)
  {
    let^ (ms2, data_last) <- read_last fsxp inum ms1 off_final len_final;
    Ret ^(ms2, data_middle++data_last)%list
  }
  else
  {
    Ret ^(ms1, data_middle)%list
  }
}
else
{
  let^ (ms1, data_last) <- read_last fsxp inum fms off_final len_final;
  Ret ^(ms1, data_last)%list
}.



Definition read_first fsxp inum fms block_off byte_off n :=
If (lt_dec (valubytes - byte_off) n)
{
    let first_read_length := (valubytes - byte_off) in 
    let^ (ms1, data_first) <- read_from_block fsxp inum fms block_off byte_off first_read_length; 
  
    let block_off := S block_off in
    let len_remain := (n - first_read_length) in  (* length of remaining part *)
    let^ (ms2, data_rem) <- read_middle fsxp inum ms1 block_off len_remain;
    Ret ^(ms2, data_first++data_rem)%list
}
else
{
   let first_read_length := n in (*# of bytes that will be read from first block*)
   let^ (ms1, data_first) <- read_from_block fsxp inum fms block_off byte_off first_read_length;   
   Ret ^(ms1, data_first)
}.


Definition read fsxp inum fms off len :=
If (lt_dec 0 len)                        (* if read length > 0 *)
{                    
  let^ (ms1, fattr) <- AFS.file_get_attr fsxp inum fms;          (* get file length *)
  let flen := # (INODE.ABytes fattr) in
  If (lt_dec off flen)                   (* if offset is inside file *)
  {                             
      let block_off := off / valubytes in              (* calculate block offset *)
      let byte_off := off mod valubytes in          (* calculate byte offset *)
      let^ (ms2, data) <- read_first fsxp inum ms1 block_off byte_off len;
      Ret ^(ms2, data)
  } 
  else                                                 (* if offset is not valid, return nil *)
  {    
    Ret ^(ms1, nil)
  }
} 
else                                                   (* if read length is not valid, return nil *)
{    
  Ret ^(fms, nil)
}. 



(* XXX Specs *)
Theorem read_from_block_ok: forall fsxp inum mscs block_off byte_off read_length,
    {< ds Fm Ftop Ftree pathname f fy Fd data ts sm,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           [[ AByteFile.rep f fy ]] *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:= byteset)) (block_off * valubytes + byte_off) data)) ]]] *
           [[ length data = read_length ]] *
           [[ 0 < length data ]] *
           [[ byte_off + read_length <= valubytes]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[ r = (map fst data) ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_from_block fsxp inum mscs block_off byte_off read_length.

Hint Extern 1 ({{_}} Bind (read_from_block _ _ _ _ _ _ ) _) => apply read_from_block_ok : prog.


Theorem read_middle_blocks_ok: forall fsxp inum mscs block_off num_of_full_blocks,
 {< ds ts sm Fm Ftop Ftree pathname f fy Fd data,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           [[ AByteFile.rep f fy ]] *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) (block_off * valubytes) data))]]] *
           [[ num_of_full_blocks > 0 ]] *
           [[ length data = mult num_of_full_blocks valubytes ]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[ r = (map fst data) ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_middle_blocks fsxp inum mscs block_off num_of_full_blocks.

Hint Extern 1 ({{_}} Bind (read_middle_blocks _ _ _ _ _) _) => apply read_middle_blocks_ok : prog.


Theorem read_last_ok: forall fsxp inum mscs off n,
 {< ds ts sm  Fm Ftop Ftree pathname f fy Fd data,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           [[ AByteFile.rep f fy ]] *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) (off * valubytes) data))]]] *
           [[ length data = n ]] *
           [[ n < valubytes ]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[ r = (map fst data) ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_last fsxp inum mscs off n.

Hint Extern 1 ({{_}} Bind (read_last _ _ _ _ _) _) => apply read_last_ok : prog.

Theorem read_middle_ok: forall fsxp inum mscs off n,
 {< ds sm Fd Fm Ftop Ftree pathname f fy data ts,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           [[ AByteFile.rep f fy ]] *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) (off * valubytes) data))]]] *
           [[ length data = n ]] 
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[ r = (map fst data) ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_middle fsxp inum mscs off n.
	
Hint Extern 1 ({{_}} Bind (read_middle _ _ _ _ _) _) => apply read_middle_ok : prog.

Theorem read_first_ok: forall fsxp inum mscs block_off byte_off n,
 {< ds sm Fd Fm Ftop Ftree pathname f fy data ts,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           [[ AByteFile.rep f fy ]] *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) (block_off * valubytes + byte_off) data))]]] *
           [[ length data = n ]] *
           [[ n > 0 ]] *
           [[ byte_off < valubytes ]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[ r = (map fst data) ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_first fsxp inum mscs block_off byte_off n.

Hint Extern 1 ({{_}} Bind (read_first _ _ _ _ _ _) _) => apply read_first_ok : prog.

Theorem read_ok: forall fsxp inum mscs off n,
 {< ds sm Fd Fm Ftop Ftree pathname f fy data ts,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
           [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
           [[ AByteFile.rep f fy ]] *
           [[[ (ByFData fy) ::: (Fd * (arrayN (ptsto (V:=byteset)) off data))]]] *
           [[ (length data) = n ]]
    POST:hm' RET:^(mscs', r)
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[ r = (map fst data) ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] *
          [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read fsxp inum mscs off n.

Hint Extern 1 ({{_}} Bind (read _ _ _ _ _) _) => apply read_ok : prog.


Definition dwrite_to_block fsxp inum mscs block_off byte_off data :=
  let^ (ms1, block) <- AFS.read_fblock fsxp inum block_off mscs;
  let new_block := list2valu (firstn byte_off (valu2list block) ++ data ++ skipn (byte_off + length data) (valu2list block)) in
  ms2 <- AFS.update_fblock_d fsxp inum block_off new_block ms1;
  Ret ms2.
  
Definition dwrite_middle_blocks fsxp inum mscs block_off num_of_full_blocks data:=
   ms <- ForN i < num_of_full_blocks
        Hashmap hm 
        Ghost [crash Fm Ftop Ftree Ff pathname old_data f fy ds ts]
        Loopvar [ms']
        Invariant 
        exists ds' ts' sm' f' fy' bnl,
          let new_blocks := map list2valu (list_split_chunk 
                   i valubytes (firstn (i * valubytes) data)) in
                  
          let old_blocks := get_sublist (DFData f) block_off i in
        
          LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL ms') sm' hm *
          [[ treeseq_in_ds Fm Ftop fsxp sm' ms' ts' ds' ]] *
          [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
          [[ ts' = tsupd_iter ts pathname block_off
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
          [[ length bnl = i ]] *
          [[ treeseq_pred (treeseq_safe pathname (MSAlloc ms') (ts' !!)) ts' ]] *
          [[ (Ftree * pathname |-> File inum f')%pred  (dir2flatmem2 (TStree ts'!!)) ]] *
          [[ AByteFile.rep f' fy' ]] *
          [[[ (ByFData fy')::: (Ff * 
          arrayN (ptsto (V:= byteset)) (block_off * valubytes) 
            (merge_bs (firstn (i*valubytes) data) (firstn (i*valubytes) old_data)) *
          arrayN (ptsto(V:= byteset)) ((block_off + i) * valubytes) 
            (skipn (i * valubytes) old_data))]]] *
          [[ ByFAttr fy' = ByFAttr fy ]] *
          [[ MSAlloc mscs = MSAlloc ms' ]] *
          [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]]
        OnCrash crash
        Begin (
          let write_data := get_sublist data (i * valubytes) valubytes in
          fms' <- dwrite_to_block fsxp inum ms' (block_off + i) 0 write_data; 
          Ret (fms')) Rof ^(mscs);
  Ret (ms).
  
  Definition dwrite_last fsxp inum mscs block_off data :=
  If (lt_dec 0 (length data))
  {
      ms1 <- dwrite_to_block fsxp inum mscs block_off 0 data;
      Ret (ms1)
  }
  else
  {
      Ret ^(mscs)
  }.
  
  Definition dwrite_middle fsxp inum mscs block_off data:=
  let num_of_full_blocks := length data / valubytes in
  If(lt_dec 0 num_of_full_blocks)
  {
      let middle_data := firstn (num_of_full_blocks * valubytes) data in
      ms2 <- dwrite_middle_blocks fsxp inum mscs block_off num_of_full_blocks middle_data;
      
      let block_off := block_off + num_of_full_blocks in
      let remaining_data := skipn (num_of_full_blocks * valubytes) data in
      If(lt_dec 0 (length remaining_data))
      {
        ms3 <- dwrite_last fsxp inum (fst ms2) block_off remaining_data;
        Ret (ms3)
      }
      else
      {
        Ret (ms2)
      }
  }
  else
  {
      ms2 <- dwrite_last fsxp inum mscs block_off data;
      Ret (ms2)
  }.
  
  Definition dwrite_first fsxp inum mscs block_off byte_off data :=
  let write_length := length data in
  If(le_dec write_length (valubytes - byte_off))
  {
      ms1 <- dwrite_to_block fsxp inum mscs block_off byte_off data;
      Ret (ms1)
  }
  else
  {
      let first_write_length := valubytes - byte_off in
      let first_data := firstn first_write_length data in
      
      ms1 <- dwrite_to_block fsxp inum mscs block_off byte_off first_data;
      
      let block_off := block_off + 1 in
      let remaining_data := skipn first_write_length data in
      ms2 <- dwrite_middle  fsxp inum (fst ms1) block_off remaining_data;
      Ret (ms2)
   }.
  
  Definition dwrite fsxp inum mscs off data :=
  let write_length := length data in
  let block_off := off / valubytes in
  let byte_off := off mod valubytes in
  If (lt_dec 0 write_length)  
  { 
              ms1 <- dwrite_first fsxp inum mscs block_off byte_off data;
              Ret (ms1)
  }
  else
  {
    Ret ^(mscs)
  }.
  
Theorem dwrite_to_block_ok : forall fsxp inum block_off byte_off data mscs,
{< ds sm Fd Fm Ftop Ftree ts pathname f fy old_data head_data tail_data,
PRE:hm 
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
  [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
  [[ AByteFile.rep f fy ]] *
  [[[ (ByFData fy) ::: (Fd * 
           arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes) head_data *
          arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off) old_data *
				   arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off + length old_data) tail_data)]]] *
  [[ length old_data = length data]] *
  [[ length data > 0 ]] *
  [[ byte_off + length data <= valubytes ]] *
  [[ byte_off = length head_data ]] *
  [[ min (length (ByFData fy) - (block_off * valubytes + byte_off + length data)) 
         (valubytes - (byte_off + length data)) = length tail_data ]]
POST:hm' RET:^(mscs')  exists bn fy' f' ds' ts' sm',
  let old_blocks := selN (DFData f) block_off valuset0 in
  let head_pad := firstn byte_off (valu2list (fst old_blocks)) in
  let tail_pad := skipn (byte_off + length data) (valu2list (fst old_blocks))in
  let new_block := list2valu (head_pad ++ data ++ tail_pad) in

  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
  [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
  [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]] *
  [[ ds' = dsupd ds bn (new_block, vsmerge old_blocks) ]] *
  [[ ts' = tsupd ts pathname block_off (new_block, vsmerge old_blocks) ]] *
  [[ AByteFile.rep f' fy' ]] *
  [[[ (ByFData fy') ::: (Fd * 
          arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes) (merge_bs (map fst head_data) head_data) *
          arrayN (ptsto (V:=byteset))
          (block_off * valubytes + byte_off) (merge_bs data old_data) *
				   arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off + length data) (merge_bs (map fst tail_data) tail_data))]]] *
  [[ ByFAttr fy = ByFAttr fy' ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]]

XCRASH:hm'
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
  exists bn ds' ts' mscs' sm',
  let old_blocks := selN (DFData f) block_off valuset0 in
  let head_pad := firstn byte_off (valu2list (fst old_blocks)) in
  let tail_pad := skipn (byte_off + length data) (valu2list (fst old_blocks))in
  let new_block := list2valu (head_pad ++ data ++ tail_pad) in
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
  [[ ds' = dsupd ds bn (new_block, vsmerge old_blocks) ]] *
  [[ ts' = tsupd ts pathname block_off (new_block, vsmerge old_blocks) ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]]
>}  dwrite_to_block fsxp inum mscs block_off byte_off data.

 
  

Hint Extern 1 ({{_}} Bind (dwrite_to_block _ _ _ _ _ _) _) => apply dwrite_to_block_ok : prog.
  
Theorem dwrite_middle_blocks_ok : forall fsxp inum block_off num_of_full_blocks data mscs,
{< ds sm Fd Fm Ftop Ftree ts pathname f fy old_data,
PRE:hm 
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
     [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
     [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
     [[ AByteFile.rep f fy ]] *
     [[[ (ByFData fy) ::: (Fd * arrayN (ptsto (V:= byteset)) 
                          (block_off * valubytes) old_data)]]] *
     [[ length old_data = length data]] *
     [[ length data = mult num_of_full_blocks valubytes ]]
POST:hm' RET:^(mscs')  exists ts' fy' f' ds' sm' bnl,

    let new_blocks := map list2valu (list_split_chunk 
                   num_of_full_blocks valubytes data) in
                  
    let old_blocks := get_sublist (DFData f) block_off num_of_full_blocks in
    
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     [[ AByteFile.rep f' fy' ]] *
     [[[ (ByFData fy') ::: (Fd * arrayN (ptsto (V:= byteset)) (block_off * valubytes) (merge_bs data old_data))]]] *
     [[ ByFAttr fy = ByFAttr fy' ]] *
     [[ MSAlloc mscs = MSAlloc mscs' ]] *
     (* spec about files on the latest diskset *)
     [[ length bnl =  num_of_full_blocks ]] *
     [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
     [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ ts' = tsupd_iter ts pathname block_off 
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]] *
     [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]]
     
XCRASH:hm'
  exists i ds' ts' mscs' sm' bnl,
  
    let new_blocks := map list2valu (list_split_chunk 
                   i valubytes (firstn (i * valubytes) data)) in
                  
    let old_blocks := get_sublist (DFData f) block_off i in
  
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ i <= num_of_full_blocks ]] *
   [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
   [[ ts' = tsupd_iter ts pathname block_off
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
   [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
   [[ length bnl = i ]] *
   [[ MSAlloc mscs' = MSAlloc mscs ]]
>}  dwrite_middle_blocks fsxp inum mscs block_off num_of_full_blocks data.

Hint Extern 1 ({{_}} Bind (dwrite_middle_blocks _ _ _ _ _ _) _) => apply dwrite_middle_blocks_ok : prog.

 Theorem dwrite_last_ok : forall fsxp inum block_off data mscs,
{< ds sm Fd Fm Ftop Ftree ts pathname f fy old_data tail_data,
PRE:hm 
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
  [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
  [[ AByteFile.rep f fy ]] *
  [[[ (ByFData fy) ::: (Fd *
           arrayN (ptsto (V:=byteset)) 
              (block_off * valubytes) old_data *
           arrayN (ptsto (V:=byteset)) 
              (block_off * valubytes + length old_data) tail_data)]]] *
  [[ length old_data = length data]] *
  [[ length data < valubytes ]] *
  [[ min (length (ByFData fy) - (block_off * valubytes + length data)) 
         (valubytes - length data) = length tail_data ]]
POST:hm' RET:^(mscs')  exists bn fy' f' ds' ts' sm',
  let old_blocks := selN (DFData f) block_off valuset0 in
  let tail_pad := skipn (length data) (valu2list (fst old_blocks))in
  let new_block := list2valu (data ++ tail_pad) in
  ([[ length data = 0 ]] * 
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm) \/
  (LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
  [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
  [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]] *
  [[ ds' = dsupd ds bn (new_block, vsmerge old_blocks) ]] *
  [[ ts' = tsupd ts pathname block_off (new_block, vsmerge old_blocks) ]] *
  [[ AByteFile.rep f' fy' ]] *
  [[[ (ByFData fy') ::: (Fd * 
            arrayN (ptsto (V:=byteset)) 
              (block_off * valubytes) (merge_bs data old_data) *
            arrayN (ptsto (V:=byteset)) 
              (block_off * valubytes + length data) 
                  (merge_bs (map fst tail_data) tail_data))]]] *
  [[ ByFAttr fy = ByFAttr fy' ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]])

XCRASH:hm'
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
  exists bn ds' ts' mscs' sm',
  let old_blocks := selN (DFData f) block_off valuset0 in
  let tail_pad := skipn (length data) (valu2list (fst old_blocks))in
  let new_block := list2valu (data ++ tail_pad) in
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
  [[ ds' = dsupd ds bn (new_block, vsmerge old_blocks) ]] *
  [[ ts' = tsupd ts pathname block_off (new_block, vsmerge old_blocks) ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]]
>}  dwrite_last fsxp inum mscs block_off data.

Hint Extern 1 ({{_}} Bind (dwrite_last _ _ _ _ _) _) => apply dwrite_last_ok : prog.


 


Theorem dwrite_middle_ok : forall fsxp inum block_off data mscs,
{< ds sm Fd Fm Ftop Ftree ts pathname f fy old_data tail_data,
PRE:hm 
  let num_of_full_blocks := length data / valubytes in
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
  [[ tree_names_distinct (TStree ts !!) ]] *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
  [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
  [[ AByteFile.rep f fy ]] *
  [[[ (ByFData fy) ::: (Fd * 
                        arrayN (ptsto (V:=byteset)) 
			                    (block_off * valubytes) old_data *
		                    arrayN (ptsto (V:=byteset)) 
			                    (block_off * valubytes + length old_data) tail_data)]]] *
  [[ length old_data = length data]] *
  [[ length data > 0 ]] * 
  [[ min (length (ByFData fy) - (block_off * valubytes + length data)) 
         (hpad_length (length data)) = length tail_data ]]
POST:hm' RET:^(mscs')  exists bnl fy' f' ds' ts' sm',
  let num_of_full_blocks := length data / valubytes in
  let last_old_block := selN (DFData f) (block_off + num_of_full_blocks) valuset0 in
  let tail_pad := skipn (length data mod valubytes) (valu2list (fst last_old_block))in
  let new_blocks :=  map list2valu 
            (list_split_chunk (roundup (length data) valubytes / valubytes) valubytes (data ++ tail_pad)) in
  let old_blocks := firstn (roundup (length data) valubytes / valubytes) (skipn block_off (DFData f)) in

  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     [[ AByteFile.rep f' fy' ]] *
     [[[ (ByFData fy') ::: (Fd * 
                            arrayN (ptsto (V:= byteset)) 
                              (block_off * valubytes) (merge_bs data old_data) *
                            arrayN (ptsto (V:=byteset)) 
			                        (block_off * valubytes + length data)
			                          (merge_bs (map fst tail_data) tail_data))]]] *
     [[ ByFAttr fy = ByFAttr fy' ]] *
     [[ MSAlloc mscs = MSAlloc mscs' ]] *
     (* spec about files on the latest diskset *)
     [[ length bnl = (roundup (length data) valubytes / valubytes) ]] *
     [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
     [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ ts' = tsupd_iter ts pathname block_off 
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]] *
     [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]]
XCRASH:hm'
  exists i ds' ts' mscs' sm' bnl,
    let num_of_full_blocks := length data / valubytes in
    let last_old_block := selN (DFData f) (block_off + num_of_full_blocks) valuset0 in
    let tail_pad := skipn  (length data mod valubytes) (valu2list (fst last_old_block))in
    let new_blocks := map list2valu (list_split_chunk 
                   i valubytes (firstn (i * valubytes) (data ++ tail_pad))) in
    let old_blocks := get_sublist (DFData f) block_off i in
  
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ i <= (roundup (length data) valubytes / valubytes) ]] *
   [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
   [[ ts' = tsupd_iter ts pathname block_off
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
   [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
   [[ length bnl = i ]] *
   [[ MSAlloc mscs' = MSAlloc mscs ]]
>}  dwrite_middle fsxp inum mscs block_off data.

Hint Extern 1 ({{_}} Bind (dwrite_middle _ _ _ _ _) _) => apply dwrite_middle_ok : prog.


  
  Theorem dwrite_first_ok : forall fsxp inum block_off byte_off data mscs,
{< ds sm Fd Fm Ftop Ftree ts pathname f fy old_data head_data tail_data,
PRE:hm 
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
  [[ tree_names_distinct (TStree ts !!) ]] *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
  [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
  [[ AByteFile.rep f fy ]] *
  [[[ (ByFData fy) ::: (Fd * 
           arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes) head_data *
          arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off) old_data *
				   arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off + length data) tail_data)]]] *
  [[ length old_data = length data]] *
  [[ length data > 0 ]] *
  [[ byte_off < valubytes ]] *
  [[ byte_off = length head_data ]] *
  [[ min (length (ByFData fy) - (block_off * valubytes + byte_off + length data)) 
         (hpad_length (byte_off + length data)) = length tail_data ]]
POST:hm' RET:^(mscs')  exists bnl fy' f' ds' ts' sm',
  let first_old_block := selN (DFData f) block_off valuset0 in
  let head_pad := firstn byte_off (valu2list (fst first_old_block)) in
  let num_of_full_blocks := (byte_off + length data) / valubytes in
  let last_old_block := selN (DFData f) (block_off + num_of_full_blocks) valuset0 in
  let tail_pad := skipn (tpad_length (byte_off + length data))
                    (valu2list (fst last_old_block)) in
  let new_blocks :=  map list2valu 
            (list_split_chunk (roundup (length head_pad + length data) valubytes / valubytes)
              valubytes (head_pad ++ data ++ tail_pad)) in
  let old_blocks := firstn (roundup (length head_pad + length data) valubytes / valubytes)
                      (skipn block_off (DFData f)) in

  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     [[ AByteFile.rep f' fy' ]] *
     [[[ (ByFData fy') ::: (Fd * 
                            arrayN (ptsto (V:=byteset))  
				                      (block_off * valubytes) 
			                          (merge_bs (map fst head_data) head_data) *
                            arrayN (ptsto (V:= byteset)) 
                              (block_off * valubytes + byte_off) (merge_bs data old_data) *
                            arrayN (ptsto (V:=byteset)) 
			                        (block_off * valubytes + byte_off + length data)
			                          (merge_bs (map fst tail_data) tail_data))]]] *
     [[ ByFAttr fy = ByFAttr fy' ]] *
     [[ MSAlloc mscs = MSAlloc mscs' ]] *
     (* spec about files on the latest diskset *)
     [[ length bnl = roundup (length head_pad + length data) valubytes / valubytes ]] *
     [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
     [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ ts' = tsupd_iter ts pathname block_off 
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]] *
     [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]]
XCRASH:hm'
  exists i ds' ts' mscs' sm' bnl,
    let first_old_block := selN (DFData f) block_off valuset0 in
    let head_pad := firstn byte_off (valu2list (fst first_old_block)) in
    let num_of_full_blocks := (byte_off + length data) / valubytes in
    let last_old_block := selN (DFData f) (block_off + num_of_full_blocks) valuset0 in
    let tail_pad := skipn  (tpad_length (byte_off + length data))
                      (valu2list (fst last_old_block)) in
    let new_blocks := map list2valu (list_split_chunk i valubytes 
                        (firstn (i * valubytes) (head_pad ++ data ++ tail_pad))) in
    let old_blocks := get_sublist (DFData f) block_off i in
  
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ i <= (roundup (length head_pad + length data) valubytes / valubytes) ]] *
  [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
  [[ ts' = tsupd_iter ts pathname block_off
                (combine new_blocks (map vsmerge old_blocks)) ]] *
  [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
  [[ length bnl = i ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]]
>}  dwrite_first fsxp inum mscs block_off byte_off data.

Hint Extern 1 ({{_}} Bind (dwrite_first _ _ _ _ _ _) _) => apply dwrite_first_ok : prog.


 
  Theorem dwrite_ok : forall fsxp inum off data mscs,
    let block_off := off / valubytes in
  let byte_off := off mod valubytes in
{< ds sm Fd Fm Ftop Ftree ts pathname f fy old_data head_data tail_data,
PRE:hm 
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
  [[ tree_names_distinct (TStree ts !!) ]] *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
  [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
  [[ AByteFile.rep f fy ]] *
  [[[ (ByFData fy) ::: (Fd * 
           arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes) head_data *
          arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off) old_data *
				   arrayN (ptsto (V:=byteset))  
				  (block_off * valubytes + byte_off + length data) tail_data)]]] *
  [[ length old_data = length data]] *
  [[ byte_off < valubytes ]] *
  [[ byte_off = length head_data ]] *
  [[ min (length (ByFData fy) - (block_off * valubytes + byte_off + length data)) 
         (hpad_length (byte_off + length data)) = length tail_data ]]
POST:hm' RET:^(mscs')  exists bnl fy' f' ds' ts' sm',
  let first_old_block := selN (DFData f) block_off valuset0 in
  let head_pad := firstn byte_off (valu2list (fst first_old_block)) in
  let num_of_full_blocks := (byte_off + length data) / valubytes in
  let last_old_block := selN (DFData f) (block_off + num_of_full_blocks) valuset0 in
  let tail_pad := skipn (tpad_length (byte_off + length data))
                    (valu2list (fst last_old_block)) in
  let new_blocks :=  map list2valu 
            (list_split_chunk (roundup (length head_pad + length data) valubytes / valubytes)
              valubytes (head_pad ++ data ++ tail_pad)) in
  let old_blocks := firstn (roundup (length head_pad + length data) valubytes / valubytes)
                      (skipn block_off (DFData f)) in
     ([[ length data = 0 ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm')
     \/
     ([[ length data > 0 ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     [[ AByteFile.rep f' fy' ]] *
     [[[ (ByFData fy') ::: (Fd * 
                            arrayN (ptsto (V:=byteset))  
				                      (block_off * valubytes) 
			                          (merge_bs (map fst head_data) head_data) *
                            arrayN (ptsto (V:= byteset)) 
                              (block_off * valubytes + byte_off) (merge_bs data old_data) *
                            arrayN (ptsto (V:=byteset)) 
			                        (block_off * valubytes + byte_off + length data)
			                          (merge_bs (map fst tail_data) tail_data))]]] *
     [[ ByFAttr fy = ByFAttr fy' ]] *
     [[ MSAlloc mscs = MSAlloc mscs' ]] *
     (* spec about files on the latest diskset *)
     [[ length bnl = roundup (length head_pad + length data) valubytes / valubytes ]] *
     [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds']] *
     [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ ts' = tsupd_iter ts pathname block_off 
                  (combine new_blocks (map vsmerge old_blocks)) ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts' !!)) ts' ]] *
     [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]])
XCRASH:hm'
  exists i ds' ts' mscs' sm' bnl,
    let first_old_block := selN (DFData f) block_off valuset0 in
    let head_pad := firstn byte_off (valu2list (fst first_old_block)) in
    let num_of_full_blocks := (byte_off + length data) / valubytes in
    let last_old_block := selN (DFData f) (block_off + num_of_full_blocks) valuset0 in
    let tail_pad := skipn  (tpad_length (byte_off + length data))
                      (valu2list (fst last_old_block)) in
    let new_blocks := map list2valu (list_split_chunk i valubytes 
                        (firstn (i * valubytes) (head_pad ++ data ++ tail_pad))) in
    let old_blocks := get_sublist (DFData f) block_off i in
  
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
  [[ i <= (roundup (length head_pad + length data) valubytes / valubytes) ]] *
  [[ ds' = dsupd_iter ds bnl (combine new_blocks (map vsmerge old_blocks)) ]] *
  [[ ts' = tsupd_iter ts pathname block_off
                (combine new_blocks (map vsmerge old_blocks)) ]] *
  [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
  [[ length bnl = i ]] *
  [[ MSAlloc mscs' = MSAlloc mscs ]]
>}  dwrite fsxp inum mscs off data.
  
Hint Extern 1 ({{_}} Bind (dwrite _ _ _ _ _) _) => apply dwrite_ok : prog.


  Definition copydata fsxp src_inum tinum mscs :=
  let^ (mscs, attr) <- AFS.file_get_attr fsxp src_inum mscs;
  let^ (mscs, data) <- read fsxp src_inum mscs 0 #(INODE.ABytes attr);
  let^ (mscs) <- dwrite fsxp tinum mscs 0 data;
  let^ (mscs) <- AFS.file_sync fsxp tinum mscs;   (* sync blocks *)
  let^ (mscs, ok) <- AFS.file_set_attr fsxp tinum attr mscs;
  Ret ^(mscs, ok).
  
  
Theorem copydata_ok : forall fsxp srcinum tmppath tinum mscs,
{< ds ts sm Fm Ftop Ftree srcpath file tfile dstbase dstname dstfile fy tfy copy_data garbage,
PRE:hm
  LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
  [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
  [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
  [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ]] *
  [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                tfile dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
  [[ AByteFile.rep file fy ]] *
  [[ AByteFile.rep tfile tfy ]] *
  [[[ (ByFData fy) ::: (arrayN (ptsto (V:= byteset)) 0 copy_data) ]]] *
  [[[ (ByFData tfy) ::: (arrayN (ptsto (V:= byteset)) 0 garbage) ]]] *
  [[ INODE.ABytes(ByFAttr fy) = INODE.ABytes (ByFAttr tfy) ]] *
  [[ length copy_data > 0 ]]
POST:hm' RET:^(mscs', r)
  exists ds' ts' sm',
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
   [[ MSAlloc mscs' = MSAlloc mscs ]] *
   [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
   [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts' ]] *
   (([[ isError r ]] *
          exists f', [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]])
         \/ ([[ r = OK tt ]] *
             exists tf' tfy', ([[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                  tf' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]] *
            [[ AByteFile.rep tf' tfy' ]] *
            [[[ (ByFData tfy') ::: (arrayN (ptsto (V:= byteset)) 0 (map (fun x => (x, nil:list byte)) (map fst copy_data))) ]]] * [[ ByFAttr tfy' = ByFAttr fy]])))
XCRASH:hm'
  exists ds' ts' mscs' sm',
  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
   [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
   [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts']]
  >} copydata fsxp srcinum tinum mscs.
  
Hint Extern 1 ({{_}} Bind (copydata _ _ _ _) _) => apply copydata_ok : prog.

  
    Definition copy2temp fsxp src_inum tinum mscs :=
    let^ (mscs, attr) <- AFS.file_get_attr fsxp src_inum mscs;
    let^ (mscs, ok) <- AFS.file_truncate fsxp tinum (roundup (# (INODE.ABytes attr)) valubytes / valubytes) mscs;
    match ok with
    | Err _ =>
        Ret ^(mscs, ok)
    | OK _ =>
        let^ (mscs, tattr) <- AFS.file_get_attr fsxp tinum mscs;
        let^ (mscs, ok) <-  AFS.file_set_attr fsxp tinum ((INODE.ABytes attr) , snd tattr) mscs;
        match ok with
        | OK _ =>    let^ (mscs, ok) <- copydata fsxp src_inum tinum mscs;
                            Ret ^(mscs, ok)
        | Err _ =>  
                            Ret ^(mscs, ok)
        end
    end.
   

  Theorem copy2temp_ok : forall fsxp srcinum tinum mscs,
    {< Fm Ftop Ftree ds ts sm tmppath srcpath file tfile fy dstbase dstname dstfile copy_data,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                tfile dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
      [[ AByteFile.rep file fy ]] *
      [[[ (ByFData fy) ::: (arrayN (ptsto (V:= byteset)) 0 copy_data) ]]] *
      [[ length (DFData tfile) <= length (DFData file) ]] *
      [[ length copy_data > 0 ]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts' sm',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       [[ MSAlloc mscs = MSAlloc mscs' ]] *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts' ]] *
       (([[ isError r]] *
          exists f',
          [[ (tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!))) ]])
         \/ ([[ r = OK tt ]] *
             exists tf' tfy', ([[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                  tf' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]] *
            [[ AByteFile.rep tf' tfy' ]] *
            [[[ (ByFData tfy') ::: (arrayN (ptsto (V:= byteset)) 0 (map (fun x => (x, nil:list byte)) (map fst copy_data))) ]]] * [[ ByFAttr tfy' = ByFAttr fy]])))
    XCRASH:hm'
     exists ds' ts' sm' mscs',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts']]
    >} copy2temp fsxp srcinum tinum mscs.

Hint Extern 1 ({{_}} Bind (copy2temp _ _ _ _) _) => apply copy2temp_ok : prog.


  Definition copy_and_rename fsxp src_inum tinum (dstbase:list string) (dstname:string) mscs :=
    let^ (mscs, ok) <- copy2temp fsxp src_inum tinum mscs;
    match ok with
      | Err _ =>
        let^ (mscs) <- AFS.tree_sync fsxp mscs;
        (* Just for a simpler spec: the state is always (d, nil) after this function *)
        Ret ^(mscs, ok)
      | OK _ =>
        let^ (mscs, r) <- AFS.rename fsxp the_dnum [] temp_fn dstbase dstname mscs;
        let^ (mscs) <- AFS.tree_sync fsxp mscs;
        Ret ^(mscs, r)
    end.
  
  Theorem copy_and_rename_ok : forall fsxp srcinum tinum (dstbase: list string) (dstname:string) mscs,
    {< Fm Ftop Ftree ds ts sm srcpath file tfile fy copy_data dstfile,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
     [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
       [[ treeseq_pred (treeseq_safe [temp_fn] (MSAlloc mscs) (ts !!)) ts ]] * 
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum file tinum 
                tfile dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
      [[ AByteFile.rep file fy ]] *
      [[[ (ByFData fy) ::: (arrayN (ptsto (V:= byteset)) 0 copy_data) ]]] *
     [[ dirtree_inum (TStree ts!!) = the_dnum ]] *
     [[ length (DFData tfile) <= length (DFData file) ]] *
     [[ length copy_data > 0 ]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts' sm',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
      (([[ isError r ]] *
         (exists f' dfile,
         [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dfile) ts' ]] *
         [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum file tinum 
                f' dstbase dstname dfile (dir2flatmem2 (TStree ts'!!)) ]])) \/
       ([[r = OK tt]] *
         (exists dfile dfy,
           [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dfile) ts' ]] *
           [[ tree_with_src Ftree srcpath [temp_fn] srcinum file dstbase dstname dfile  (dir2flatmem2 (TStree ts'!!)) ]] *
            [[AByteFile.rep dfile dfy ]] * 
            [[[ (ByFData dfy) ::: (arrayN (ptsto (V:= byteset)) 0 (map (fun x => (x, nil:list byte)) (map fst copy_data))) ]]] *
            [[ ByFAttr fy = ByFAttr dfy ]])))
    XCRASH:hm'
      exists mscs' ds' ts' sm',
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       ((exists t, [[ ts' = (t, nil) ]] * 
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts']] )
       \/ (exists t ts'' dfile, [[ ts' = pushd t ts'' ]] * 
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dfile t ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts'' ]] ))
    >} copy_and_rename fsxp srcinum tinum dstbase dstname mscs.

 Hint Extern 1 ({{_}} Bind (copy_and_rename _ _ _ _ _ _) _) => apply copy_and_rename_ok : prog. 

   

