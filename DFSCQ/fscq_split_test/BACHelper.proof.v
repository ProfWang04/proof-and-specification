Proof.
  intros.
  rewrite concat_map.
  repeat (rewrite map_map; simpl).
  replace  (fun x : valuset => map (fun x0 : byteset => (fst x0, [])) (valuset2bytesets x))
    with ((fun x : valuset => valuset2bytesets (fst x, []))).
  reflexivity.
  apply functional_extensionality; intros.
  replace (map (fun x0 : byteset => (fst x0, [])) (valuset2bytesets x))
  with (map (fun x0 : byte => (x0, nil: list byte)) (map fst (valuset2bytesets x))).
  rewrite mapfst_valuset2bytesets.
  unfold valuset2bytesets; simpl.
  rewrite v2b_rec_nil.
  rewrite l2b_cons_x_nil.
  reflexivity.
  rewrite valu2list_len; reflexivity.
  rewrite map_map; simpl.
  reflexivity.
Qed.
Proof.
  induction l; intros.
  reflexivity.
  destruct l'; simpl.
  rewrite merge_bs_nil.
  rewrite map_map; simpl.
  rewrite map_id; reflexivity.
  rewrite IHl; reflexivity.
Qed.
  Proof.
    intros.
    unfold treeseq_pred, tree_rep in *.
    eapply NEforall_d_in'.
    intros.
    eapply tsupd_d_in_exists in H0.
    destruct H0.
    intuition.
    eapply tree_names_distinct_treeseq_one_upd; eauto.
    eapply NEforall_d_in in H as Hx.
    2: instantiate (1 := x0); eauto.
    intuition.
    eapply NEforall_d_in in H as Hx.
    2: instantiate (1 := x0); eauto.
    intuition.
    destruct H3.
(*     unfold tree_with_tmp in H3. *)
    rewrite H2.
    left.
    eexists {|
             DFData := (DFData x1) ⟦ off := vs ⟧;
             DFAttr := DFAttr x1|}.
    eapply treeseq_one_upd_tree_rep_tmp; eauto.
    right.
    rewrite H2.
    left.
    eapply treeseq_one_upd_tree_rep_src; eauto.
    right; right.
    unfold tree_with_dst in *.
    destruct H5.
    exists x1.
    rewrite H2.
    eapply dirents2mem2_treeseq_one_upd_src; eauto.
    pred_apply; cancel.
  Qed.
 Proof.
    intros.
    unfold treeseq_pred, tree_rep in *.
    eapply NEforall_d_in'.
    intros.
    destruct H1; simpl in H1.
    eapply NEforall_d_in in H0 as Hx.
    apply Hx.
    rewrite H1; unfold d_in; left; reflexivity.
    destruct H1.
    rewrite <- H1.
    apply H.
    eapply NEforall_d_in in H0 as Hx.
    apply Hx.
    unfold d_in; right; auto.
 Qed.
 Proof.
  induction vsl; simpl; intros.
  auto.
  apply IHvsl.
  apply treeseq_upd_off_tree_rep; auto.
 Qed.
Proof.
  unfold subset_invariant_bs; intros.
  apply emp_empty_mem_only in H0.
  unfold Mem.empty_mem in H0.
  assert (forall x, bsl x = bsl' x).
  intros.
  destruct H with (a:= x).
  auto.
  destruct H1.
  rewrite H0 in H1.
  contradiction.
  rewrite H0 in H1.
  unfold emp.
  intros.
  symmetry; apply H1.
Qed.
Proof.   
  intros.
  unfold synced_bdata.
  repeat rewrite map_length.
  reflexivity.
Qed.
Proof.
  intros.
  unfold AByteFile.rep; intros.
  repeat eexists.
  instantiate (1:=mk_proto_bytefile (map valuset2bytesets (DFData f))).
  reflexivity.
  instantiate (1:= mk_unified_bytefile (concat (map valuset2bytesets (DFData f)))).
  reflexivity.
  unfold bytefile_valid.
  simpl.
  rewrite firstn_length_l.
  reflexivity.
  rewrite concat_hom_length with (k:= valubytes).
  rewrite map_length.
  eapply le_trans.
  apply roundup_ge with (sz := valubytes); auto.
  rewrite H; apply le_n.
  apply Forall_map_vs2bs.
  simpl.
  rewrite firstn_length_l.
  reflexivity.
  rewrite concat_hom_length with (k:= valubytes).
  rewrite map_length.
  eapply le_trans.
  apply roundup_ge with (sz := valubytes); auto.
  rewrite H; apply le_n.
  apply Forall_map_vs2bs.
  simpl.
  rewrite firstn_length_l.
  auto.
  rewrite concat_hom_length with (k:= valubytes).
  rewrite map_length.
  eapply le_trans.
  apply roundup_ge with (sz := valubytes); auto.
  rewrite H; apply le_n.
  apply Forall_map_vs2bs.
Qed.
Proof.
  intros.
  unfold tree_rep, treeseq_pred in *; simpl.
  eapply NEforall_d_in in H as Hx.
  destruct Hx.
  split.
  eapply tree_names_distinct_update_subtree.
  apply H0.
  apply TND_file.
  destruct H1.
  unfold tree_with_tmp in *; simpl.
  split; eauto.
  destruct H2.
  left.
  exists tf.
  do 2 destruct H2.
  exists x0.
  apply sep_star_comm in H2.
  apply sep_star_assoc in H2.
  eapply dir2flatmem2_update_subtree with (f':= tf) in H2.
  pred_apply; cancel.
  auto.
  right; auto.
  unfold tree_with_src in *; simpl in *.
  destruct H2.
  destruct H2.
  left.
  exists x.
  apply sep_star_comm.
  apply sep_star_assoc.
  apply sep_star_comm in H2.
  apply sep_star_assoc in H2.
  apply dir2flatmem2_find_subtree_ptsto_none in H2 as Hx.
  eapply update_subtree_path_notfound in Hx.
  rewrite Hx.
  pred_apply; cancel.
  all: auto.
  unfold tree_with_dst in *.
  right.
  destruct H2.
  exists x.
  apply sep_star_comm.
  apply sep_star_assoc.
  apply sep_star_comm in H2.
  apply sep_star_assoc in H2.
  apply dir2flatmem2_find_subtree_ptsto_none in H2 as Hx.
  eapply update_subtree_path_notfound in Hx.
  rewrite Hx.
  pred_apply; cancel.
  all: auto.
  apply latest_in_ds.
Qed.
Proof.
  intros.
  unfold roundup.
  rewrite mul_div.
  all: auto.
  apply Nat.mod_mul.
  all: omega.
Qed.
Proof.
  intros.
  unfold tree_with_tmp in *.
  destruct H.
  exists x.
  pred_apply; cancel.
  instantiate (1:= dstinum).
Qed.
Proof.
  intros.
  eapply treeseq_in_ds_eq with (a:= mscs'); eauto.
  eapply treeseq_in_ds_eq with (a:= mscs); eauto.
Qed.
Proof.
  induction names; intros.
  inversion H0.
  destruct H0.
  unfold not; intros; apply H; left; rewrite H0; auto.
  apply IHnames.
  unfold not; intros; apply H; right; auto.
  auto.
Qed.
Proof.
  induction tree; simpl in *; intros; auto.
  destruct a; simpl in *.
  destruct (string_dec s name); simpl in *.
  destruct H.
  left; auto.
  right; right; auto.
  destruct H.
  right; left; auto.
  apply IHtree in H.
  destruct H.
  left; auto.
  right; right; auto.
Qed.
Proof.
  induction tree; intros.
  unfold add_to_list.
  apply NoDup_cons.
  apply in_nil.
  apply NoDup_nil.
  destruct a; simpl in *.
  destruct (string_dec s fname); simpl in *.
  destruct H0; left; auto.
  apply NoDup_cons.
  unfold not; intros.
  apply in_add_to_list_or in H1; auto.
  destruct H1.
  apply H0; left; auto.
  apply NoDup_cons_iff in H.
  apply H; auto.
  apply IHtree.
  apply NoDup_cons_iff in H.
  apply H; auto.
  unfold not; intros; apply H0.
  right; auto.
Qed.
Proof.
  induction tree; simpl in *; intros; auto.
  destruct H.
  left; auto.
  right; auto.
  destruct a; simpl in *.
  destruct (string_dec s name); simpl in *.
  destruct H.
  left; auto.
  right; right; auto.
  destruct H.
  right; left; auto.
  apply IHtree in H.
  destruct H.
  left; auto.
  right; right; auto.
Qed.
Proof.
  intros.
  unfold tree_rep, treeseq_pred, tree_graft in *; simpl.
  eapply NEforall_d_in in H as Hx.
  destruct Hx.
  split.
  eapply tree_names_distinct_update_subtree.
  eauto.
  apply TND_dir; intros; eauto.
  rewrite Forall_forall; intros.
  apply in_map_iff in H6.
  do 2 destruct H6.
  apply in_add_to_list_tree_or in H7 as Hx.
  destruct Hx.
  rewrite <- H6; rewrite H8; simpl; apply TND_file.
  rewrite <- H6; apply H0; auto.

  apply NoDup_add_to_list; auto.
  destruct H5.
  left.
  destruct H5.
  exists f.
  unfold tree_with_tmp in *.
  destruct H5.
  exists x0.
  apply sep_star_comm;
  apply sep_star_assoc;
  eapply dirents2mem2_graft_file_replace;
  auto.
  pred_apply; cancel.
  left.
  
  unfold tree_with_src, tree_with_tmp in *.
  exists f.
  destruct H5.
  destruct H5.
  exists x.
  apply sep_star_comm;
  apply sep_star_assoc;
  eapply dirents2mem2_graft_file_none; auto.
  pred_apply; cancel.
  unfold tree_with_dst in *.
  destruct H5.
  exists x.
  apply sep_star_comm;
  apply sep_star_assoc;
  eapply dirents2mem2_graft_file_none; auto.
  pred_apply; cancel.
  apply latest_in_ds.
Qed. *)

(*  Lemma f_fy_ptsto_subset_b_lt: forall f fy block_off byte_off Fd old_data,
  (Fd ✶ arrayN ptsto_subset_b (block_off * valubytes + byte_off) old_data)%pred
         (list2nmem (ByFData fy)) ->
  AByteFile.rep f fy ->
  byte_off + Datatypes.length old_data <= valubytes ->
  Datatypes.length old_data > 0 ->
  block_off < Datatypes.length (DFData f).
  Proof. 
    intros.
    apply ptsto_subset_b_to_ptsto in H as H'.
    destruct H'.
    destruct H3.
    eapply inlen_bfile.
    4: eauto.
    all: eauto.
    omega.
  Qed. *)

  (* Hint Extern 1 (_ < Datatypes.length (DFData _)) => eapply f_fy_ptsto_subset_b_lt; eauto; omega. *)
  Hint Extern 1 (Forall (fun sublist : list byteset => Datatypes.length sublist = valubytes)
  (PByFData _)) => eapply proto_len; eauto.
  
  Lemma proto_len_updN: forall f pfy a v,
proto_bytefile_valid f pfy ->
Forall (fun sublist : list byteset => Datatypes.length sublist = valubytes)
  (PByFData pfy) ⟦ a := valuset2bytesets v⟧.
Proof.
  intros.
rewrite Forall_forall; intros.
apply in_updN in H0.
destruct H0.
rewrite H in H0.
apply in_map_iff in H0.
repeat destruct H0.
apply valuset2bytesets_len.
rewrite H0.
apply valuset2bytesets_len.
Qed.
Proof.
  intros.
  eapply ptsto_subset_b_to_ptsto in H as H''.
  destruct H''.
  destruct H2.
  apply list2nmem_arrayN_bound in H2.
  destruct H2.
  rewrite H2 in H3; simpl in *.
  rewrite H3 in H1; inversion H1.
  omega.
Qed. *)

(* Hint Extern 1 (_ * valubytes <= Datatypes.length (ByFData _)) => eapply fy_ptsto_subset_b_le_block_off; eauto; omega. *)

(* Lemma pfy_ptsto_subset_b_le_block_off: forall f pfy ufy fy block_off byte_off Fd old_data,
(Fd ✶ arrayN ptsto_subset_b (block_off * valubytes + byte_off) old_data)%pred
       (list2nmem (ByFData fy)) ->
byte_off + Datatypes.length old_data <= valubytes ->
Datatypes.length old_data > 0 ->
proto_bytefile_valid f pfy ->
unified_bytefile_valid pfy ufy ->
bytefile_valid ufy fy ->
block_off * valubytes <= Datatypes.length (concat (PByFData pfy)).
Proof.
  intros.
  rewrite concat_hom_length with (k:= valubytes); auto.
  erewrite <- unified_byte_protobyte_len; eauto.
  erewrite <- bytefile_unified_byte_len; eauto.
Qed.
Proof.
  intros.
  destruct (length data) eqn:D.
  apply length_zero_iff_nil in D.
  auto.

  apply arrayN_list2nmem in H0 as Hx.
  unfold AByteFile.rep in H; split_hypothesis.
  erewrite <- selN_map.
  rewrite <- H.
  erewrite proto_bytefile_unified_bytefile_selN; eauto.
  unfold get_sublist.
  rewrite <- (skipn_firstn_comm (a*valubytes)).
  rewrite skipn_skipn.
  rewrite <- skipn_firstn_comm.
  rewrite firstn_firstn.
  rewrite min_l.
  erewrite <- unified_bytefile_bytefile_firstn; eauto.
  rewrite skipn_firstn_comm.
  rewrite <- D; rewrite Nat.add_comm; auto.
  apply list2nmem_arrayN_bound in H0 as H'; destruct H';
  try apply length_zero_iff_nil in H7; omega.
  omega.
  erewrite bfile_protobyte_len_eq; eauto.
  eapply inlen_bfile; eauto.
  unfold AByteFile.rep; repeat eexists; eauto.
  omega.
  omega.
  eapply inlen_bfile; eauto.
  unfold AByteFile.rep; repeat eexists; eauto.
  omega.
  omega.
  apply byteset0.
Qed.
   Proof.
    intros; split; intros; pred_apply; cancel.
   Qed.
    Proof.
      unfold isSubset; intros.
      edestruct H. left.
      unfold mem_except.
      destruct (addr_eq_dec a0 a); eauto.
      destruct (addr_eq_dec a0 a); eauto.
      left.
      unfold mem_except.
      destruct (addr_eq_dec a0 a); eauto.
      omega.

      right.
      destruct H0.
      unfold mem_except.
      split;
      destruct (addr_eq_dec a0 a); eauto.
      omega.
    Qed.
   Proof.
    intros.
    apply sep_star_comm;
    apply mem_except_ptsto.
    apply ptsto_valid' in H1; rewrite H2; eauto.
        
    eapply H.
    apply isSubset_mem_except; eauto.
    apply sep_star_comm in H1;
    apply ptsto_mem_except in H1; eauto.
  Qed. *)
  
  Lemma incl_dup_head: forall A (a: A) b c,
    incl (a::b) c -> incl (a::a::b) c.
    Proof.
      unfold incl; intros.
      apply H.
      destruct H0.
      rewrite H0.
      apply in_eq.
      auto.
    Qed.
    Proof.
      intros.
      unfold ptsto_subset_b in *.
      destruct_lift H1.
      destruct H0 with (a:= a).
      apply exists_impl.
      exists dummy.
      apply sep_star_lift_apply'; auto.
      eapply subset_invariant_bs_ptsto_trans; eauto.

      apply exists_impl.
      destruct H2.
      apply ptsto_valid' in H1 as Hx.
      rewrite Hx in H3; unfold some_strip in H3; simpl in H3.
      exists (b_1 :: dummy).

      apply sep_star_lift_apply'; auto.
      apply sep_star_comm;
      apply mem_except_ptsto.
      auto.
        
      eapply H.
      apply isSubset_mem_except; eauto.
      apply sep_star_comm in H1;
      apply ptsto_mem_except in H1; eauto.
      
      apply incl_dup_head; eauto.
    Qed.
  Proof.
    induction l; simpl; intros.
    unfold subset_invariant_bs in *; simpl in *; intros.
    apply emp_star_r.
    eapply H; eauto.
    pred_apply; cancel.
    unfold subset_invariant_bs in *; intros.
    apply sep_star_assoc.
    eapply IHl; intros.
    eapply ptsto_subset_b_impl; eauto.
    eauto.
    pred_apply; cancel.
  Qed.
  Proof.
    unfold subset_invariant_bs; intros; split; intros;
    apply sep_star_comm;
    eapply H; eauto;
    pred_apply; cancel.
  Qed. 
  Proof.
    unfold subset_invariant_bs; intros; split; intros;
    apply sep_star_assoc;
    eapply H; eauto;
    pred_apply; cancel.
  Qed.
  Proof.
    intros; apply subset_invariant_bs_comm; apply subset_invariant_bs_arrayN_sep_r; auto.
  Qed. *)
  
  Lemma dsupd_iter_dsupd_head: forall bnl vsl bn vs ds,
  dsupd_iter (dsupd ds bn vs) bnl vsl = dsupd_iter ds (bn::bnl) (vs::vsl).
  Proof.
    intros; reflexivity.
  Qed.
  Proof.
    induction bnl; intros; simpl.
    symmetry in H; apply length_zero_iff_nil in H.
    rewrite H; simpl.
    reflexivity.
    destruct vsl.
    simpl in H; inversion H.
    simpl.
    apply IHbnl.
    simpl in H; inversion H; auto.
  Qed.
  Proof.
    induction l1; intros.
    simpl in H; symmetry in H; apply length_zero_iff_nil in H; subst; simpl.
    reflexivity.
    simpl in *.
    destruct l2.
    simpl in H; inversion H.
    simpl in *.
    rewrite IHl1. reflexivity.
    omega.
  Qed.
  Proof. intros; simpl; reflexivity. Qed.
  
  Lemma get_sublist_app_tail: forall A (l: list A) a b def,
  length l >= S (a + b) ->
  get_sublist l a (S b) = (get_sublist l a b ++ [selN l (a+b) def])%list.
  Proof.
    induction l; simpl; intros.
    inversion H.
    unfold get_sublist in *.
    simpl in *.
    destruct a0; simpl.
    destruct b; simpl.
    reflexivity.
    apply le_S_n in H.
    eapply IHl with (a:= 0) in H; simpl in *.
    rewrite H; reflexivity.
    apply le_S_n in H.
    
    eapply IHl with (a:= a0) in H; simpl in *.
    rewrite H.
    auto.
  Qed.
  Proof.
    intros; split; intros.
    destruct l.
    right; reflexivity.
    destruct n.
    left; reflexivity.
    simpl in H; inversion H.
    destruct H; subst; try reflexivity.
    apply firstn_nil.
  Qed.
  Proof.
    induction l; intros; split; intros.
    left; simpl; omega.
    apply skipn_nil.
    destruct n; simpl in *.
    inversion H.
    apply IHl in H.
    destruct H.
    left; omega.
    left; apply length_zero_iff_nil in H; omega.
    destruct H.
    apply skipn_oob; auto.
    inversion H.
  Qed.
   Proof.
    intros.
    apply list2nmem_arrayN_bound in H1 as Hb.
    destruct Hb.
    apply length_zero_iff_nil in H4; pose proof valubytes_ge_O; unfold datatype in *; omega.
    apply list2nmem_arrayN_bound in H2 as Hb'.
    destruct Hb'.
    apply length_zero_iff_nil in H5; pose proof valubytes_ge_O; unfold datatype in *; omega.
    replace (a * valubytes) with (a * valubytes + 0) in H1 by omega.
    eapply inlen_bfile in H1 as Hl; eauto.
    replace (a * valubytes) with (a * valubytes + 0) in H2 by omega.
    eapply inlen_bfile in H2 as Hl'; eauto.
    rewrite <- plus_n_O in *.
    unfold rep in H; split_hypothesis.
    rewrite H7, H6, H in H1.
    apply arrayN_list2nmem in H1 as Hx.
    assert (A: bytesets2valuset (firstn valubytes l) = selN (DFData f) a valuset0).
    rewrite Hx.
    rewrite firstn_firstn.
    rewrite min_l; auto.
    rewrite <- skipn_firstn_comm.
    rewrite firstn_firstn; rewrite min_l.
    rewrite skipn_firstn_comm.
    rewrite concat_hom_skipn with (k:= valubytes).
    rewrite skipn_map_comm.
    replace valubytes with (1 * valubytes) by omega.
    rewrite concat_hom_firstn.
    rewrite firstn_map_comm.
    erewrite firstn_1_selN.
    rewrite skipn_selN.
    rewrite <- plus_n_O.
    simpl.
    rewrite app_nil_r.
    rewrite valuset2bytesets2valuset; eauto.
    {
    unfold not; intros Hn.
    rewrite skipn_eq_nil in Hn.
    destruct Hn.
    unfold datatype in *; omega.
    unfold datatype in *.
    apply length_zero_iff_nil in H11; omega.
    }
    rewrite <- skipn_map_comm.
    rewrite <- H.
    eapply proto_skip_len; eauto.
    rewrite <- H.
    eapply proto_len; eauto.
    omega.
    
    
    unfold rep in H0; split_hypothesis.
    rewrite H12, H11, H0 in H2.
    apply arrayN_list2nmem in H2 as Hx'.
    assert (A': bytesets2valuset (firstn valubytes l) = selN (DFData f') a valuset0).
    rewrite Hx'.
    rewrite firstn_firstn.
    rewrite min_l; auto.
    rewrite <- skipn_firstn_comm.
    rewrite firstn_firstn; rewrite min_l.
    rewrite skipn_firstn_comm.
    rewrite concat_hom_skipn with (k:= valubytes).
    rewrite skipn_map_comm.
    replace valubytes with (1 * valubytes) by omega.
    rewrite concat_hom_firstn.
    rewrite firstn_map_comm.
    erewrite firstn_1_selN.
    rewrite skipn_selN.
    rewrite <- plus_n_O.
    simpl.
    rewrite app_nil_r.
    rewrite valuset2bytesets2valuset; eauto.
    {
    unfold not; intros Hn.
    rewrite skipn_eq_nil in Hn.
    destruct Hn.
    unfold datatype in *; omega.
    unfold datatype in *.
    apply length_zero_iff_nil in H16; omega.
    }
    rewrite <- skipn_map_comm.
    rewrite <- H0.
    eapply proto_skip_len; eauto.
    rewrite <- H0.
    eapply proto_len; eauto.
    omega.
    rewrite <- A; auto.
    apply byteset0.
    apply byteset0.
    apply valubytes_ge_O.
    pose proof valubytes_ge_O; unfold datatype in *; omega.
    apply valubytes_ge_O.
    pose proof valubytes_ge_O; unfold datatype in *; omega.
Qed.
   Proof. intros; omega. Qed.
   
      Lemma combine_cons: forall A B (a:A) (b:B) c d,
   (a, b)::combine c d = combine (a::c) (b::d).
   Proof. intros; simpl; auto. Qed.
   
   Lemma tsupd_iter_tsupd_head: forall vsl vs ts s pathname,
  tsupd_iter (tsupd ts pathname s vs) pathname (S s) vsl = tsupd_iter ts pathname s (vs::vsl).
  Proof.
    intros; reflexivity.
  Qed.
  Proof.
    induction vsl; intros; simpl in *.
    subst; rewrite <- plus_n_O; auto. 
    rewrite H; simpl.
    apply IHvsl.
    omega.
  Qed.
   Proof.
      intros.
      rewrite dsupd_iter_dsupd_tail; simpl.
      rewrite <- combine_app_tail.
      rewrite <- map_single.
      rewrite <- map_single with (f:= vsmerge).
      repeat rewrite <- map_app.
       
       erewrite bfile_selN_eq.
       rewrite <- get_sublist_app_tail.
       rewrite <- list_split_chunk_app_1.
       unfold get_sublist.
       rewrite <- firstn_sum_split.
       destruct (map vsmerge
          (firstn (S (Datatypes.length bnl)) (skipn block_off (DFData f)))) eqn:D.
       apply map_eq_nil in D; apply firstn_eq_nil in D.
       destruct D.
       inversion H6.
       apply skipn_eq_nil in H6.
       destruct H6.
       
       assert (block_off < Datatypes.length (DFData f)).
       eapply inlen_bfile with (j:= 0); try rewrite <- plus_n_O; eauto.
       rewrite valubytes_is; omega.
       rewrite H2; rewrite H3; rewrite valubytes_is; omega.
       
       apply le_lt_false in H6; auto.
       inversion H6.
       
       assert (block_off < Datatypes.length (DFData f)).
       eapply inlen_bfile with (j:= 0); try rewrite <- plus_n_O; eauto.
       rewrite valubytes_is; omega.
       rewrite H2; rewrite H3; rewrite valubytes_is; omega.
       
       rewrite H6 in H7; simpl in H7; inversion H7.
       
       rewrite combine_cons.
       rewrite <- map_cons.

       rewrite <- list_split_chunk_cons.
       replace ((valubytes + Datatypes.length bnl * valubytes))
          with ((Datatypes.length bnl * valubytes + valubytes)) by omega.
       rewrite <- D; eauto.
       rewrite firstn_length_l. omega.
       rewrite H3; rewrite valubytes_is; omega.
       apply firstn_length_l.
       rewrite H3; rewrite valubytes_is; omega.
       apply get_sublist_length.
       replace (Datatypes.length bnl * valubytes + valubytes)
          with ((S (Datatypes.length bnl)) * valubytes) by (simpl; omega).
       rewrite H3; rewrite valubytes_is; omega.
       
       
       apply lt_le_S.
       eapply inlen_bfile with (j:= 0); eauto.
       apply valubytes_ge_O.
       2: {
         rewrite <- plus_n_O; pred_apply.
         rewrite arrayN_split with (i:= length bnl * valubytes).
         rewrite Nat.mul_add_distr_r; cancel.
       }
       rewrite skipn_length.
       apply Nat.lt_add_lt_sub_r; simpl.
       rewrite H2; rewrite H3; rewrite valubytes_is; omega.
       eauto.
       eauto.
       eauto.
       
       pred_apply.
       rewrite arrayN_split with (i:= length bnl * valubytes).
       rewrite Nat.mul_add_distr_r; cancel.
       rewrite skipn_length.
       apply Nat.le_add_le_sub_l; simpl.
       rewrite H2; rewrite H3; rewrite valubytes_is; omega.
       repeat rewrite map_length.
       rewrite list_split_chunk_length.
       rewrite get_sublist_length.
       apply min_l.
       rewrite firstn_length_l.
       rewrite Nat.div_mul; auto.
       rewrite H3;  rewrite valubytes_is; omega.
       
       apply Nat.lt_le_incl.
       eapply inlen_bfile with (j:= 0); eauto.
       apply valubytes_ge_O.
       2: {
         rewrite <- plus_n_O; pred_apply.
         rewrite arrayN_split with (i:= length bnl * valubytes).
         rewrite Nat.mul_add_distr_r; cancel.
       }
       rewrite skipn_length.
       apply Nat.lt_add_lt_sub_r; simpl.
       rewrite H2; rewrite H3; rewrite valubytes_is; omega.
       auto.
       
       apply firstn_length_l.
       rewrite H3; rewrite valubytes_is; omega.
       rewrite combine_length.
       rewrite min_r.
       rewrite map_length; rewrite get_sublist_length; auto.
       
       apply Nat.lt_le_incl.
       eapply inlen_bfile with (j:= 0); eauto.
       apply valubytes_ge_O.
       2: {
         rewrite <- plus_n_O; pred_apply.
         rewrite arrayN_split with (i:= length bnl * valubytes).
         rewrite Nat.mul_add_distr_r; cancel.
       }
       rewrite skipn_length.
       apply Nat.lt_add_lt_sub_r; simpl.
       rewrite H2; rewrite H3; rewrite valubytes_is; omega.
       auto.
       
       repeat rewrite map_length.
       rewrite list_split_chunk_length.
       rewrite get_sublist_length.
       rewrite min_l; auto.
       rewrite firstn_length_l.
       rewrite Nat.div_mul; auto.
       rewrite H3;  rewrite valubytes_is; omega.
       apply Nat.lt_le_incl.
       eapply inlen_bfile with (j:= 0); eauto.
       apply valubytes_ge_O.
       2: {
         rewrite <- plus_n_O; pred_apply.
         rewrite arrayN_split with (i:= length bnl * valubytes).
         rewrite Nat.mul_add_distr_r; cancel.
       }
       rewrite skipn_length.
       apply Nat.lt_add_lt_sub_r; simpl.
       rewrite H2; rewrite H3; rewrite valubytes_is; omega.
       auto.
       
       apply firstn_length_l.
       rewrite H3; rewrite valubytes_is; omega.
   Qed.
   Proof.
      intros.
      rewrite tsupd_iter_tsupd_tail.
      rewrite <- combine_app_tail with (e1:= list2valu
       (get_sublist data (Datatypes.length bnl * valubytes) valubytes))
       (e2:= vsmerge (DFData f') ⟦ block_off + Datatypes.length bnl ⟧).
      rewrite <- map_single.
      rewrite <- map_single with (f:= vsmerge).
      repeat rewrite <- map_app.
       
       erewrite bfile_selN_eq.
       rewrite <- get_sublist_app_tail.
       rewrite <- list_split_chunk_app_1.
       unfold get_sublist.
       rewrite <- firstn_sum_split.
       destruct (map vsmerge
          (firstn (S (Datatypes.length bnl)) (skipn block_off (DFData f)))) eqn:D.
       apply map_eq_nil in D; apply firstn_eq_nil in D.
       destruct D.
       inversion H6.
       apply skipn_eq_nil in H6.
       destruct H6.
       
       assert (block_off < Datatypes.length (DFData f)).
       eapply inlen_bfile with (j:= 0); try rewrite <- plus_n_O; eauto.
       rewrite valubytes_is; omega.
       rewrite H2; rewrite H3; rewrite valubytes_is; omega.
       
       apply le_lt_false in H6; auto.
       inversion H6.
       
       assert (block_off < Datatypes.length (DFData f)).
       eapply inlen_bfile with (j:= 0); try rewrite <- plus_n_O; eauto.
       rewrite valubytes_is; omega.
       rewrite H2; rewrite H3; rewrite valubytes_is; omega.
       
       rewrite H6 in H7; simpl in H7; inversion H7.

       replace ((Datatypes.length bnl * valubytes + valubytes))
          with (S (Datatypes.length bnl) * valubytes) by (simpl; omega).
          replace (Datatypes.length bnl + 1) with (S (Datatypes.length bnl)) by omega.
       rewrite <- D; eauto.
       
       rewrite firstn_length_l. omega.
       rewrite H3; rewrite valubytes_is; omega.
       apply firstn_length_l.
       rewrite skipn_length;
       apply Nat.le_add_le_sub_l; simpl.
       rewrite H3; rewrite valubytes_is; omega.
       
       
       apply lt_le_S.
       eapply inlen_bfile with (j:= 0); eauto.
       apply valubytes_ge_O.
       2: {
         rewrite <- plus_n_O; pred_apply.
         rewrite arrayN_split with (i:= length bnl * valubytes).
         rewrite Nat.mul_add_distr_r; cancel.
       }
       rewrite skipn_length.
       apply Nat.le_add_le_sub_r; simpl.
       rewrite H2; rewrite H3; rewrite valubytes_is; omega.
       eauto.
       eauto.
       eauto.
       
       pred_apply.
       rewrite arrayN_split with (i:= length bnl * valubytes).
       rewrite Nat.mul_add_distr_r; cancel.
       rewrite skipn_length.
       apply Nat.le_add_le_sub_l; simpl.
       rewrite H2; rewrite H3; rewrite valubytes_is; omega.
       repeat rewrite map_length.
       rewrite list_split_chunk_length.
       rewrite get_sublist_length.
       apply min_l.
       rewrite firstn_length_l.
       rewrite Nat.div_mul; auto.
       rewrite H3;  rewrite valubytes_is; omega.
       
       apply Nat.lt_le_incl.
       eapply inlen_bfile with (j:= 0); eauto.
       apply valubytes_ge_O.
       2: {
         rewrite <- plus_n_O; pred_apply.
         rewrite arrayN_split with (i:= length bnl * valubytes).
         rewrite Nat.mul_add_distr_r; cancel.
       }
       rewrite skipn_length.
       apply Nat.lt_add_lt_sub_r; simpl.
       rewrite H2; rewrite H3; rewrite valubytes_is; omega.
       auto.
       
       apply firstn_length_l.
       rewrite H3; rewrite valubytes_is; omega.
        apply Nat.add_cancel_l.
       unfold datatype.
       rewrite combine_length.
       rewrite min_r.
       rewrite map_length; rewrite get_sublist_length; auto.
       
       apply Nat.lt_le_incl.
       eapply inlen_bfile with (j:= 0); eauto.
       apply valubytes_ge_O.
       2: {
         rewrite <- plus_n_O; pred_apply.
         rewrite arrayN_split with (i:= length bnl * valubytes).
         rewrite Nat.mul_add_distr_r; cancel.
       }
       rewrite skipn_length.
       apply Nat.lt_add_lt_sub_r; simpl.
       rewrite H2; rewrite H3; rewrite valubytes_is; omega.
       auto.
       
       repeat rewrite map_length.
       rewrite list_split_chunk_length.
       rewrite get_sublist_length.
       rewrite min_l; auto.
       rewrite firstn_length_l.
       rewrite Nat.div_mul; auto.
       rewrite H3;  rewrite valubytes_is; omega.
       apply Nat.lt_le_incl.
       eapply inlen_bfile with (j:= 0); eauto.
       apply valubytes_ge_O.
       2: {
         rewrite <- plus_n_O; pred_apply.
         rewrite arrayN_split with (i:= length bnl * valubytes).
         rewrite Nat.mul_add_distr_r; cancel.
       }
       rewrite skipn_length.
       apply Nat.lt_add_lt_sub_r; simpl.
       rewrite H2; rewrite H3; rewrite valubytes_is; omega.
       auto.
       
       apply firstn_length_l.
       rewrite H3; rewrite valubytes_is; omega.
   Qed.
    Proof.
      intros.
      split. 
      unfold pimpl; intros.
      apply arrayN_split with (i := b).
      rewrite merge_bs_firstn_comm.
      repeat rewrite firstn_firstn.
      repeat rewrite min_l; try omega.
      rewrite merge_bs_skipn_comm.
      repeat rewrite skipn_firstn_comm.
      pred_apply; cancel.
      
      rewrite arrayN_split with (i := b).
      rewrite merge_bs_firstn_comm.
      repeat rewrite firstn_firstn.
      repeat rewrite min_l; try omega.
      rewrite merge_bs_skipn_comm.
      repeat rewrite skipn_firstn_comm.
      cancel.
    Qed.
Proof.
  intros.
  apply diskIs_combine_upd in H.
  apply diskIs_eq in H.
  symmetry in H; apply list2nmem_upd_updN in H; auto.
Qed.
Proof.
  intros; subst.
  eapply list2nmem_arrayN_app_iff; eauto.
Qed.
Proof.
  intros.
  apply arrayN_list2nmem in H2 as Hx.
  rewrite firstn_oob in Hx.
  rewrite Hx.
  rewrite <- concat_hom_firstn with (k:= valubytes).
  rewrite <- H0.
  erewrite <- unified_bytefile_bytefile_firstn; eauto.
  rewrite firstn_skipn; auto.
  apply list2nmem_arrayN_bound in H2.
  destruct H2.
  subst; simpl in *.
  destruct H4; auto.
  omega.
  eapply proto_len; eauto.
  rewrite skipn_length; omega.
  apply byteset0.
Qed.
Proof. reflexivity. Qed.

Proof. intros; omega. Qed.

Proof.
  intros; apply list2nmem_arrayN_bound in H0; destruct H0; auto; destruct H0;
  destruct H; auto.
Qed.
Proof.
  intros.
  assert (A: (head_data ++ old_data ++ tail_data)%list <> []).
  unfold not; intros H';
  apply length_zero_iff_nil in H';
  repeat rewrite app_length in H'; omega.
  
  assert (A0: block_off <= length (PByFData pfy)).
  eapply block_off_le_length_proto_bytefile with (byte_off:= 0); 
  try rewrite <- plus_n_O; eauto; try omega; length_rewrite_l.
  
  apply list2nmem_arrayN_bound_nonnil in H5 as A1; 
  repeat rewrite app_length in A1; auto; try omega.
  
apply sep_star_assoc.
rewrite <- arrayN_app'; [| length_rewrite_l; auto].
apply sep_star_assoc.
rewrite <- arrayN_app'; [| length_rewrite_l; auto].
repeat rewrite <- merge_bs_app; [| length_rewrite_l; auto | length_rewrite_l; auto].

simpl.
unfold valuset2bytesets; simpl.
rewrite list2valu2list; [| length_rewrite_l; auto].
rewrite valuset2bytesets_rec_cons_merge_bs.
rewrite updN_firstn_skipn.
rewrite concat_app; simpl.
rewrite firstn_app_le; [ | length_rewrite_l; auto; eapply proto_len_firstn; eauto].
length_rewrite_l; [ | eapply proto_len_firstn; eauto].

destruct (le_dec (length (ByFData fy) - (block_off * valubytes + length head_data + length data))
       (valubytes - (length head_data + length data))).
       
(* XXX: Start of the Case 1 *)
rewrite min_l in H9; try omega.
rewrite firstn_app_l; [| length_rewrite_l; auto].
rewrite merge_bs_firstn_comm.
rewrite firstn_app_le; [| length_rewrite_l; auto].
rewrite firstn_length_l; [| length_rewrite_l; auto].
rewrite firstn_app_le; [| length_rewrite_l; auto].

replace (firstn (length head_data) (valu2list (fst (DFData f) ⟦ block_off ⟧)))
  with (map fst head_data).
  
replace (firstn
           (length (ByFData fy) - block_off * valubytes - length head_data -
            length data)
           (skipn (length head_data + length data)
              (valu2list (fst (DFData f) ⟦ block_off ⟧))))
  with (map fst tail_data).
rewrite fold_valuset2bytesets.
replace (firstn (length (ByFData fy) - block_off * valubytes)
          (valuset2bytesets (DFData f) ⟦ block_off ⟧))
with (head_data ++ old_data ++ tail_data)%list.
apply list2nmem_arrayN_app_general;  [| length_rewrite_l; auto; [eapply proto_len_firstn; eauto] | auto ].

eapply list2nmem_arrayN_app_iff_general.
2: erewrite <- proto_bytefile_bytefile_arrayN_app_end_eq; eauto; length_rewrite_l; auto.

length_rewrite_l; eapply proto_len_firstn; eauto.

replace (length (ByFData fy) - block_off * valubytes)
  with (length (head_data ++ old_data ++ tail_data)%list); [| length_rewrite_l].

replace  (valuset2bytesets (DFData f) ⟦ block_off ⟧)
with (skipn 0  (valuset2bytesets (selN (DFData f) block_off valuset0))) by auto.
erewrite bfile_bytefile_selN_firstn_skipn with (b:= 0); eauto;
[ unfold AByteFile.rep; repeat eexists; eauto |
  rewrite <- plus_n_O; eauto |
  length_rewrite_l; eauto].

rewrite <- mapfst_valuset2bytesets.
replace  (valuset2bytesets (DFData f) ⟦ block_off ⟧)
with (skipn 0  (valuset2bytesets (selN (DFData f) block_off valuset0))) by auto.
rewrite <- skipn_firstn_comm.
replace (length head_data + length data +
      (length (ByFData fy) - block_off * valubytes - length head_data -
       length data))
with (length (ByFData fy) - block_off * valubytes); [ | subst; omega].
rewrite firstn_map_comm.
replace (length (ByFData fy) - block_off * valubytes)
  with (length (head_data ++ old_data ++ tail_data)); [| length_rewrite_l; auto].
erewrite bfile_bytefile_selN_firstn_skipn with (b:= 0); eauto;
[ | unfold AByteFile.rep; repeat eexists; eauto |
  rewrite <- plus_n_O; eauto |
  length_rewrite_l; eauto].
rewrite skipn_map_comm.
rewrite <- H6.
rewrite <- app_length.
rewrite app_assoc.
rewrite skipn_app; auto.

rewrite <- mapfst_valuset2bytesets.
replace  (valuset2bytesets (DFData f) ⟦ block_off ⟧)
with (skipn 0  (valuset2bytesets (selN (DFData f) block_off valuset0))) by auto.
rewrite firstn_map_comm.

rewrite arrayN_app in H5.
erewrite bfile_bytefile_selN_firstn_skipn with (b:= 0); eauto;
[ unfold AByteFile.rep; repeat eexists; eauto |
  rewrite <- plus_n_O; pred_apply; cancel |
  length_rewrite_l; eauto].
(* XXX: End of Case 1 *)

(* XXX: Start of the Case 2 *)
rewrite min_r in H9; try omega.

assert (A2: block_off + 1 <= length (PByFData pfy)).
apply le_mult_weaken with (p:= valubytes); eauto.
erewrite <- unified_byte_protobyte_len; eauto.
eapply le_trans.
2: eapply bytefile_unified_byte_len; eauto.
rewrite Nat.mul_add_distr_r; simpl; omega.

rewrite firstn_app_le; [ length_rewrite_l; auto | length_rewrite_l; auto].
replace (length (ByFData fy) - block_off * valubytes -
         (length head_data +
          (length data + (valubytes - (length head_data + length data)))))
with (length (ByFData fy) - block_off * valubytes - valubytes) by omega.

replace (firstn (length head_data) (valu2list (fst (DFData f) ⟦ block_off ⟧)))
  with (map fst head_data).
  
replace (skipn (length head_data + length data)
              (valu2list (fst (DFData f) ⟦ block_off ⟧)))
  with (map fst tail_data).
rewrite fold_valuset2bytesets.
replace (valuset2bytesets (DFData f) ⟦ block_off ⟧)
with (head_data ++ old_data ++ tail_data)%list.
apply list2nmem_arrayN_middle with (b:= valubytes);  [length_rewrite_l; auto; eapply proto_len_firstn; eauto | length_rewrite_l; auto | auto].

apply arrayN_frame_mem_ex_range in H5 as Hx; repeat rewrite app_length in Hx.


erewrite mem_except_range_out_apply with (l2':= (head_data ++ old_data ++ tail_data)%list); length_rewrite_l; auto; [| eapply proto_len_firstn; eauto]; repeat rewrite <- plus_n_O.

replace (head_data ++ old_data ++ tail_data)%list with (concat (firstn 1 (skipn block_off (PByFData pfy)))).

rewrite app_assoc.
rewrite <- concat_app.
rewrite <- firstn_sum_split.

replace (length (ByFData fy) - block_off * valubytes - valubytes)
with (length (ByFData fy) - length (concat (firstn (block_off + 1) (PByFData pfy)))); [| length_rewrite_l; [rewrite Nat.mul_add_distr_r; simpl; omega | eapply proto_len_firstn; eauto] ].

rewrite <- firstn_app_le; [| length_rewrite_l; [| eapply proto_len_firstn; eauto] ].

rewrite <- concat_app.

replace (firstn (block_off + 1) (PByFData pfy) ++
          skipn (block_off + 1) (PByFData pfy))%list
with (PByFData pfy) by (symmetry; apply firstn_skipn).
rewrite <- H0.
rewrite <- H1.

replace (length head_data + (length old_data + length tail_data))
  with valubytes in Hx; [auto | omega].
  
rewrite Nat.mul_add_distr_r; simpl; omega.

rewrite firstn_1_selN with (def:= nil).
rewrite skipn_selN; rewrite <- plus_n_O.
simpl; rewrite app_nil_r.
erewrite proto_bytefile_unified_bytefile_selN; eauto.
unfold get_sublist.
rewrite <- skipn_firstn_comm.
erewrite <- unified_bytefile_bytefile_firstn; eauto; try omega.
rewrite skipn_firstn_comm.

eapply arrayN_list2nmem in H5; eauto.
replace (length (head_data ++ old_data ++ tail_data)%list) with valubytes in H5; auto; length_rewrite_l.
apply byteset0.
omega.

unfold not; intros Hy.
apply skipn_eq_nil in Hy.
destruct Hy.
omega.
apply length_zero_iff_nil in H10; omega.

replace  (valuset2bytesets (DFData f) ⟦ block_off ⟧)
with (firstn (length (head_data ++ old_data ++ tail_data)%list)(skipn 0  (valuset2bytesets (selN (DFData f) block_off valuset0)))).
erewrite bfile_bytefile_selN_firstn_skipn with (b:= 0); eauto;
[ unfold AByteFile.rep; repeat eexists; eauto |
  rewrite <- plus_n_O; eauto |
  length_rewrite_l; eauto].
  simpl; apply firstn_oob; length_rewrite_l; omega.
  

rewrite <- mapfst_valuset2bytesets.
replace  (valuset2bytesets (DFData f) ⟦ block_off ⟧)
with (firstn (length (head_data ++ old_data ++ tail_data)%list)(skipn 0  (valuset2bytesets (selN (DFData f) block_off valuset0))));
[| simpl; apply firstn_oob; length_rewrite_l; omega].
erewrite bfile_bytefile_selN_firstn_skipn with (b:= 0); eauto;
[ rewrite skipn_map_comm;
  rewrite <- H6;
  rewrite <- app_length;
  rewrite app_assoc;
  rewrite skipn_app; auto  | 
  unfold AByteFile.rep; repeat eexists; eauto |
  rewrite <- plus_n_O; eauto |
  length_rewrite_l; eauto].
  

rewrite <- mapfst_valuset2bytesets.

replace  (valuset2bytesets (DFData f) ⟦ block_off ⟧)
with (firstn (length (head_data ++ old_data ++ tail_data)%list)(skipn 0  (valuset2bytesets (selN (DFData f) block_off valuset0))));
[| simpl; apply firstn_oob; length_rewrite_l; omega].
erewrite bfile_bytefile_selN_firstn_skipn with (b:= 0); eauto;
[  | 
  unfold AByteFile.rep; repeat eexists; eauto |
  rewrite <- plus_n_O; eauto |
  length_rewrite_l; eauto].
  
  rewrite map_app; rewrite firstn_app_l; 
  [ symmetry; apply firstn_oob; length_rewrite_l; auto 
    |length_rewrite_l; auto].
(* XXX: End of Case 2 *)

apply lt_mult_weaken with (p:= valubytes); eauto.
erewrite <- unified_byte_protobyte_len; eauto.
eapply lt_le_trans.
2: eapply bytefile_unified_byte_len; eauto.
omega.

apply Forall_cons.
length_rewrite_l; auto.
apply valu2list_sublist_v.
Qed.
    Proof.
      intros.
      rewrite map_app; simpl; auto.
    Qed.
        Proof.
          intros.
          rewrite tsupd_latest in H1.
          rewrite treeseq_one_upd_alternative in H1.
          apply dir2flatmem2_find_subtree_ptsto in H0 as Hy; auto.
          rewrite Hy in H1; simpl in *.
          apply dir2flatmem2_find_subtree_ptsto in H1 as Hz; auto.
          erewrite find_update_subtree in Hz; eauto.
          inversion Hz.
          simpl; auto.
          apply tree_names_distinct_update_subtree; auto.
          apply TND_file.
        Qed.
        Proof.
          intros.
          unfold treeseq_one_upd.
          destruct (find_subtree tmppath (TStree t)) eqn:D; simpl; auto.
          destruct d; simpl; auto.
          eapply tree_names_distinct_update_subtree; auto.
          apply TND_file.
        Qed.
        Proof.
          intros.
          rewrite tsupd_latest.
          apply tree_names_distinct_treeseq_one_upd'; auto.
        Qed.
    Proof.
        induction l; intros.
        simpl in *.
        apply dir2flatmem2_find_subtree_ptsto in H0; auto.
        apply dir2flatmem2_find_subtree_ptsto in H1; auto.
        rewrite H0 in H1. inversion H1; auto.
        simpl in *.
        destruct a0.
        inversion H2.
        replace (block_off + S a0) with (S block_off + a0) by omega.
        rewrite <- selN_updN_ne with (n:= block_off)(v:= a) at 1.
        eauto.
        eapply dir2flatmem2_tsupd_updN in H0 as Hx.
        rewrite <- Hx.
        eapply IHl.
        3: eauto.
        apply tree_names_distinct_tsupd; auto.
        instantiate (1:= {| DFData := (DFData f) ⟦ block_off := a ⟧;
                            DFAttr := DFAttr f |}).
        rewrite tsupd_latest; auto.
        apply dirents2mem2_treeseq_one_upd_tmp; auto.
        omega.
        auto.
        rewrite tsupd_latest; auto.
        apply dirents2mem2_treeseq_one_upd_tmp; auto.
        omega.
      Qed.
        Proof.
          induction l; intros.
          auto.
          simpl.
          apply IHl.
          apply tree_names_distinct_tsupd; auto.
        Qed.
        Proof.
          intros.
          rewrite roundup_eq; auto; [| omega].
          rewrite <- divmult_plusminus_eq; auto.
          rewrite Nat.div_add; auto.
          rewrite Nat.div_same; auto; omega.
        Qed.
        Proof. 
          intros.
          unfold roundup; simpl.
          rewrite divup_eq_div; auto.
          rewrite mul_div; omega.
        Qed.
        Proof.
          unfold AByteFile.rep; intros.
          split_hypothesis.
          apply le_mult_weaken with (p:= valubytes); auto.
          erewrite <- bfile_protobyte_len_eq; eauto.
          erewrite <- unified_byte_protobyte_len; eauto.
          eapply unibyte_len; eauto.
          apply list2nmem_arrayN_bound_nonnil in H0.
          omega.
          unfold not; intros Hx; apply length_zero_iff_nil in Hx; omega.
       Qed.
        Proof.
          intros.
          destruct (lt_dec a b).
          left; rewrite min_l in H; omega.
          right; rewrite min_r in H; omega.
        Qed.
    Proof.
      intros.
      rewrite tsupd_iter_tsupd_tail.
      rewrite <- combine_app_tail with (e1:= list2valu
       (skipn (Datatypes.length data / valubytes * valubytes) data ++
        skipn
          (Datatypes.length
             (skipn (Datatypes.length data / valubytes * valubytes) data))
          (valu2list
             (fst
                (DFData f) ⟦ block_off + Datatypes.length data / valubytes ⟧))))
       (e2:= vsmerge (DFData f) ⟦ block_off + length data / valubytes  ⟧).
      rewrite <- map_single.
      rewrite <- map_single with (f:= vsmerge).
      repeat rewrite <- map_app.
       
       rewrite <- get_sublist_app_tail.
       rewrite <- list_split_chunk_app_1.
       unfold get_sublist.
       rewrite app_assoc.
       rewrite firstn_skipn.
       rewrite skipn_length.
       rewrite Nat.mul_comm; rewrite <- Nat.mod_eq; auto.
       replace (roundup (Datatypes.length data) valubytes / valubytes)
        with (Datatypes.length data / valubytes + 1); auto.
       replace (Datatypes.length data / valubytes + 1) with (S (Datatypes.length data / valubytes)) by omega; auto.
       
       rewrite roundup_div_S_eq; auto; try omega.
       rewrite skipn_length in H2.
       rewrite Nat.mul_comm in H2; rewrite <- Nat.mod_eq in H2; auto.
       
       length_rewrite_l.
       rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
       
       length_rewrite_l.
       symmetry; apply le_plus_minus.
       rewrite Nat.mul_comm; rewrite <- Nat.mod_eq; auto.
       apply mod_upper_bound_le'; auto.
       
       eapply inlen_bfile_S; eauto.
       pred_apply; cancel.
       
       length_rewrite_l.
       rewrite H1.
       rewrite skipn_length in H2; auto.
       
       length_rewrite_l.
       apply Nat.lt_le_incl.
       eapply inlen_bfile with (j:= 0); eauto.
       apply valubytes_ge_O.
       2: {
         rewrite <- plus_n_O; pred_apply; cancel.
       }
       length_rewrite_l.
       rewrite H1.
       rewrite skipn_length in H2; auto.
       rewrite Nat.div_mul; auto.
       rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
       auto.
       rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
       unfold datatype.
       length_rewrite_l; auto.
       
       rewrite Nat.div_mul; auto.
       rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
       rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
       
       apply Nat.lt_le_incl.
       eapply inlen_bfile with (j:= 0); eauto.
       apply valubytes_ge_O.
       2: {
         rewrite <- plus_n_O; pred_apply; cancel.
       }
       length_rewrite_l.
       rewrite H1.
       rewrite skipn_length in H2; auto.
       
       rewrite Nat.div_mul; auto.
       rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
       rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   Qed.
    Proof.
      intros; unfold roundup.
      apply Nat.mod_mul; auto.
    Qed.
   Proof.
      induction a; intros.
      simpl in *.
      auto.
      simpl.
      rewrite firstn_app_l.
      rewrite skipn_app_l.
      rewrite IHa; auto.
      simpl in *.
      rewrite skipn_length.
      omega.
      simpl in *.
      eapply le_trans.
      2: eauto.
      apply le_plus_l.
      eapply le_trans.
      2: eauto.
      apply le_plus_l.
    Qed.
   Proof.
      intros.
      pose proof between_mod_ne_0.
      eapply H2 in H.
      eauto.
      instantiate(1:= 1).
      all: simpl; omega.
  Qed.
  Proof.
    intros.
    unfold roundup.
    rewrite divup_small; simpl; auto; omega.
  Qed.
    Proof. intros; omega. Qed.
    
    Lemma le_sub_le_add_r': forall a b c,
    a > 0 -> a <= b - c -> a + c <= b.
    Proof. intros; omega. Qed.
    
    Lemma lt_sub_lt_add_l': forall a b c,
    a < b - c -> c + a < b.
    Proof. intros; omega. Qed.
    
    Lemma lt_sub_lt_add_r': forall a b c,
    a < b - c -> a + c < b.
    Proof. intros; omega. Qed.
    
      Lemma mm_dist': forall a b c,
  b >= c -> a - (b - c) = a + c - b.
  Proof. intros; omega. Qed.
  
   Lemma bytefile_length_eq: forall f f' fy fy',
  AByteFile.rep f fy ->
  AByteFile.rep f' fy' ->
  ByFAttr fy = ByFAttr fy' ->
  length (ByFData fy) = length (ByFData fy').
  Proof.
    intros.
    unfold AByteFile.rep in *; split_hypothesis.
    rewrite <- H10; rewrite H1; auto.
  Qed.
  Proof.
    intros.
    unfold roundup.
    repeat rewrite Nat.div_mul; auto.
    rewrite divup_sub_1; auto; try omega.
    destruct (divup a b) eqn:D.
    assert (divup a b > 0).
    apply divup_gt_0; omega.
    omega.
    omega.
  Qed.
  Proof.
      intros.
      simpl.
      rewrite firstn_app_l; try omega.
      rewrite skipn_app_r_ge; try omega.
      rewrite H; replace (b - b) with 0 by omega; simpl; auto.
      rewrite firstn_oob; auto; omega.
  Qed.
  Proof. intros; repeat rewrite app_assoc; auto. Qed.
  
  
    Lemma skipn_updN_oob_eq :
forall (A : Type) (l : list A) (i n : addr) (v : A),
n > i -> skipn n (l ⟦ i := v ⟧) = skipn n l.
Proof.
  intros.
  destruct (lt_dec i (length l)).
  rewrite updN_firstn_skipn; auto; simpl.
  rewrite skipn_app_r_ge.
  length_rewrite_l.
  destruct (n - i) eqn:D.
  omega.
  simpl.
  rewrite skipn_skipn.
  replace (n0 + (i + 1)) with n by omega; auto.
  length_rewrite_l.
  rewrite updN_oob; auto; omega.
Qed.
  Proof.
    intros; unfold roundup.
    repeat rewrite Nat.div_mul; auto.
    apply divup_sub_1; auto.
  Qed.
  Proof.
    induction a; intros.
    auto.
    simpl.
    rewrite firstn_firstn; rewrite min_l; try omega.
    rewrite skipn_firstn_comm.
    rewrite IHa; auto.
    apply le_plus_l.
  Qed.
  Proof.
    intros.
    destruct ts; destruct l; unfold latest; simpl in *.
    destruct H; simpl in *.
    auto.
    destruct H; simpl in *.
    inversion H0; simpl in *; auto.
  Qed.