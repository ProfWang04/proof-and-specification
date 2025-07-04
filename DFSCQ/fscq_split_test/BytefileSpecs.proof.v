  Proof.
    intros.
    rewrite Nat.mul_comm;
    rewrite <- Nat.div_mod; auto.
  Qed.
  Proof.
    intros;
    rewrite Nat.mul_comm; 
    rewrite <- Nat.mod_eq; auto.
  Qed.
  Proof.
    intros.
    unfold tree_with_src in H0.
    edestruct dir2flatmem2_find_subtree_ptsto_dir with 
      (tree := TStree ts !!) (fnlist := @nil string)
      (F := (exists dstinum : addr,
          (Ftree ✶ (srcpath |-> File srcinum file)
           ✶ tmppath |-> Nothing)
          ✶ (dstbase ++ [dstname])%list |-> File dstinum dstfile)%pred).
    distinct_names'.
    pred_apply; cancel.
    eexists x; auto.
  Qed.
   Proof.
    intros.
    destruct dummy3.
    destruct l.
    or_l; xcrash; eauto.
    or_r; xcrash.
    instantiate (1:= (t, l)).
    instantiate (1:= t0).
    simpl; auto.
    inversion H; simpl in *;
    inversion H2; eauto.
    split; simpl.
    inversion H; simpl; auto.
    inversion H; simpl in *;
    inversion H2; eauto.
  Qed.
   Proof.
    intros.
    destruct dummy3.
    destruct l.
    or_l; xcrash; eauto.
    or_r; xcrash.
    instantiate (1:= (t, l)).
    instantiate (1:= t0).
    simpl; auto.
    inversion H; simpl in *;
    inversion H2; eauto.
    split; simpl.
    inversion H; simpl; auto.
    inversion H; simpl in *;
    inversion H2; eauto.
    inversion H; simpl in *;
    inversion H2; eauto.
  Qed.
	   Proof.
	    intros.
	    erewrite proto_bytefile_unified_bytefile_selN; eauto.
	    unfold get_sublist, not; intros.
	    pose proof valubytes_ge_O as Hx.
	    eapply firstn_nonnil in Hx.
	    split_hypothesis.
	    rewrite H6 in H5.
	    inversion H5.
	    
	    unfold not; intros Hy.
	    assert (A: (block_off * valubytes) < length (UByFData ufy)).
	    erewrite unified_byte_protobyte_len with (k:= valubytes); eauto.
	    apply mult_lt_compat_r; auto.
	    erewrite bfile_protobyte_len_eq; eauto.
	    eapply inlen_bfile with (j:= byte_off); eauto.
	    
	    eapply skipn_nonnil in A.
	    split_hypothesis.
	    rewrite H6 in Hy.
	    inversion Hy.

	  erewrite bfile_protobyte_len_eq; eauto.
	  eapply inlen_bfile with (j:= byte_off); eauto.
  Qed.
  Proof.
    intros.
    rewrite valubytes_is in *; omega.
  Qed.
   Proof.
      intros.
      rewrite <- map_app.
      rewrite <- skipn_firstn_comm.
      replace (firstn (m * valubytes) data ) with (firstn (m * valubytes) (firstn (m * valubytes + valubytes) data)).
      rewrite firstn_skipn.
      rewrite Nat.add_comm; reflexivity.
      rewrite firstn_firstn.
      rewrite Nat.min_l.
      reflexivity.
      omega.
  Qed.
   Proof.
      intros; unfold rep in *; split_hypothesis.
      apply list2nmem_arrayN_bound in H1.
      destruct H1.
      apply length_zero_iff_nil in H1; omega.
      rewrite H5 in H6; rewrite H6 in H0; omega.
  Qed.
Proof.
  intros.
  rewrite sep_star_assoc.
  rewrite <- arrayN_app.
  rewrite sep_star_assoc.
  rewrite <- arrayN_app; auto.
Qed.
Proof.
  intros.
  apply list2nmem_arrayN_bound in H0 as Hx; destruct Hx.
  apply length_zero_iff_nil in H1; repeat rewrite app_length in H1; omega.
  repeat rewrite app_length in H1; auto.
Qed.
Proof.
  intros.
  exists({| PByFData:= (updN (PByFData pfy) block_off 
                            (valuset2bytesets ((list2valu
                              (firstn (length head_data) 
                              (valu2list (fst (selN (DFData f) block_off valuset0))) ++
                              data ++
                               skipn (length head_data + length data)
                                 (valu2list (fst (selN (DFData f) block_off valuset0)))%list),
                           vsmerge (selN (DFData f) block_off valuset0))))) |}).
                           
  exists ({| UByFData:= concat (updN (PByFData pfy) block_off 
                                    (valuset2bytesets ((list2valu
                                      (firstn (length head_data) 
                                      (valu2list (fst (selN (DFData f) block_off valuset0))) ++
                                      data ++
                                       skipn (length head_data + length data)
                                         (valu2list (fst (selN (DFData f) block_off valuset0)))%list),
                                   vsmerge (selN (DFData f) block_off valuset0))))) |}).

  match goal with | [H: (((_ ✶ _) ✶ _) ✶ _)%pred _ |- _] => apply arrayN_app_merge in H end.
  match goal with | [H: (_ * arrayN _ _ (_++_++_))%pred _ |- _] => 
  apply list2nmem_arrayN_bound_app_middle in H as Hx end.
  intuition.
  unfold proto_bytefile_valid; simpl.
  rewrite_proto.
  rewrite <- map_updN.
  match goal with | [H: (diskIs _ * _)%pred _ |- _] => apply diskIs_ptsto_updN in H end.
  match goal with | [H: DFData ?f = _ |- context[DFData ?f] ] => rewrite H end; auto.
  eapply inlen_bfile with (j:= length head_data); eauto.
  solve_rep.
  omega.
  instantiate (1:= old_data).
  omega.
  pred_apply; repeat rewrite arrayN_app; cancel.

  unfold unified_bytefile_valid; simpl.
  reflexivity.

  unfold bytefile_valid; simpl.
  length_rewrite_l; auto.
  erewrite <- unified_byte_protobyte_len; eauto.
  eapply bytefile_unified_byte_len; eauto.

  simpl; match goal with | [H: ByFAttr _ = _ |- _] => rewrite H end; auto.
  simpl; length_rewrite_l; auto.
  erewrite <- unified_byte_protobyte_len; eauto.
  eapply bytefile_unified_byte_len; eauto.

  simpl; match goal with | [H: (diskIs _ * _)%pred _ |- _] => apply diskIs_ptsto_updN in H end.
          match goal with | [H: DFData ?f = _ |- context[DFData ?f] ] => rewrite H end; auto.
  length_rewrite_l; auto.
  erewrite <- unified_byte_protobyte_len; eauto.
  eapply bytefile_unified_byte_len; eauto.
  eapply inlen_bfile with (j:= length head_data); eauto.
  solve_rep.
  omega.
  instantiate (1:= old_data).
  omega.
  pred_apply; repeat rewrite arrayN_app; cancel.
  omega.
Qed.
Proof.
      intros.
     assert (A: block_off + length data / valubytes <= length (DFData f)).
      apply Nat.lt_le_incl; eapply inlen_bfile with (j:= 0); eauto.
     apply valubytes_ge_O.
     2: rewrite <- plus_n_O; pred_apply; cancel.
     length_rewrite_l.
     match goal with | [H: 0 < length (skipn _ _) |- _] => 
        rewrite skipn_length in H end; omega.
   

     erewrite dsupd_iter_dsupd_tail; [ | solve_eq_dwrite_middle ]. 
      rewrite <- combine_app_tail; [ | solve_eq_dwrite_middle ].
      simpl.
    
    length_rewrite_l.
    repeat rewrite map_app_tail.
    rewrite <- list_split_chunk_app_1; solve_eq_dwrite_middle.
    rewrite mod_eq'; eauto.
    simpl_skipn_lt.
    erewrite <- bfile_selN_tsupd_iter_eq with (f:= f)(f':= f'); eauto; [ |
   unfold datatype; solve_eq_dwrite_middle]. 
    rewrite <- get_sublist_app_tail.
    rewrite roundup_div_S_eq; unfold get_sublist; eauto.
    rewrite app_assoc; rewrite firstn_skipn.
    rewrite Nat.add_1_r; eauto.
    
   eapply inlen_bfile_S; eauto.
   pred_apply; cancel.
   rewrite skipn_length; 
   repeat match goal with | [H: ?a = _ |- context[?a] ] => rewrite H; auto end.
   rewrite mod_eq'; auto.
   rewrite <-  le_plus_minus; auto.
   rewrite mod_eq'; auto.
   apply mod_upper_bound_le'; auto.
 Qed.
Proof.
     intros.
     assert (A: block_off + length data / valubytes <= length (DFData f)).
     apply Nat.lt_le_incl; eapply inlen_bfile with (j:= 0); eauto.
     apply valubytes_ge_O.
     2: rewrite <- plus_n_O; pred_apply; cancel.
     length_rewrite_l.
     match goal with | [H: 0 < length (skipn _ _) |- _] => 
        rewrite skipn_length in H end; omega.
   

     erewrite dsupd_iter_dsupd_tail; [ | solve_eq_dwrite_middle ]. 
      rewrite <- combine_app_tail; [ | solve_eq_dwrite_middle ].

    rewrite skipn_length.
    repeat rewrite map_app_tail.
    rewrite <- list_split_chunk_app_1; solve_eq_dwrite_middle.
    rewrite mod_eq'; eauto.
    simpl_skipn_lt.
    erewrite <- bfile_selN_tsupd_iter_eq with (f:= f)(f':= f'); eauto; [ |
   unfold datatype; solve_eq_dwrite_middle]. 
    rewrite <- get_sublist_app_tail.
    unfold get_sublist; eauto.
    rewrite app_assoc; rewrite firstn_skipn.
    rewrite firstn_oob with (n:=  (S (length data / valubytes) * valubytes)); auto.
    rewrite Nat.add_1_r; eauto.
    
    length_rewrite_l.
    rewrite Nat.add_sub_assoc; [| apply mod_upper_bound_le'; auto ].
    rewrite Nat.add_sub_swap; [| apply Nat.mod_le; auto ].
    rewrite mod_minus; auto; omega.
    
   eapply inlen_bfile_S; eauto.
   pred_apply; cancel.
   rewrite skipn_length; 
   repeat match goal with | [H: ?a = _ |- context[?a] ] => rewrite H; auto end.
   rewrite mod_eq'; auto.
   rewrite <-  le_plus_minus; auto.
   rewrite mod_eq'; auto.
   apply mod_upper_bound_le'; auto.
Qed.
 Proof.
   intros.
   erewrite <- bfile_selN_tsupd_iter_eq; eauto.
   rewrite firstn_app_le.
   rewrite firstn_oob with (n:= (S (length data / valubytes) * valubytes - length data)).
   repeat rewrite <- roundup_div_S_eq; auto.
   unfold get_sublist.
   eapply tsupd_tsupd_iter_merge'; eauto.
   simpl_skipn_lt.

   length_rewrite_l.
   apply Nat.le_add_le_sub_l.
  rewrite Nat.add_sub_assoc.
  rewrite Nat.add_sub_swap.
  rewrite  sub_mod_eq_round; auto.
  omega.
  apply Nat.mod_le; auto.
  apply mod_upper_bound_le'; auto.
  rewrite <- roundup_div_S_eq; auto.
  rewrite mul_div; auto.
  apply roundup_ge; auto.
   apply roundup_mod_0; auto.
   simpl_skipn_lt.
 
   unfold datatype; length_rewrite_l.
   rewrite Nat.div_mul; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   
   apply Nat.lt_le_incl.
   eapply inlen_bfile with (j:= 0); eauto.
   apply valubytes_ge_O.
   2: rewrite <- plus_n_O; pred_apply; cancel.
   
   length_rewrite_l.
   rewrite H2.
   rewrite skipn_length in H1; auto.
   
   rewrite Nat.div_mul; auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
   auto.
   rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
Qed.
Proof.
  intros.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= 0); eauto.
  apply valubytes_ge_O.
  2: rewrite <- plus_n_O; pred_apply; cancel.
  omega.
  
  rewrite roundup_lt_one; auto.
  rewrite Nat.div_same; auto; simpl.
  destruct (skipn block_off (DFData f)) eqn:D.
  apply skipn_eq_nil in D.
  destruct D.
  omega.
  apply length_zero_iff_nil in H6; omega.

  simpl.
  rewrite firstn_oob.
  erewrite skipn_selN_skipn in D; inversion D.
  rewrite Nat.mod_small; auto.
  apply Nat.div_small_iff; auto.

  length_rewrite_l.
  length_rewrite_l.
  rewrite Nat.mod_small; auto.
  rewrite <- le_plus_minus; auto.
  apply Nat.lt_le_incl; apply Nat.div_small_iff; auto.
  apply Nat.div_small_iff; auto.
  apply Nat.div_small_iff in H2; auto.
  omega.
Qed.
Proof.
  intros.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= 0); eauto.
  apply valubytes_ge_O.
  2: rewrite <- plus_n_O; pred_apply; cancel.
  omega.

  rewrite roundup_lt_one; auto.
  rewrite Nat.div_same; auto.
  rewrite H2; simpl; rewrite <- plus_n_O.
  destruct (skipn block_off (DFData f)) eqn:D.
  apply skipn_eq_nil in D.
  destruct D; try apply length_zero_iff_nil in H6; omega.

  simpl.
  rewrite firstn_oob.
  erewrite skipn_selN_skipn in D; inversion D.
  rewrite Nat.mod_small; auto.
  apply Nat.div_small_iff; auto.
  length_rewrite_l.
  length_rewrite_l.
  rewrite Nat.mod_small; auto.
  rewrite <- le_plus_minus; auto.
  apply Nat.lt_le_incl; apply Nat.div_small_iff; auto.
  apply Nat.div_small_iff; auto.
  apply Nat.div_small_iff in H2; auto.
  omega.
Qed.
Proof.
  intros.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); [eauto|eauto| |pred_apply; cancel].
  omega.
  unfold not; intros D.
  apply skipn_eq_nil in D.
  destruct D; try omega.
  apply length_zero_iff_nil in H4.
  omega.
Qed.
  Proof.
    intros.
    match goal with |[H: _ <= _ - _ |- _] => apply le_sub_le_add_l' in H end; auto.
    rewrite roundup_lt_one; auto.
    unfold tpad_length.
    inversion H4.
    rewrite H6 in *.
    rewrite Nat.mod_same; simpl; auto.
    rewrite skipn_oob.
    rewrite skipn_oob.
    rewrite app_nil_r.
    rewrite Nat.div_same.
    erewrite firstn_1_selN.
    rewrite skipn_selN; rewrite <- plus_n_O.
    simpl; rewrite firstn_oob with (n:= valubytes); eauto.
    length_rewrite_l.
    
    eapply skipn_not_nil'; eauto.
    auto.
    length_rewrite_l.
    length_rewrite_l.

    rewrite H5 in *.
    rewrite Nat.mod_small; auto; try omega.
    destruct (length head_data + length data) eqn:D; try omega.
    rewrite Nat.div_same.
    erewrite firstn_1_selN.
    rewrite skipn_selN; rewrite <- plus_n_O.
    replace (S n / valubytes) with 0. rewrite <- plus_n_O.
    simpl; rewrite firstn_oob with (n:= valubytes); eauto.
    length_rewrite_l.
    destruct (valu2list (fst (DFData f) ⟦ block_off ⟧)) eqn:D0.
    simpl; omega.
    rewrite Nat.add_assoc.
    rewrite D.
    length_rewrite_l.
    assert (A: length(valu2list (fst (selN (DFData f) block_off valuset0))) 
                = length (b :: l)).
    rewrite D0; auto.
    rewrite valu2list_len in A.
    simpl in A.
    rewrite <- le_plus_minus; omega.
    symmetry; apply Nat.div_small_iff; auto; omega.
    
    eapply skipn_not_nil'; eauto.
    auto.
    length_rewrite_l.
    length_rewrite_l.
Qed.
  Proof.
    intros.
    match goal with |[H: _ <= _ - _ |- _] => apply le_sub_le_add_l' in H end; auto.
    rewrite roundup_lt_one; auto.
    unfold tpad_length.
    inversion H4.
    rewrite H6 in *.
    rewrite Nat.mod_same; simpl; auto.
    rewrite skipn_oob.
    rewrite skipn_oob.
    rewrite app_nil_r.
    rewrite Nat.div_same.
    erewrite firstn_1_selN.
    rewrite skipn_selN; rewrite <- plus_n_O.
    simpl; rewrite firstn_oob with (n:= valubytes); eauto.
    length_rewrite_l.
    
    eapply skipn_not_nil'; eauto.
    auto.
    length_rewrite_l.
    length_rewrite_l.

    rewrite H5 in *.
    rewrite Nat.mod_small; auto; try omega.
    destruct (length head_data + length data) eqn:D; try omega.
    rewrite Nat.div_same.
    erewrite firstn_1_selN.
    rewrite skipn_selN; rewrite <- plus_n_O.
    replace (S n / valubytes) with 0. rewrite <- plus_n_O.
    simpl; rewrite firstn_oob with (n:= valubytes); eauto.
    length_rewrite_l.
    destruct (valu2list (fst (DFData f) ⟦ block_off ⟧)) eqn:D0.
    simpl; omega.
    rewrite Nat.add_assoc.
    rewrite D.
    length_rewrite_l.
    assert (A: length(valu2list (fst (selN (DFData f) block_off valuset0))) 
                = length (b :: l)).
    rewrite D0; auto.
    rewrite valu2list_len in A.
    simpl in A.
    rewrite <- le_plus_minus; omega.
    symmetry; apply Nat.div_small_iff; auto; omega.
    
    eapply skipn_not_nil'; eauto.
    auto.
    length_rewrite_l.
    length_rewrite_l.
Qed.
Proof.
  intros.
  repeat xcrash_rewrite.
  xform_norm; xform_normr; cancel.
- repeat (rewrite crash_xform_exists_comm; cancel).
  repeat (rewrite crash_xform_sep_star_dist;
  rewrite crash_xform_lift_empty).
  safecancel.
  instantiate (1:= 0).
  omega.
  simpl.
  instantiate(1:= nil); eauto.
  all: simpl; eauto.

- repeat (rewrite crash_xform_exists_comm; cancel).
  repeat (rewrite crash_xform_sep_star_dist;
  rewrite crash_xform_lift_empty).
  safecancel.
  instantiate (1:= length [x]).
  match goal with |[H: _ <= _ - _ |- _] => apply le_sub_le_add_l' in H end.
  rewrite roundup_lt_one; auto.
  rewrite Nat.div_same; auto.
  omega.
  length_rewrite_l.
  omega.
  
  match goal with |[H: _ <= _ - _ |- _] => apply le_sub_le_add_l' in H end.
    unfold tpad_length.
    inversion H4.
    rewrite H10 in *.
    rewrite Nat.mod_same; simpl; auto.
    rewrite skipn_oob.
    rewrite skipn_oob.
    rewrite app_nil_r.
    rewrite <- plus_n_O.
    rewrite firstn_oob with (n:= valubytes); eauto.
    rewrite firstn_oob with (n:= valubytes); eauto.
    simpl.
    destruct (map vsmerge (get_sublist (DFData f) block_off 1)) eqn:D.
    apply map_eq_nil in D; unfold get_sublist in D; 
    apply firstn_eq_nil in D.
    destruct D; [omega | ].
     apply skipn_eq_nil in H9.
     destruct H9.
     assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    omega.
    exfalso; eapply le_lt_false.
    apply H9. apply A.
    
    apply length_zero_iff_nil in H9.
       assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    omega.
    unfold datatype in A; rewrite H9 in A; inversion A.
    simpl in D.
    unfold get_sublist in D; erewrite firstn_1_selN in D.
    simpl in D.
    rewrite skipn_selN in D; rewrite <- plus_n_O in D.
    inversion D.
    instantiate(2:= [x]); simpl; eauto.
    
    eapply skipn_not_nil'; eauto.
    length_rewrite_l.
    length_rewrite_l.
    length_rewrite_l.
    length_rewrite_l.
    
    length_rewrite_l.
      unfold tpad_length.
    rewrite H9 in *.
    rewrite Nat.mod_small; auto; try omega.
    destruct (length head_data + length data) eqn:D; try omega.
    simpl; unfold get_sublist.
    erewrite firstn_1_selN.
    rewrite skipn_selN; rewrite <- plus_n_O.
    replace (S n / valubytes) with 0. repeat rewrite <- plus_n_O.
    simpl; rewrite firstn_oob with (n:= valubytes); eauto.
    simpl; rewrite firstn_oob with (n:= valubytes); eauto.
    length_rewrite_l.
    destruct (valu2list (fst (DFData f) ⟦ block_off ⟧)) eqn:D0.
    simpl; omega.
    rewrite Nat.add_assoc.
    rewrite D.
    length_rewrite_l.
    assert (A: length(valu2list (fst (selN (DFData f) block_off valuset0))) = length (b :: l0)).
    rewrite D0; auto.
    rewrite valu2list_len in A.
    simpl in A.
    rewrite <- le_plus_minus; omega.
    length_rewrite_l.
    destruct (valu2list (fst (DFData f) ⟦ block_off ⟧)) eqn:D0.
    apply length_zero_iff_nil in D0; rewrite valu2list_len in D0; rewrite valubytes_is in D0.
    simpl in *; omega.
    rewrite Nat.add_assoc.
    rewrite D.
    length_rewrite_l.
    assert (A: length(valu2list (fst (selN (DFData f) block_off valuset0))) = length (b :: l0)).
    rewrite D0; auto.
    rewrite valu2list_len in A.
    simpl in A.
    rewrite <- le_plus_minus; omega.
    symmetry; apply Nat.div_small_iff; auto; omega.
    unfold not; intros D1.
    apply skipn_eq_nil in D1.
    destruct D1.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    omega.
    omega.
    apply length_zero_iff_nil in H12.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    omega.
    omega.
    auto.
    length_rewrite_l.
    length_rewrite_l.
    2: eauto.

    match goal with |[H: _ <= _ - _ |- _] => apply le_sub_le_add_l' in H end.
    unfold tpad_length.
    inversion H4.
    rewrite H10 in *.
    rewrite Nat.mod_same; simpl; auto.
    rewrite skipn_oob.
    rewrite skipn_oob.
    rewrite app_nil_r.
    rewrite <- plus_n_O.
    rewrite firstn_oob with (n:= valubytes); eauto.
    rewrite firstn_oob with (n:= valubytes); eauto.
    simpl.
    destruct (map vsmerge (get_sublist (DFData f) block_off 1)) eqn:D.
    apply map_eq_nil in D; unfold get_sublist in D; 
    apply firstn_eq_nil in D.
    destruct D; [omega | ].
    apply skipn_eq_nil in H9.
    destruct H9.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    omega.
    exfalso; eapply le_lt_false.
    apply H9. apply A.
    
    apply length_zero_iff_nil in H9.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    omega.
    unfold datatype in A; rewrite H9 in A; inversion A.
    simpl in D.
    unfold get_sublist in D; erewrite firstn_1_selN in D.
    simpl in D.
    rewrite skipn_selN in D; rewrite <- plus_n_O in D.
    inversion D.
    simpl; eauto.
    
    eapply skipn_not_nil'; eauto.
    length_rewrite_l.
    length_rewrite_l.
    length_rewrite_l.
    length_rewrite_l.

    length_rewrite_l.
    unfold tpad_length.
    rewrite H9 in *.
    rewrite Nat.mod_small; auto; try omega.
    destruct (length head_data + length data) eqn:D; try omega.
    simpl; unfold get_sublist.
    erewrite firstn_1_selN.
    rewrite skipn_selN; rewrite <- plus_n_O.
    replace (S n / valubytes) with 0. repeat rewrite <- plus_n_O.
    simpl; rewrite firstn_oob with (n:= valubytes); eauto.
    simpl; rewrite firstn_oob with (n:= valubytes); eauto.
    length_rewrite_l.
    destruct (valu2list (fst (DFData f) ⟦ block_off ⟧)) eqn:D0.
    simpl; omega.
    rewrite Nat.add_assoc.
    rewrite D.
    length_rewrite_l.
    assert (A: length(valu2list (fst (selN (DFData f) block_off valuset0))) = length (b :: l0)).
    rewrite D0; auto.
    rewrite valu2list_len in A.
    simpl in A.
    rewrite <- le_plus_minus; omega.
    length_rewrite_l.
    destruct (valu2list (fst (DFData f) ⟦ block_off ⟧)) eqn:D0.
    apply length_zero_iff_nil in D0; rewrite valu2list_len in D0; rewrite valubytes_is in D0.
    simpl in *; omega.
    rewrite Nat.add_assoc.
    rewrite D.
    length_rewrite_l.
    assert (A: length(valu2list (fst (selN (DFData f) block_off valuset0))) = length (b :: l0)).
    rewrite D0; auto.
    rewrite valu2list_len in A.
    simpl in A.
    rewrite <- le_plus_minus; omega.
    symmetry; apply Nat.div_small_iff; auto; omega.
    unfold not; intros D1.
    apply skipn_eq_nil in D1.
    destruct D1.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    omega.
    omega.
    apply length_zero_iff_nil in H12.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    omega.
    omega.
    auto.
    length_rewrite_l.
    length_rewrite_l.
    auto.
Qed.
Proof.
  intros.
  rewrite dsupd_iter_dsupd_head.
  rewrite combine_cons.
  repeat rewrite <- map_cons.
  repeat rewrite firstn_length_l; try omega.
  rewrite cons_app with (a:= (selN (DFData f) block_off valuset0) ).
  replace ([(selN (DFData f) block_off valuset0)])
    with (firstn 1 (skipn block_off (DFData f))).
  replace (skipn (block_off + 1) (DFData f'))
    with (skipn 1 (skipn block_off (DFData f))).
  rewrite <- firstn_sum_split.
  replace (1 + roundup (length data -
               (valubytes - length head_data)) valubytes / valubytes)
    with (S (roundup (length data +
               length head_data - valubytes) valubytes / valubytes)).
  rewrite roundup_div_minus_S.
  rewrite list_split_chunk_cons'.
  repeat rewrite mm_dist'; try omega.
  rewrite roundup_div_minus_S.
  rewrite <- le_plus_minus; try omega.
  replace (skipn valubytes (valu2list (fst  (selN (DFData f) block_off valuset0))))
      with (nil: list byte).
  rewrite app_nil_r.
  rewrite <- app_assoc.
  rewrite app_assoc_middle_2'.
  rewrite firstn_skipn.
  rewrite mod_subt.
  erewrite dir2flatmem2_tsupd_updN with (f':=f'); eauto.
  rewrite selN_updN_ne.
  rewrite div_ge_subt; auto.
  rewrite <- Nat.add_assoc; rewrite <- le_plus_minus.
  unfold tpad_length.

  destruct ((length head_data + length data)
                mod valubytes) eqn:D.
  rewrite Nat.add_comm in D; rewrite D.
  repeat rewrite roundup_eq_mod_O; try omega.
  rewrite app_assoc; rewrite list_split_chunk_app_l.
  replace (skipn valubytes (valu2list (fst (selN (DFData f) (block_off +
                      (length head_data + length data) /
                      valubytes ) valuset0))))
      with (nil: list byte). rewrite app_nil_r.
  replace (length head_data + length data)
      with  (length data + length head_data) by omega; eauto.
  rewrite skipn_oob; auto.
  length_rewrite_l.
  length_rewrite_l.
  rewrite Nat.add_comm; rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
  rewrite Nat.add_comm; auto.
  
  rewrite <- D.
  replace (length head_data + length data)
      with  (length data + length head_data) by omega; eauto.
  apply Nat.div_str_pos; omega.
  unfold not; intros; omega.
  omega.
  rewrite skipn_oob; auto.
  length_rewrite_l.
  auto.
  omega.
  length_rewrite_l.
  auto.
  omega.
  rewrite mm_dist'; auto.
  omega.
  rewrite skipn_skipn'.
  erewrite dir2flatmem2_tsupd_updN with (f':=f'); eauto.
  simpl. 
  rewrite skipn_updN_oob_eq; auto; omega.
  erewrite firstn_1_selN; eauto.
  rewrite skipn_selN; rewrite <- plus_n_O; eauto.
  
  unfold not; intros D1.
  apply skipn_eq_nil in D1.
  destruct D1.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  apply length_zero_iff_nil in H8.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  length_rewrite_l.
Qed.
Proof.
  intros.
  rewrite <- Nat.add_assoc; rewrite <- le_plus_minus; try omega.
  length_rewrite_l.
  replace (block_off + 1) with (S block_off) by omega.
  rewrite tsupd_iter_tsupd_head.
    replace (S block_off) with (block_off + 1) by omega.
  unfold datatype; rewrite combine_cons.
  repeat rewrite <- map_cons.
  repeat rewrite firstn_length_l; try omega.
  rewrite cons_app with (a:= (selN (DFData f) block_off valuset0) ).
  replace ([(selN (DFData f) block_off valuset0)])
    with (firstn 1 (skipn block_off (DFData f))).
    
  fold datatype; replace (skipn (block_off + 1) (DFData f'))
    with (skipn 1 (skipn block_off (DFData f))).
  rewrite <- firstn_sum_split.
  replace (1 + roundup (length data -
               (valubytes - length head_data)) valubytes / valubytes)
    with (S (roundup (length data +
               length head_data - valubytes) valubytes / valubytes)).
  rewrite roundup_div_minus_S.
  rewrite list_split_chunk_cons'.
  repeat rewrite mm_dist'; try omega.
  rewrite roundup_div_minus_S.
  replace (skipn valubytes (valu2list (fst  (selN (DFData f) block_off valuset0))))
      with (nil: list byte).
  rewrite app_nil_r.
  rewrite <- app_assoc.
  rewrite app_assoc_middle_2'.
  rewrite firstn_skipn.
  rewrite mod_subt.
  erewrite dir2flatmem2_tsupd_updN with (f':=f'); eauto.
  rewrite selN_updN_ne.
  rewrite div_ge_subt; auto.
  replace (S ((length data + length head_data) / valubytes - 1))
     with ((length data + length head_data) / valubytes).
  unfold tpad_length.

  destruct ((length head_data + length data)
                mod valubytes) eqn:D.
  rewrite Nat.add_comm in D; rewrite D.
  repeat rewrite roundup_eq_mod_O; try omega.
  rewrite app_assoc; rewrite list_split_chunk_app_l.
  replace (skipn valubytes (valu2list (fst (selN (DFData f) (block_off +
                      (length head_data + length data) /
                      valubytes ) valuset0))))
      with (nil: list byte). rewrite app_nil_r.
  replace (length head_data + length data)
      with  (length data + length head_data) by omega; eauto.
  rewrite skipn_oob; auto.
  length_rewrite_l.
  length_rewrite_l.
  rewrite Nat.add_comm; rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
  rewrite Nat.add_comm; auto.
  
  rewrite <- D.
  replace (length head_data + length data)
      with  (length data + length head_data) by omega; eauto.
  assert ((length data + length head_data) / valubytes > 0).
  apply Nat.div_str_pos; omega.
  omega.
  unfold not; intros; omega.
  omega.
  rewrite skipn_oob; auto.
  length_rewrite_l.
  auto.
  omega.
  length_rewrite_l.
  auto.
  omega.
  rewrite mm_dist'; auto.
  omega.
  rewrite skipn_skipn'.
  erewrite dir2flatmem2_tsupd_updN with (f':=f'); eauto.
  simpl. 
  
  rewrite skipn_updN_oob_eq; auto; omega.
  erewrite firstn_1_selN; eauto.
  rewrite skipn_selN; rewrite <- plus_n_O; eauto.
  
  unfold not; intros D1.
  apply skipn_eq_nil in D1.
  destruct D1.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
  apply length_zero_iff_nil in H8.
  assert (A: block_off < length (DFData f)).
  eapply inlen_bfile with (j:= length head_data); eauto.
  2: pred_apply; cancel.
  omega.
  omega.
Qed.
Proof.
	unfold read_from_block, AByteFile.rep; step.

	- eapply addr_id; eauto.
	   eapply inlen_bfile; eauto.
	   solve_rep.
	   omega.

	- step.
	   assert (A: rep f fy).
	   solve_rep.
	   assert (A0: block_off < length (DFData f)).
	   eapply inlen_bfile with (j:= byte_off); eauto; omega.
	   erewrite f_pfy_selN_eq; eauto.
	   rewrite v2l_fst_bs2vs_map_fst_eq; auto.
	   eapply content_match; eauto; try omega.
    eapply proto_bytefile_nonnil; eauto.
    omega.
    proto_bytefile_rewrite.
	  erewrite selN_map with (default':= valuset0); auto.
	  length_rewrite_l.
Qed.
Proof.
  unfold read_middle_blocks; step.

  - step.
    rewrite <- plus_n_O.
    instantiate (1:= firstn valubytes (skipn (m * valubytes) data)).
    erewrite arrayN_split with (i:= m * valubytes).
    erewrite arrayN_split with (i:= valubytes)(a:=(skipn (m * valubytes) data)).
    rewrite Nat.mul_add_distr_r; cancel.
    length_rewrite_l.
    eapply length_le_middle; eauto.
    length_rewrite_l; auto.
    apply valubytes_ge_O.
    eapply length_le_middle; eauto. 

    step.
    apply map_app_firstn_skipn.

  - step.
    match goal with
    | [H: _ = num_of_full_blocks * valubytes |- _ ] => rewrite <- H
    end.
    rewrite firstn_exact; auto.
  
  - instantiate (1:= LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm).
    eapply LOG.idempred_hashmap_subset.
    exists l; auto.
    
  Grab Existential Variables.
  constructor.
Qed.
Proof.
	unfold read_last; step.

  - step.
	  rewrite <- plus_n_O; cancel.
    step.
    
 - step.
   match goal with
   | [H: _ < _ -> False |- _ ] => 
                apply Nat.nlt_ge in H; inversion H as [Hx | ];
                apply length_nil in Hx; rewrite Hx; auto
   end.
Qed.
Proof.
	unfold read_middle; step.
	
	- safestep.
	  5: instantiate (1:= firstn (length data / valubytes * valubytes) data).
	  eauto.
	  eauto.
	  eauto.
	  pred_apply.
    erewrite arrayN_split; cancel.
    length_rewrite_l.
    rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.

    step.
    + step.
        rewrite Nat.mul_add_distr_r.
	      rewrite arrayN_split with (i:= length data / valubytes * valubytes); cancel.
        length_rewrite_l.
        symmetry; rewrite Nat.mul_comm; apply Nat.mod_eq; auto.
        apply Nat.mod_upper_bound; auto.
	
	      step.
	      rewrite <- map_app.
	      rewrite firstn_skipn; auto.

	  + step.
        nlt_eq_0.
	      rewrite Rounding.mul_div; auto.
	      rewrite firstn_exact; auto.
	
	- step.
    rewrite_nlt; eauto.
	  rewrite Nat.mod_eq; auto.
	  rewrite_nlt; eauto.
	  rewrite <- mult_n_O.
	  apply minus_n_O.
    apply Nat.mod_upper_bound; auto.
    
    step.
Qed.
Proof.
  unfold read_first; step.
  
  - safestep.
    5: instantiate (1:= firstn (valubytes - byte_off) data).
    eauto.
    eauto.
    eauto.
    pred_apply; erewrite arrayN_split; cancel.
    length_rewrite_l.
    length_rewrite_l.
  
    step.
    instantiate (1:= skipn (valubytes - byte_off) data).
    rewrite Nat.add_comm with (n:= valubytes).
    rewrite arrayN_split with (i:= valubytes - byte_off).
    rewrite <- Nat.add_assoc; rewrite <- le_plus_minus; [cancel | omega].
    length_rewrite_l.
    
    step.
    rewrite <- map_app.
    rewrite firstn_skipn; auto.

  
  - step.
     step.
Qed.
Proof.   
  unfold read; step.
  - step.
    step.
    
    + step.
        rewrite Nat.mul_comm; rewrite <- Nat.div_mod; eauto.
        apply Nat.mod_upper_bound; auto.
        step.
      
    + step.
      exfalso; eapply bound_le_exfalso; eauto.

  - step.
    match goal with
   | [H: _ < _ -> False |- _ ] => 
                apply Nat.nlt_ge in H; inversion H as [Hx | ];
                apply length_nil in Hx; rewrite Hx; auto
   end.
Qed.
Proof.
  unfold dwrite_to_block; step.

  remember (length head_data) as byte_off.
  apply addr_id.
  eapply inlen_bfile with (j:= byte_off); eauto.
  omega.
  instantiate (1:= old_data);
  omega.
  pred_apply; cancel.

  - step.
    remember (length head_data) as byte_off.
    apply addr_id.
    eapply inlen_bfile with (j:= byte_off); eauto.
    omega.
    instantiate (1:= old_data); omega.
    pred_apply; cancel.

    + unfold rep in *; split_hypothesis;
        safestep.
        eauto.
        eauto.
        eauto.
        eauto.
        eapply rep_modified_exists; eauto.

        eapply sep_star_modified_bytefile; eauto.
        match goal with | [H: (((_ ✶ _) ✶ _) ✶ _)%pred _ |- _] => apply arrayN_app_merge in H end.
        pred_apply; cancel.
        auto.
        match goal with | [H: _ = MSAlloc ?a |- context[MSAlloc ?a] ] => rewrite <- H end.
        match goal with | [H: forall _, _ -> treeseq_pred _ _ |- _ ] => apply H end.
        match goal with | [H: MSAlloc ?a = _ |- context[MSAlloc ?a] ] => rewrite H; auto end.

    + xcrash.
      or_r.
         match goal with | [H: (_, _) = _, H0: treeseq_in_ds _ _ _ _ _ (_, _) _ |- _ ] => 
          rewrite H in H0 end;
    match goal with | [H: MSAlloc ?a = _, H0: _ = MSAlloc ?a |- _ ] => 
          rewrite H in H0; clear H end;
    cancel;
    do 2 (rewrite crash_xform_exists_comm; cancel);
    rewrite crash_xform_exists_comm; unfold pimpl; intros.
    exists x0.
    apply crash_xform_exists_comm.
    eexists.
    pred_apply.
    repeat (rewrite crash_xform_sep_star_dist;
       rewrite crash_xform_lift_empty).
    safecancel;
    eauto.
    

  - xcrash.
Qed.
Proof.
    unfold dwrite_middle_blocks; safestep.
    3: instantiate (1:= nil).
    3: instantiate (1:= ds).
    9: rewrite <- plus_n_O.
    (* step or all: eauto takes forever to finish *)
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    pred_apply; cancel.
    eauto.
    eauto.
    eauto.

    (* step initializes wrongly *)
    - safestep.
      eauto.
      eauto.
      eauto.
      eauto.
      pred_apply.
      rewrite <- plus_n_O. 
      rewrite arrayN_split with (i:= valubytes)
      (a:= (skipn (length bnl * valubytes) old_data)) at 1.
      instantiate (1:= nil).
      instantiate (3:= nil).
      simpl; cancel.
      solve_ineq_dwrite_middle.
      solve_ineq_dwrite_middle.
      solve_ineq_dwrite_middle.
      auto.

      rewrite get_sublist_length at 2; auto;[| solve_ineq_dwrite_middle].
      replace (valubytes - valubytes) with 0 by omega.
      rewrite Nat.min_0_r; auto.

      + step.
          solve_dsupd_iter.
          solve_tsupd_iter.
          length_rewrite_l.
          solve_cancel_dwrite_middle block_off bnl.
          
          + subst; repeat xcrash_rewrite;
              xform_norm; cancel; xform_normr.
              * unfold pimpl; intros;
                 repeat apply sep_star_lift_apply'; 
                 [eauto | apply Nat.lt_le_incl; eauto | | | | | ].
                 all: eauto.
             * unfold pimpl; intros.
                repeat apply sep_star_lift_apply'.
                5: eauto.
                all: eauto.
                solve_dsupd_iter.
                solve_tsupd_iter.
                length_rewrite_l.

      - step;
        [rewrite <- H5;
        rewrite firstn_exact;
        rewrite <- H6;
        rewrite firstn_exact;
        rewrite skipn_exact;
        simpl; cancel
        | rewrite <- H5; rewrite firstn_exact; auto
        | rewrite <- H5; rewrite firstn_exact; auto].

    - instantiate (1:= LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) _ hm).
        unfold pimpl; intros m' Hy.
        apply sep_star_lift_apply in Hy as Hx.
        destruct Hx as [Hz  Hx0].
        clear Hz; pred_apply.
        split_hypothesis.

        subst; repeat xcrash_rewrite;
                   xform_norm; cancel; xform_normr.

        rewrite LOG.idempred_hashmap_subset; [| eauto].
        safecancel.
        4: eauto.
        instantiate (1:= 0); omega.
        instantiate (1:= nil).
        simpl; auto.
        simpl; auto.
        all: eauto.

        Unshelve.
        constructor.
 Qed.
Proof.
  unfold dwrite_last; step.

  prestep; norm.
  unfold stars; cancel.
  rewrite <- plus_n_O.
  intuition; eauto.
  instantiate (1:= nil); simpl; pred_apply; 
  match goal with | [H: _ = _ |- _ ] => rewrite H end; cancel.
  auto.
  step.
  step.
  Unshelve.
  all: repeat try constructor.
Qed.
Proof.
  unfold dwrite_middle; step.
  match goal with | [H: (_ * _ *_)%pred _ |- _] => 
    rewrite arrayN_split with (i:= length data / valubytes * valubytes) in H end.
  step.
  
  - repeat rewrite firstn_length_l; try omega.
    rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
    match goal with | [H: length _ = length _ |- _ ] => rewrite H end; 
    rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
  - apply firstn_length_l; rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
  
  - match goal with | [H: ((_ * (_ *_)) * _)%pred _ |- _] => 
      rewrite <- Nat.mul_add_distr_r in H end.
    step.
    
    step.
    repeat rewrite Nat.mul_add_distr_r; cancel.
    rewrite skipn_length; rewrite <- Nat.add_assoc; rewrite <- le_plus_minus.
    cancel.

    solve_length_le.
    length_rewrite_l.
    solve_length_le_v.
    solve_min_dwrite_middle fy fy' data.

    safestep.
    apply H32.
  
    solve_cancel_dwrite_middle2.
    repeat match goal with | [H: ?a = _ |- context[?a] ] => rewrite H; auto end.
    all: eauto.
    simpl_skipn_lt.
    instantiate(1:= (bnl++[bn])%list); 
    rewrite roundup_div_S_eq; auto; length_rewrite_l.
    eapply dsupd_dsupd_iter_dwrite_middle; eauto.
    
    assert (A: block_off + length data / valubytes <= length (DFData f)).
    apply Nat.lt_le_incl; eapply inlen_bfile with (j:= 0); eauto.
    apply valubytes_ge_O.
    2: rewrite <- plus_n_O; pred_apply; cancel.
    length_rewrite_l.
    match goal with | [H: 0 < length (skipn _ _) |- _] => 
      rewrite skipn_length in H end; omega.

    erewrite <- bfile_selN_tsupd_iter_eq with (f:= f)(f':= f'); eauto; [ |
    unfold datatype; solve_eq_dwrite_middle]. 
    eapply tsupd_tsupd_iter_merge'; eauto.
    match goal with | [H: MSAlloc ?a = _ |- context[MSAlloc ?a] ] => rewrite H; auto end.
   
   repeat xcrash_rewrite.
   xform_norm; xform_normr; cancel.
   repeat (rewrite crash_xform_exists_comm; cancel).
   repeat (rewrite crash_xform_sep_star_dist;
   rewrite crash_xform_lift_empty).
   safecancel.
   instantiate (1:= length data / valubytes).
   rewrite roundup_div_S_eq; auto.
   simpl_skipn_lt; auto.

   rewrite firstn_app_l; eauto; solve_length_le.
   rewrite firstn_app_l; eauto; solve_length_le.
   all: eauto.
   
   repeat (rewrite crash_xform_exists_comm; cancel).
   repeat (rewrite crash_xform_sep_star_dist;
   rewrite crash_xform_lift_empty).
    + safecancel.
      4: eauto.
      2: eapply dsupd_dsupd_iter_dwrite_middle2; eauto.
      simpl_skipn_lt; rewrite roundup_div_S_eq; auto.
      eapply tsupd_tsupd_iter_dwrite_middle2; eauto.
      length_rewrite_l.
      rewrite H16; auto.
      
      
    + step.
      simpl_skipn_zero.
      simpl_min_zero.
      rewrite H5; simpl.
      rewrite mul_div; auto.
      rewrite firstn_exact.
      rewrite <- H7.
      rewrite skipn_exact; rewrite firstn_exact; cancel.
      
      instantiate (1:= bnl).
      simpl_skipn_zero.
      rewrite roundup_eq_mod_O; auto.
      
        simpl_skipn_zero.
       rewrite roundup_eq_mod_O; auto.
       rewrite H10; simpl.
        rewrite list_split_chunk_app_l.
        rewrite mul_div; auto.
        rewrite firstn_exact; auto.
        rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
        
        simpl_skipn_zero.
      rewrite roundup_eq_mod_O; auto.
      rewrite list_split_chunk_app_l.
      rewrite mul_div; auto.
      rewrite firstn_exact.
      unfold get_sublist; auto.
      rewrite mul_div; auto.
  
  
  - repeat xcrash_rewrite.
     xform_norm; xform_normr; cancel.
     repeat (rewrite crash_xform_exists_comm; cancel).
     repeat (rewrite crash_xform_sep_star_dist;
     rewrite crash_xform_lift_empty).
     safecancel.
   
     + instantiate (1:= length x4).
       eapply le_trans.
       apply H21.
       apply Nat.div_le_mono; auto.
       apply roundup_ge; auto.
        
    + rewrite firstn_firstn; rewrite min_l.
      rewrite firstn_app_l; auto.
      eapply le_trans.
      2: eapply Nat.mul_div_le with (b:= valubytes); auto.
      rewrite Nat.mul_comm; apply mult_le_compat_l; auto.
      apply mult_le_compat_r; auto.
   
   + eauto.
   + rewrite firstn_app_l.
       rewrite firstn_firstn; rewrite min_l; auto.
       repeat (rewrite firstn_firstn in H18; rewrite min_l in H18); eauto.
       apply mult_le_compat_r; auto.
       apply mult_le_compat_r; auto.
       eapply le_trans.
       2: eapply Nat.mul_div_le with (b:= valubytes); auto.
       rewrite Nat.mul_comm; apply mult_le_compat_l; auto.
  + eauto.
  + eauto.
  
  - step.
    nlt_eq_0.
    apply Nat.div_small_iff; auto.

    nlt_eq_0.
    unfold hpad_length in H5.
    destruct (length data mod valubytes) eqn:D.
    apply Nat.div_small_iff in Hx; auto.
    apply mod_lt_nonzero in Hx; auto; try omega.
    rewrite <- D in *; auto.
    apply Nat.div_small_iff in Hx; auto.
    apply Nat.mod_small_iff in Hx. rewrite Hx in H5; auto.
    auto.

    + nlt_eq_0.
      step.
      instantiate (1:= [bn]).
      rewrite roundup_lt_one; auto.
      rewrite Nat.div_same; auto.
      apply Nat.div_small_iff in Hx; auto.
      omega.
      rewrite Hx; simpl; rewrite <- plus_n_O.
      eapply dsupd_eq_dwrite_middle; eauto.
      eapply tsupd_eq_dwrite_middle; eauto.

    + repeat xcrash_rewrite.
       xform_norm; xform_normr; cancel.
       repeat (rewrite crash_xform_exists_comm; cancel).
       repeat (rewrite crash_xform_sep_star_dist;
       rewrite crash_xform_lift_empty).
       * safecancel.
          instantiate (1:= 0).
          omega.
          simpl.
          instantiate(1:= nil); eauto.
          all: simpl; eauto.
       * nlt_eq_0.
          assert (A: block_off < length (DFData f)).
          eapply inlen_bfile with (j:= 0); eauto.
          apply valubytes_ge_O.
          2: rewrite <- plus_n_O; pred_apply; cancel.
          omega.
          repeat (rewrite crash_xform_exists_comm; cancel).
          repeat (rewrite crash_xform_sep_star_dist;
          rewrite crash_xform_lift_empty).
          safecancel.
          instantiate (1:= length [x]).
          rewrite roundup_lt_one; auto.
          rewrite Nat.div_same; auto.
          apply Nat.div_small_iff in Hx; auto.
          omega.
  
          simpl; rewrite Hx; simpl; rewrite <- plus_n_O.
          destruct (map vsmerge (get_sublist (DFData f) block_off 1)) eqn:D.
          apply map_eq_nil in D; unfold get_sublist in D; 
          apply firstn_eq_nil in D.
          destruct D; [omega | ].
          apply skipn_eq_nil in H10.
          destruct H10.
          exfalso; eapply le_lt_false.
          apply H10. apply A.
  
          apply length_zero_iff_nil in H10.
          unfold datatype in A; rewrite H10 in A; inversion A.
          simpl in D.
          unfold get_sublist in D; erewrite firstn_1_selN in D.
          simpl in D.
          rewrite skipn_selN in D; rewrite <- plus_n_O in D.
          inversion D.
          rewrite firstn_firstn; rewrite Nat.min_id.
          rewrite <- plus_n_O; rewrite firstn_oob.
          rewrite Nat.mod_small; auto.
          instantiate(2:= [x]); simpl; eauto.
    
          apply Nat.div_small_iff; auto.
          length_rewrite_l.
          rewrite Nat.mod_small; auto.
          rewrite <- le_plus_minus; auto.
          apply Nat.lt_le_incl; apply Nat.div_small_iff; auto.
          apply Nat.div_small_iff; auto.

          unfold not; intros H10.
          apply skipn_eq_nil in H10.
          destruct H10.
          exfalso; eapply le_lt_false.
          apply H10. apply A.
          apply length_zero_iff_nil in H10.
          rewrite H10 in A; inversion A.
    
          2: eauto.
          simpl; rewrite <- plus_n_O.
          destruct (map vsmerge (get_sublist (DFData f) block_off 1)) eqn:D.
          apply map_eq_nil in D; unfold get_sublist in D; 
          apply firstn_eq_nil in D.
          destruct D; [omega | ].
          apply skipn_eq_nil in H10.
          destruct H10.
          exfalso; eapply le_lt_false.
          apply H10. apply A.
    
          apply length_zero_iff_nil in H10.
          unfold datatype in A; rewrite H10 in A; inversion A.
          simpl in D.
          unfold get_sublist in D; erewrite firstn_1_selN in D.
          simpl in D.
          rewrite skipn_selN in D; rewrite <- plus_n_O in D.
          inversion D.
          rewrite firstn_firstn; rewrite Nat.min_id.
          rewrite firstn_oob.
          rewrite Nat.mod_small; auto.
          rewrite Hx; rewrite <- plus_n_O; simpl; auto.
    
          apply Nat.div_small_iff; auto.
          length_rewrite_l.
          rewrite Nat.mod_small; auto.
          rewrite <- le_plus_minus; auto.
          apply Nat.lt_le_incl; apply Nat.div_small_iff; auto.
          apply Nat.div_small_iff; auto.
    
          unfold not; intros H10.
          apply skipn_eq_nil in H10.
          destruct H10.
          exfalso; eapply le_lt_false.
          apply H10. apply A.
          apply length_zero_iff_nil in H10.
          rewrite H10 in A; inversion A.
  
  all: auto.
  
  Unshelve.
  all: repeat constructor.
Qed.
Proof.
  unfold dwrite_first; step.
  - unfold hpad_length in *.
    step.
    rewrite H9; cancel.
    eauto.
    match goal with |[H: _ <= _ - _ |- _] => apply le_sub_le_add_l' in H end.
    destruct (Nat.eq_dec (length head_data + length data) valubytes).
    rewrite e in *; rewrite Nat.mod_same in H5; auto.
    replace (valubytes - valubytes) with 0 by omega; simpl in *; auto.
    inversion H18; try omega.
    assert (A: length head_data + length data < valubytes).
    omega.
    apply Nat.mod_small_iff in A; auto; try omega.
    destruct (length head_data + length data) eqn:D.
    apply plus_is_O in D; destruct D; omega.
    rewrite H in *.
    rewrite A in H5; auto.
    auto.
  
    step.
    instantiate (1:= [bn]).
    match goal with |[H: _ <= _ - _ |- _] => apply le_sub_le_add_l' in H end; auto.
    length_rewrite_l.
    rewrite roundup_lt_one; auto; try omega.
    rewrite Nat.div_same; auto.
    eapply dsupd_dsupd_iter_eq_dwrite_first; eauto.
    eapply tsupd_tsupd_iter_eq_dwrite_first; eauto.
    
    eapply crash_dwrite_first1; eauto.

  - safestep.
    eauto.
    eauto.
    eauto.
    eauto.
    
    erewrite arrayN_split with (a:= old_data)(i := valubytes - length head_data) in H10.
    pred_apply.
    instantiate (1:= nil).
    simpl;
    rewrite <- Nat.add_assoc; rewrite <- le_plus_minus; try omega.
    cancel.
    all: try solve [length_rewrite_l].
    length_rewrite_l.
    rewrite <- le_plus_minus; try omega.
    replace (valubytes - valubytes) with 0 by omega.
    apply Nat.min_0_r.
    
    safestep.
    2: eauto.
    4: apply H24.
    3: eauto.
    apply tree_names_distinct_tsupd; eauto.
    rewrite H20; auto.
    pred_apply.
    replace (block_off * valubytes + valubytes) with ((block_off + 1) * valubytes) 
        by (rewrite Nat.mul_add_distr_r; simpl; omega).
    cancel.
    length_rewrite_l. 
    rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
    rewrite Nat.add_sub_assoc.
    rewrite Nat.add_sub_swap.
    rewrite <- Nat.add_sub_assoc.
    rewrite sub_sub_assoc; auto.
    rewrite H9; cancel.
    
    all: length_rewrite_l.
    apply le_trans with (m:= valubytes); length_rewrite_l.
    apply le_plus_r.
    
    apply Nat.nle_gt in H18.
    apply Nat.lt_sub_lt_add_l in H18.
    rewrite mm_dist'; try omega.
    unfold hpad_length in *.
    rewrite mod_subt; auto; try omega.
    rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
    rewrite <- Nat.add_assoc; rewrite <- le_plus_minus; try omega. 
    erewrite <- bytefile_length_eq with (fy:= fy); eauto.
    replace (block_off * valubytes +
      (length data + length head_data))
      with (block_off * valubytes + length head_data +
           length data) by omega; auto.
    replace (length data + length head_data)
        with (length head_data + length data) by omega; auto.
    
    step.
    + rewrite Nat.mul_add_distr_r; simpl; rewrite <- plus_n_O.
    rewrite mm_dist'; try omega.
    rewrite <- Nat.add_assoc; rewrite <- le_plus_minus; try omega.
    rewrite <- merge_bs_firstn_comm.
    rewrite <- merge_bs_skipn_comm.
    replace (block_off * valubytes + valubytes)
      with (block_off * valubytes + length head_data +
                (valubytes - length head_data)).
    rewrite <- arrayN_split.
    replace (length data + length head_data)
        with (length head_data + length data) by omega.
    rewrite Nat.add_assoc; cancel.
    rewrite <- Nat.add_assoc; rewrite <- le_plus_minus; try omega.
    
    + instantiate (1:= bn::bnl).
    length_rewrite_l.
    simpl; rewrite H33.
    rewrite mm_dist'; try omega.
    rewrite Nat.add_comm; apply roundup_div_minus_S; auto; omega.
    
    + eapply dsupd_iter_dsupd_dwrite_first; eauto.
    
    + eapply tsupd_iter_tsupd_dwrite_first; eauto.
    
    + repeat xcrash_rewrite.
    xform_norm; xform_normr; cancel.
    repeat (rewrite crash_xform_exists_comm; cancel).
    repeat (rewrite crash_xform_sep_star_dist;
    rewrite crash_xform_lift_empty).
    safecancel.
    4: eauto.
    
    length_rewrite_l.
    rewrite skipn_length in H27.
    instantiate (1:= length (bn::x4)).
    rewrite mm_dist' in H27; try omega.
    simpl.
    rewrite roundup_div_minus in H27; auto; try omega.
    rewrite Nat.add_comm; simpl.
    destruct (length x4).
    apply Nat.div_str_pos; auto.
    split; auto.
    apply valubytes_ge_O.
    apply le_trans with (m:= length data + length head_data).
    omega.
    apply roundup_ge; auto.
    apply le_sub_le_add_r' in H27.
    omega.
    omega.
    
    rewrite skipn_length in H27.
    rewrite mm_dist' in H27; try omega.
    rewrite roundup_div_minus in H27; auto; try omega.
    rewrite firstn_length_l.
    rewrite skipn_length.
    rewrite mm_dist'; try omega.
    rewrite dsupd_iter_dsupd_head.
    rewrite combine_cons.
    repeat rewrite <- map_cons.
    repeat rewrite firstn_length_l; try omega.
    unfold get_sublist.
    rewrite cons_app with (a:= (selN (DFData f) block_off valuset0) ).
    replace ([(selN (DFData f) block_off valuset0)])
      with (firstn 1 (skipn block_off (DFData f))).
    replace (skipn (block_off + 1) (DFData f'))
      with (skipn 1 (skipn block_off (DFData f))).
    rewrite <- firstn_sum_split.
    rewrite <- Nat.add_assoc.
    rewrite list_split_chunk_cons'.
    repeat rewrite mm_dist'; try omega.
    rewrite <- le_plus_minus; try omega.
    replace (skipn valubytes (valu2list (fst  (selN (DFData f) block_off valuset0))))
        with (nil: list byte).
    rewrite app_nil_r.
    rewrite <- app_assoc.
    replace (firstn (length head_data)
                (valu2list (fst (DFData f) ⟦ block_off ⟧)) ++
              firstn (valubytes - length head_data) data ++
              firstn (length x4 * valubytes)
                (skipn (valubytes - length head_data) data ++
                 skipn
                   ((length data + length head_data -
                     valubytes) mod valubytes)
                   (valu2list
                      (fst
                         (DFData f')
                         ⟦ block_off +
                           (1 +
                            (length data + length head_data -
                             valubytes) / valubytes) ⟧))))%list
     with (firstn (length (bn::x4) * valubytes) 
              (firstn (length head_data)
                (valu2list (fst (selN (DFData f) block_off valuset0))) ++
              firstn (valubytes - length head_data) data ++
              skipn (valubytes - length head_data) data ++
                 skipn
                   ((length data + length head_data -
                     valubytes) mod valubytes)
                   (valu2list
                      (fst
                         (selN (DFData f')
                         (block_off +
                           (1 +
                            (length data + length head_data -
                             valubytes) / valubytes)) valuset0))))).
    rewrite app_assoc_middle_2'.
    rewrite firstn_skipn.
    rewrite mod_subt.
    erewrite dir2flatmem2_tsupd_updN with (f':=f'); eauto.
    rewrite selN_updN_ne.
    rewrite div_ge_subt; auto.
    unfold tpad_length.
    
    rewrite list_split_chunk_firstn_cancel.
    replace (S (length x4)) with (length (bn :: x4)) by auto.
    rewrite list_split_chunk_firstn_cancel.
      destruct ((length head_data + length data)
                  mod valubytes) eqn:D.
    rewrite Nat.add_comm in D; rewrite D.
    repeat rewrite roundup_eq_mod_O; try omega.
    rewrite app_assoc; rewrite list_split_chunk_app_l.
    replace (skipn valubytes (valu2list (fst (selN (DFData f) (block_off +
                        (length head_data + length data) /
                        valubytes ) valuset0))))
        with (nil: list byte). rewrite app_nil_r.
    replace (length head_data + length data)
        with  (length data + length head_data) by omega; eauto.
    rewrite skipn_oob; auto.
    length_rewrite_l.
    length_rewrite_l.
    rewrite roundup_eq_mod_O in H27; auto.
    destruct (length x4). simpl in *; try omega.
    apply le_sub_le_add_r' in H27; try omega.
    replace (valubytes + S n * valubytes) with
    ((S n + 1) * valubytes) by (rewrite Nat.mul_add_distr_r; simpl; omega).
    apply mult_le_compat_r with (p:= valubytes) in H27; auto.
    eapply le_trans.
    apply H27.
    rewrite Nat.add_comm; rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
    
    rewrite <- D.
    replace (length head_data + length data)
        with  (length data + length head_data) by omega; eauto.
    rewrite <- le_plus_minus; try omega; eauto.
    apply Nat.div_str_pos; omega.
    unfold not; intros; omega.
    omega.
    rewrite app_assoc.
    rewrite firstn_app_le; simpl.
    length_rewrite_l.
    repeat rewrite <- le_plus_minus; eauto.
    rewrite pm_1_3_cancel; rewrite app_assoc_reverse; eauto.
    omega.
    length_rewrite_l. 
    rewrite <- le_plus_minus; try omega.
    apply Nat.le_add_r.
    rewrite skipn_oob; auto.
    length_rewrite_l.
    length_rewrite_l.
    rewrite skipn_skipn'.
    erewrite dir2flatmem2_tsupd_updN with (f':= f'); eauto.
    rewrite skipn_updN_oob_eq; auto.
    length_rewrite_l.
    erewrite firstn_1_selN; eauto.
    rewrite skipn_selN; rewrite <- plus_n_O; eauto.
    
    unfold not; intros D1.
    apply skipn_eq_nil in D1.
    destruct D1.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    omega.
    omega.
    apply length_zero_iff_nil in H0.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    omega.
    omega.
    length_rewrite_l.
    
    rewrite skipn_length in H27.
    rewrite mm_dist' in H27; try omega.
    rewrite roundup_div_minus in H27; auto; try omega.
    rewrite firstn_length_l.
    rewrite skipn_length.
    rewrite mm_dist'; try omega.
    replace (block_off + 1) with (S block_off) by omega.
    rewrite tsupd_iter_tsupd_head.
    replace (S block_off) with (block_off + 1) by omega.
    unfold datatype; rewrite combine_cons.
    repeat rewrite <- map_cons.
    repeat rewrite firstn_length_l; try omega.
    unfold get_sublist.
    rewrite cons_app with (a:= (selN (DFData f) block_off valuset0) ).
    replace ([(selN (DFData f) block_off valuset0)])
      with (firstn 1 (skipn block_off (DFData f))).
    fold datatype;
    replace (skipn (block_off + 1) (DFData f'))
      with (skipn 1 (skipn block_off (DFData f))).
    rewrite <- firstn_sum_split.
    rewrite <- Nat.add_assoc.
    rewrite list_split_chunk_cons'.
    repeat rewrite mm_dist'; try omega.
    rewrite <- le_plus_minus; try omega.
    replace (skipn valubytes (valu2list (fst  (selN (DFData f) block_off valuset0))))
        with (nil: list byte).
    rewrite app_nil_r.
    rewrite <- app_assoc.
    replace (firstn (length head_data)
                (valu2list (fst (DFData f) ⟦ block_off ⟧)) ++
              firstn (valubytes - length head_data) data ++
              firstn (length x4 * valubytes)
                (skipn (valubytes - length head_data) data ++
                 skipn
                   ((length data + length head_data -
                     valubytes) mod valubytes)
                   (valu2list
                      (fst
                         (DFData f')
                         ⟦ block_off +
                           (1 +
                            (length data + length head_data -
                             valubytes) / valubytes) ⟧))))%list
     with (firstn (length (bn::x4) * valubytes) 
              (firstn (length head_data)
                (valu2list (fst (selN (DFData f) block_off valuset0))) ++
              firstn (valubytes - length head_data) data ++
              skipn (valubytes - length head_data) data ++
                 skipn
                   ((length data + length head_data -
                     valubytes) mod valubytes)
                   (valu2list
                      (fst
                         (selN (DFData f')
                         (block_off +
                           (1 +
                            (length data + length head_data -
                             valubytes) / valubytes)) valuset0))))).
    rewrite app_assoc_middle_2'.
    rewrite firstn_skipn.
    rewrite mod_subt.
    erewrite dir2flatmem2_tsupd_updN with (f':=f'); eauto.
    rewrite selN_updN_ne.
    rewrite div_ge_subt; auto.
    unfold tpad_length.
    
    rewrite list_split_chunk_firstn_cancel.
    replace (S (length x4)) with (length (bn :: x4)) by auto.
    rewrite list_split_chunk_firstn_cancel.
      destruct ((length head_data + length data)
                  mod valubytes) eqn:D.
    rewrite Nat.add_comm in D; rewrite D.
    repeat rewrite roundup_eq_mod_O; try omega.
    rewrite app_assoc; rewrite list_split_chunk_app_l.
    replace (skipn valubytes (valu2list (fst (selN (DFData f) (block_off +
                        (length head_data + length data) /
                        valubytes ) valuset0))))
        with (nil: list byte). rewrite app_nil_r.
    replace (length head_data + length data)
        with  (length data + length head_data) by omega; eauto.
    rewrite skipn_oob; auto.
    length_rewrite_l.
    length_rewrite_l.
    rewrite roundup_eq_mod_O in H27; auto.
    destruct (length x4). simpl in *; try omega.
    apply le_sub_le_add_r' in H27; try omega.
    replace (valubytes + S n * valubytes) with
    ((S n + 1) * valubytes) by (rewrite Nat.mul_add_distr_r; simpl; omega).
    apply mult_le_compat_r with (p:= valubytes) in H27; auto.
    eapply le_trans.
    apply H27.
    rewrite Nat.add_comm; rewrite Nat.mul_comm; apply Nat.mul_div_le; auto.
    
    rewrite <- D.
    replace (length head_data + length data)
        with  (length data + length head_data) by omega; eauto.
    rewrite <- le_plus_minus; try omega; eauto.
    apply Nat.div_str_pos; omega.
    unfold not; intros; omega.
    omega.
    rewrite app_assoc.
    rewrite firstn_app_le; simpl.
    length_rewrite_l.
    repeat rewrite <- le_plus_minus; eauto.
    rewrite pm_1_3_cancel; rewrite app_assoc_reverse; eauto.
    omega.
    length_rewrite_l. 
    rewrite <- le_plus_minus; try omega.
    apply Nat.le_add_r.
    rewrite skipn_oob; auto.
    length_rewrite_l.
    length_rewrite_l.
    rewrite skipn_skipn'.
    erewrite dir2flatmem2_tsupd_updN with (f':= f'); eauto.
    rewrite skipn_updN_oob_eq; auto.
    length_rewrite_l.
    erewrite firstn_1_selN; eauto.
    rewrite skipn_selN; rewrite <- plus_n_O; eauto.
    
    unfold not; intros D1.
    apply skipn_eq_nil in D1.
    destruct D1.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    omega.
    omega.
    apply length_zero_iff_nil in H0.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    omega.
    omega.
    length_rewrite_l.
    
    auto.
    rewrite H12; auto.
    
    + repeat xcrash_rewrite.
    xform_norm; xform_normr; cancel.
    repeat (rewrite crash_xform_exists_comm; cancel).
    repeat (rewrite crash_xform_sep_star_dist;
    rewrite crash_xform_lift_empty).
    safecancel.
    4: eauto.

    instantiate (1:= 0).
    omega.

    instantiate (1:= []).
    auto.
    simpl; auto.
    auto.
    auto.

    xform_norm; xform_normr; cancel.
    repeat (rewrite crash_xform_exists_comm; cancel).
    repeat (rewrite crash_xform_sep_star_dist;
    rewrite crash_xform_lift_empty).
    safecancel.
    4: eauto.

    instantiate (1:= 1).
    length_rewrite_l.
    eapply le_trans.
    instantiate (1:= (length head_data + length data) / valubytes).
    apply Nat.div_str_pos; auto.
    split; auto.
    apply valubytes_ge_O.
    omega.
    apply Nat.div_le_mono; auto.
    apply roundup_ge; auto.
    simpl.
    
    unfold get_sublist.
    rewrite firstn_length_l.
    rewrite <- le_plus_minus; try omega.
    instantiate (1:= [x]).
    erewrite firstn_1_selN. 
    simpl.
    rewrite skipn_selN.
    repeat rewrite <- plus_n_O.
    rewrite firstn_firstn.
    rewrite Nat.min_id.
    unfold tpad_length.
    rewrite skipn_oob.
    repeat rewrite app_nil_r.
    rewrite firstn_app_le.
    rewrite firstn_app_l.
    rewrite firstn_length_l; auto.
    
    length_rewrite_l.
    length_rewrite_l.
    length_rewrite_l.
    length_rewrite_l.
    
      unfold not; intros D1.
    apply skipn_eq_nil in D1.
    destruct D1.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    omega.
    omega.
    apply length_zero_iff_nil in H.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    omega.
    omega.
    length_rewrite_l.

    unfold get_sublist.
    rewrite firstn_length_l.
    rewrite <- le_plus_minus; try omega.
    erewrite firstn_1_selN. 
    simpl.
    rewrite skipn_selN.
    repeat rewrite <- plus_n_O.
    rewrite firstn_firstn.
    rewrite Nat.min_id.
    unfold tpad_length.
    rewrite skipn_oob.
    repeat rewrite app_nil_r.
    rewrite firstn_app_le.
    rewrite firstn_app_l.
    rewrite firstn_length_l; auto.
    
    length_rewrite_l.
    length_rewrite_l.
    length_rewrite_l.
    length_rewrite_l.
    
      unfold not; intros D1.
    apply skipn_eq_nil in D1.
    destruct D1.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    omega.
    omega.
    apply length_zero_iff_nil in H.
    assert (A: block_off < length (DFData f)).
    eapply inlen_bfile with (j:= length head_data); eauto.
    2: pred_apply; cancel.
    omega.
    omega.
    length_rewrite_l.
    all: auto.
Qed.
  Proof.
    unfold dwrite; step.
    step.
    step.
    step.
    Unshelve.
    all: repeat constructor.
  Qed.
Proof.
  unfold copydata, tree_with_tmp; step. 
  instantiate (1:= file).
  instantiate (1:= srcpath).
  cancel.
  
  prestep.
  unfold AByteFile.rep; norm.
  unfold stars; cancel.
  intuition.
  eauto.
  pred_apply; instantiate (1:= file).
  instantiate (1:= srcpath); cancel.
  all: eauto.
  pred_apply.
  cancel.

  unfold AByteFile.rep in H10; split_hypothesis.
  rewrite <- H15; auto. rewrite H16;
  apply list2nmem_array_eq in H8; rewrite H8; auto.
  
  safestep.
  eapply ATOMICCP.tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  eauto.
  rewrite H22; rewrite H21; eauto.
  pred_apply; cancel.
  eauto.

  unfold hpad_length in *; auto.
  rewrite Nat.div_0_l in *; auto.
  rewrite Nat.mod_0_l in *; auto.
  repeat rewrite <- minus_n_O in *; auto.
  simpl in *.
  instantiate (1:= nil).
  instantiate (2:= nil).
  pred_apply; cancel.
  apply list2nmem_array_eq in H7; rewrite <- H7; auto.
  apply list2nmem_array_eq in H8; rewrite <- H8; auto.
  rewrite map_length.
  unfold AByteFile.rep in *; split_hypothesis.
  rewrite <- H17; rewrite <- H26; rewrite H6; auto.
   rewrite Nat.mod_0_l in *; auto.
   apply valubytes_ge_O.
    rewrite Nat.mod_0_l in *; auto.
  rewrite Nat.div_0_l in *; auto.
  rewrite Nat.mod_0_l in *; auto.
  simpl in *.
  rewrite map_length.
  unfold AByteFile.rep in *; split_hypothesis.
  rewrite <- H17; rewrite <- H6; rewrite H26; auto.
  apply list2nmem_array_eq in H8; rewrite H8; auto.
  replace (length copy_data - length copy_data) with 0 by omega.
  apply Nat.min_0_l.
  
  safestep; try (rewrite map_length in H16; omega).
  eauto.
  rewrite <- H29; eauto.
  eauto.
  
  step.
  step.
  apply treeseq_tssync_tree_rep; eauto.
  apply treeseq_upd_iter_tree_rep; auto.
  
  or_r; safecancel.
  instantiate (1:= {| ByFData:= synced_bdata (ByFData fy'); ByFAttr:= (ByFAttr fy) |}).
  unfold rep in *; split_hypothesis.
  unfold rep; repeat eexists.
  instantiate (1:= {| PByFData := map synced_bdata (PByFData x) |} ).
  unfold proto_bytefile_valid, synced_bdata; simpl.
  rewrite H31.
  rewrite synced_list_map_nil_eq.
  repeat rewrite map_map; simpl.
  
  replace (fun x5 : valuset =>
   map (fun x6 : byte => (x6, [])) (map fst (valuset2bytesets x5)))
   with (fun x5 : valuset => valuset2bytesets (fst x5, [])); auto.
  apply functional_extensionality; intros.
  destruct x5; simpl.
  unfold valuset2bytesets; simpl.
  rewrite mapfst_valuset2bytesets_rec.
  rewrite v2b_rec_nil.
  rewrite l2b_cons_x_nil; auto.
  length_rewrite_l.
  length_rewrite_l.
  
  rewrite Forall_forall; intros z Hz.
  apply in_map_iff in Hz; repeat destruct Hz.
  repeat destruct H57; length_rewrite_l.
  
  
  instantiate (1:= {| UByFData:= synced_bdata (UByFData x0) |}).
  unfold unified_bytefile_valid; rewrite H32; simpl.
  unfold synced_bdata.
  repeat rewrite concat_map.
  repeat rewrite map_map; simpl; auto.
  
  
  unfold bytefile_valid; rewrite H34.
  simpl.
  rewrite synced_bdata_length; rewrite firstn_length_l.
  unfold synced_bdata; repeat rewrite firstn_map_comm; auto.
  eapply bytefile_unified_byte_len; eauto.
  simpl; auto.
  simpl; rewrite synced_bdata_length; auto.
  rewrite H6;rewrite H30; auto.
  simpl; rewrite synced_bdata_length; rewrite synced_list_length;  rewrite map_length; auto.
  simpl.
  rewrite Nat.div_0_l in H16; auto.
  rewrite Nat.mod_0_l in H16; auto.
  apply list2nmem_array_eq in H16.
  rewrite H16.
  unfold synced_bdata.
  rewrite merge_bs_map_fst.
  apply list2nmem_array.
  simpl; auto.
  eauto.
  
  eapply treeseq_pushd_tree_rep; eauto.
  eapply tree_rep_update_subtree; eauto.
  eapply treeseq_tssync_tree_rep; eauto.
  eapply treeseq_upd_iter_tree_rep; eauto.
  eapply treeseq_tssync_tree_rep; eauto.
  eapply treeseq_upd_iter_tree_rep; eauto.
  
  repeat xcrash_rewrite.
  xform_norm. 
  xcrash.
  eauto.
  eapply treeseq_tssync_tree_rep; eauto.
  eapply treeseq_upd_iter_tree_rep; eauto.
  
  
  xcrash.
  apply H47.
  eapply treeseq_pushd_tree_rep; eauto.
  eapply tree_rep_update_subtree; eauto.
  eapply treeseq_tssync_tree_rep; eauto.
  eapply treeseq_upd_iter_tree_rep; eauto.
  eapply treeseq_tssync_tree_rep; eauto.
  eapply treeseq_upd_iter_tree_rep; eauto.
  
  
  xcrash; eauto.
  eapply treeseq_upd_iter_tree_rep; eauto.
  
  xcrash; eauto.
  eapply treeseq_upd_iter_tree_rep; eauto.
  
  xcrash; eauto.
  xcrash; eauto.
  
  Unshelve.
  all: repeat constructor.
  all: apply any.
Qed.
Proof.
  unfold copy2temp, tree_with_tmp; step.
  instantiate(1:= file).
  instantiate(1:= srcpath).
  cancel.
  step.
  rewrite H19; eauto.
  cancel.
  unfold rep in *; split_hypothesis.
  rewrite <- H13; rewrite H14; rewrite H15; auto.
  rewrite Nat.div_mul; auto.
  
  step.
  step.

  prestep; norm.
  inversion H23.
  inversion H23.
  unfold stars; cancel.
  instantiate (10:= fy).
  split.
  split.
  split.
  split.
  split.
  split.
  split.
  intuition.
  eauto.
  rewrite H14; apply H35.
  rewrite H28; rewrite H4; apply H26.
  rewrite H19; eauto.
  rewrite update_update_subtree_same.
  apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
  eauto.
  apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
  unfold tree_with_tmp.
  pred_apply; cancel.
  eauto.
  apply bytefile_exists.
  simpl.
  rewrite setlen_length.
  rewrite roundup_div_mul; auto.
  eauto.
  simpl; apply list2nmem_array.
  simpl.
  unfold rep in *; split_hypothesis.
  rewrite H25; auto.
  auto.
  auto.
  
  step.
  
  unfold tree_with_tmp in *; or_l; cancel.
    unfold tree_with_tmp in *; or_r; safecancel.
  eauto.
  eauto.
  auto.
  
  xcrash.
  xcrash; eauto.
  
  unfold stars; cancel.
  unfold tree_with_tmp; or_l; cancel.
  2: intuition; eauto.
  pred_apply; cancel.
  apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
  eauto.
  
  unfold stars; cancel.
   intuition; eauto.
  rewrite update_update_subtree_same.
  apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
  apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
  
  
  xcrash; eauto.
    apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
    rewrite update_update_subtree_same.
  apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
  apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
  
  xcrash; eauto.
    apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
  
 xcrash; eauto.
   apply treeseq_pushd_tree_rep; auto.
  apply tree_rep_update_subtree; auto.
  
  xcrash; eauto.
  
  Unshelve.
  all: repeat econstructor.
  all: apply any.
Qed.
Proof.
  unfold copy_and_rename; step.
  prestep.
  unfold pimpl; intros m' Hx; destruct_lift Hx.
  apply sep_star_or_distr in H;
  inversion H;
  destruct_lift H0.
  inversion H4.
  eapply tree_with_tmp_the_dnum in H15 as Hx; eauto.
  destruct Hx.
  destruct H15.
  pred_apply; cancel.
  instantiate (2:= []); simpl.
  rewrite H18; eauto.
  simpl; cancel.
  
  step.
  step.
  or_l; cancel.
  eapply NEforall_d_in'.
  intros.
  destruct H25.
  rewrite H25; simpl.
  eapply NEforall_d_in in H20.
  apply H20.
  apply latest_in_ds.
  simpl in H25; inversion H25.
    unfold tree_with_tmp; cancel.
    
  xcrash.
  eapply crash_ts_split; eauto.

  step.
  or_r; safecancel.

  eapply NEforall_d_in'.
  intros.
  destruct H25.
  simpl in H25; rewrite H25.
  repeat rewrite pushd_latest in *.

  unfold tree_rep; simpl; split.
  eapply rep_tree_names_distinct; eauto.
  split; auto.
  eapply treerep_synced_dirfile; eauto.
  right; left; pred_apply; unfold tree_with_src; cancel.
  
  simpl in H25; inversion H25.
  
  unfold tree_with_src; cancel.
  all: eauto.
  
  xcrash; eauto.
  or_r; xcrash; eauto.
  unfold tree_rep; simpl; split.
  eapply rep_tree_names_distinct; eauto.
  split.
  eapply treerep_synced_dirfile; eauto.
  right; left; pred_apply; unfold tree_with_src; cancel.
  
  destruct dummy0;
  destruct l1.
  repeat xcrash_rewrite.
  unfold pimpl; intros m'' Hx.
  apply H17 in Hx.
  apply crash_xform_or_dist in Hx.
  inversion Hx.
  
  pred_apply; xcrash.
  eapply crash_ts_split; eauto.
  
  pred_apply; xcrash.
  or_r; xcrash; eauto.
  unfold tree_rep; simpl; split.
  eapply rep_tree_names_distinct; eauto.
  split.
  eapply treerep_synced_dirfile; eauto.
  right; left; pred_apply; unfold tree_with_src; cancel.
  
  
  repeat xcrash_rewrite.
  unfold pimpl; intros m'' Hx.
  apply H17 in Hx.
  pred_apply; xcrash.
  eapply crash_ts_split; eauto.
  
  or_r; xcrash; eauto.
  unfold tree_rep; simpl. split.
  eapply rep_tree_names_distinct; eauto.
  split.
  eapply treerep_synced_dirfile; eauto.
  right; left; pred_apply; unfold tree_with_src; cancel.
  
  norm.
  unfold stars; cancel.
  intuition; eauto.
  
  step.
  or_l; cancel.
  eapply NEforall_d_in'; intros.
  destruct H14.
  simpl in H14; rewrite H14.
  apply treeseq_pred_tree_rep_latest; auto.
  simpl in *; inversion H14.
  
  xcrash.
  eapply crash_ts_split; eauto.
  
  inversion H0.
  inversion H0.
  
  repeat xcrash_rewrite.
  unfold pimpl; intros m'' Hx.
  apply crash_xform_exists_comm in Hx; destruct Hx.
  apply crash_xform_exists_comm in H4; destruct H4.
  pred_apply; xcrash.
  eapply crash_ts_split; eauto.

  Unshelve.
  all: repeat constructor.
  all: apply any.
Qed.