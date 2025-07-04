Proof. intros; unfold diskIs; reflexivity. Qed.

Proof.
intros.
eapply diskIs_extract.
eapply list2nmem_ptsto_cancel in H.
pred_apply; cancel.
firstorder.
Qed.
Proof.
intros.
unfold mem_except_range.
rewrite <- plus_n_O.
apply functional_extensionality.
intros.
destruct (le_dec a x);
destruct (lt_dec x a); try omega; try reflexivity.
Qed.
Proof.
intros.
eexists.
apply sep_star_comm.
apply mem_except_ptsto with (a:= a).
unfold mem_except_range.
destruct H0.
destruct (le_dec s a); try omega.
unfold list2nmem, some_strip.
erewrite selN_map.
reflexivity. auto.
destruct (lt_dec a (s + n)); try omega.
destruct (le_dec s a); try omega.
unfold list2nmem, some_strip.
erewrite selN_map.
reflexivity. auto.
instantiate (1:= diskIs (mem_except (mem_except_range (list2nmem l) s n) a)).
apply diskIs_id.
Grab Existential Variables.
apply valuset0.
apply valuset0.
Qed. 
Proof.
intros.
unfold mem_except, mem_except_range.
apply functional_extensionality; intros.
destruct (AEQ x i).
rewrite e.
destruct (le_dec i i).
destruct (lt_dec i (i + (j + 1))).
reflexivity.
omega.
omega.

destruct (le_dec i x).
destruct (le_dec (i+1) x).
destruct (lt_dec x (i + 1 + j)).
destruct (lt_dec x (i + (j + 1))).
reflexivity.
omega.
destruct (lt_dec x (i + (j + 1))).
omega.
reflexivity.
destruct (lt_dec x (i + (j + 1))).
omega.
reflexivity.
destruct (le_dec (i+1) x).
destruct (lt_dec x (i + 1 + j)).
omega.
all: reflexivity.
Qed.
Proof.
intros.
unfold mem_except, mem_except_range.
apply functional_extensionality; intros.
destruct (AEQ x (i + j)).
rewrite e.
destruct (le_dec i (i + j)).
destruct (lt_dec (i + j) (i + (j + 1))).
reflexivity.
omega.
omega.

destruct (le_dec i x).
destruct (lt_dec x (i + j)).
destruct (lt_dec x (i + (j + 1))).
reflexivity.
omega.
destruct (lt_dec x (i + (j + 1))).
omega.
reflexivity.
reflexivity.
Qed.
Proof.
intros.
unfold valu2list.
eapply ptsto_valid' in H.
unfold list2nmem in H.
erewrite selN_map in H.
simpl in H.
unfold map in H.
symmetry;
apply some_eq. apply H.
eapply selN_map_some_range.
apply H.
Qed.
Proof.
intros.
erewrite block_content_match with (f:=f) (vs:=vs) (block_off:= block_off) (def:= def').
reflexivity.
apply H0.
Qed.
Proof.
intros.
rewrite H.
rewrite firstn_length.
rewrite flat_map_len.
apply le_min_r.
Qed.
Proof.
intros.
rewrite H.
rewrite firstn_length.
apply le_min_r.
Qed.
Proof.
intros.
rewrite H.
apply concat_hom_length with (k:= k).
apply H0.
Qed.
Proof.
unfold bytefile_valid; intros.
pose proof H0.
rewrite H in H0.
apply list2nmem_sel with (def:= byteset0) in H0.
rewrite H0.
rewrite selN_firstn.
apply sep_star_comm.
apply sep_star_assoc.
replace (list2nmem(UByFData ufy))
    with (list2nmem(ByFData fy ++ skipn (length (ByFData fy)) (UByFData ufy))).
apply list2nmem_arrayN_app.
apply sep_star_comm.
rewrite selN_firstn in H0.
rewrite <- H0.
apply H1.
apply list2nmem_inbound in H1.
apply H1.
rewrite H.
rewrite firstn_length.
rewrite min_l. 
rewrite firstn_skipn.
reflexivity.
apply bytefile_unified_byte_len.
apply H.
apply list2nmem_inbound in H1.
apply H1.
Qed.
Proof.
unfold get_sublist, unified_bytefile_valid.
intros.
rewrite H.
rewrite concat_hom_skipn with (k:= k).
replace (k) with (1 * k) by omega.
rewrite concat_hom_firstn.
rewrite firstn1.
rewrite skipn_selN.
simpl.
repeat rewrite <- plus_n_O.
apply addr_id.
apply Nat.div_lt_upper_bound.
unfold not; intros.
rewrite H3 in H1; inversion H1.
rewrite Nat.mul_comm.
rewrite <- unified_byte_protobyte_len with (ufy:= ufy).
apply list2nmem_inbound in H2.
apply H2.
apply H.
apply H0.
simpl;  rewrite <- plus_n_O.
apply forall_skipn.
apply H0.
apply H0.
Qed.
Proof.
unfold proto_bytefile_valid; intros.
rewrite H in H0.
pose proof H0.
eapply list2nmem_sel in H0.
erewrite selN_map in H0.
rewrite H0.
rewrite valuset2bytesets2valuset.
apply addr_id.
apply list2nmem_inbound in H1.
rewrite map_length in H1.
apply H1.
apply list2nmem_inbound in H1.
rewrite map_length in H1.
apply H1.
Grab Existential Variables.
apply nil.
apply valuset0.
Qed. 
Proof.
unfold proto_bytefile_valid, 
    unified_bytefile_valid, 
    bytefile_valid.
intros.
destruct_lift H.
rewrite flat_map_concat_map.
rewrite <- H.
rewrite <- H0.
apply H1.
Qed.
Proof.
unfold rep; intros.
split_hypothesis.
eapply list2nmem_arrayN_bound in H2.
destruct H2.
rewrite H2 in H1.
inversion H1.
rewrite len_f_fy with (f:=f) (fy:=fy) in H2.
apply le2lt_l in H2.
apply lt_weaken_l with (m:= j) in H2.
apply lt_mult_weaken in H2.
apply H2.
apply H1.
eapply bytefile_bfile_eq; eauto.
Qed.
Proof.
intros.
repeat eexists.
eapply unifiedbyte2protobyte with (a:= i * valubytes + j) (k:= valubytes)in H0.
rewrite div_eq in H0.
unfold proto_bytefile_valid in H.
eapply protobyte2block; eauto.
apply H2.
apply Forall_forall; intros.
rewrite H in H5.
apply in_map_iff in H5.
destruct H5.
inversion H5.
rewrite <- H6.
apply valuset2bytesets_len.
omega.
eapply byte2unifiedbyte.
eauto.
pred_apply.
rewrite arrayN_isolate with (i:=0).
rewrite <- plus_n_O .
cancel.
auto.
Grab Existential Variables.
apply byteset0.
Qed.
Proof.
intros.
apply Forall_forall; intros.
rewrite H in H0.
apply in_map_iff in H0.
destruct H0.
inversion H0.
rewrite <- H1.
apply valuset2bytesets_len.
Qed.
Proof.
intros.
apply Forall_forall; intros.
apply in_skipn_in in H0.
rewrite H in H0.
rewrite in_map_iff in H0.
repeat destruct H0.
apply valuset2bytesets_len.
Qed.
 Proof.
 intros.
       
unfold get_sublist.
apply arrayN_list2nmem in H2 as H1'.
rewrite H1 in H1'.
rewrite <- skipn_firstn_comm in H1'.
rewrite firstn_firstn in H1'.
rewrite min_l in H1'.
rewrite H0 in H1'.

rewrite skipn_firstn_comm in H1'.
rewrite Nat.add_comm in H1'.
rewrite <- skipn_skipn with (m:= i * valubytes) in H1'.
rewrite concat_hom_skipn in H1'.
rewrite <- skipn_firstn_comm in H1'.
erewrite <- concat_hom_subselect_firstn with (k:= valubytes) in H1'.

rewrite H in *.
erewrite selN_map in *.
rewrite valuset2bytesets2valuset.

rewrite skipn_firstn_comm in H1'.
rewrite H1'.
rewrite firstn_length.
rewrite skipn_length.
rewrite min_l.
rewrite <- firstn_map_comm.
rewrite <- skipn_map_comm.

rewrite mapfst_valuset2bytesets.
reflexivity.

rewrite valuset2bytesets_len.
omega.

all: try eapply inlen_bfile; eauto.
all: try eapply proto_len; eauto.
unfold rep; repeat eexists; eauto.
unfold rep; repeat eexists; eauto.
unfold rep; repeat eexists; eauto.

rewrite H; rewrite map_length.
eapply inlen_bfile; eauto.
unfold rep; repeat eexists; eauto.

apply list2nmem_arrayN_bound in H2.
destruct H2.
rewrite H2 in H4; inversion H4.
omega.


apply byteset0.

Grab Existential Variables.
apply valuset0.
apply nil.
Qed.
Proof. 
intros.
unfold BFILE.rep in H0.
repeat rewrite sep_star_assoc in H0.
apply sep_star_comm in H0.
repeat rewrite <- sep_star_assoc in H0.

unfold BFILE.file_match in H0.
rewrite listmatch_isolate with (i:=inum) in H0.
sepauto.
rewrite listmatch_length_pimpl in H0.
sepauto.
rewrite listmatch_length_pimpl in H0.
sepauto.
Qed.
Proof.
  intros.
  eapply sep_star_ptsto_some_eq with (a:= (selN ilist i _)).
  erewrite listmatch_isolate with (i:= i) in H.
  apply sep_star_comm.
  eapply sep_star_assoc in H.
  eapply H.
  auto.
  apply listmatch_length_r in H as H'.
  rewrite <- H'; auto.
  rewrite listmatch_extract with (i:= i) in H0.
  destruct_lift H; destruct_lift H0.
  apply ptsto_valid' in H0.
  unfold selN in *.
  instantiate (1:= 0).
  eauto.
  apply listmatch_length_r in H as H'.
  apply listmatch_length_r in H0 as H0'.
  omega.
Qed.
Proof.
intros.
erewrite unified_byte_protobyte_len with (k:= valubytes); eauto.
apply mult_le_compat_r.
apply lt_le_S.
eapply lt_le_trans with (m:= length (ByFData fy)) in H2.
2: apply bytefile_unified_byte_len; eauto.
erewrite unified_byte_protobyte_len with (k:= valubytes) in H2; eauto.
apply lt_mult_weaken in H2; auto.
eapply proto_len; eauto.
eapply proto_len; eauto.
Qed.
Proof.
intros.
apply bytefile_unified_byte_len in H1.
eapply lt_le_trans with (m:= length (ByFData fy))in H2.
2:eauto.
erewrite unified_byte_protobyte_len with (k:= valubytes) in H2.
2:eauto.
apply lt_weaken_l in H2.
rewrite H in H2.
rewrite map_length in H2.
apply lt_mult_weaken in H2.
auto.
eapply proto_len; eauto.
Qed. 
Proof.
intros.
rewrite H3; rewrite H2; rewrite H1.
rewrite selN_firstn.
rewrite concat_hom_selN.
erewrite selN_map.
reflexivity.
eapply inbound_bytefile_bfile; eauto.
rewrite <- H1; eapply proto_len; eauto.
auto.
auto.
Qed.
Proof.
intros.
rewrite H.
rewrite map_length.
apply list2nmem_arrayN_bound in H2 as H'.
destruct H'.
rewrite <- length_zero_iff_nil in H6.
rewrite H6 in H4; symmetry in H4; apply mult_is_O in H4.
destruct H4.
omega.
rewrite valubytes_is in *; omega.
apply list2nmem_arrayN_bound in H2.
destruct H2.
apply length_zero_iff_nil in H2; rewrite valubytes_is in *; omega.


rewrite bytefile_unified_byte_len with (ufy:= ufy) in H6; eauto.
rewrite unified_byte_protobyte_len with (pfy:= pfy)(k:=valubytes) in H6; eauto.
rewrite H4 in H6.
eapply le_lt_weaken with (k:= m1 * valubytes) in H6; eauto.
rewrite <- Nat.mul_add_distr_r in H6.
apply lt_mult_weaken in H6.
rewrite H in H6.
rewrite map_length in H6.
auto.
rewrite valubytes_is in *; omega.
eapply proto_len; eauto.
Qed.
Proof.
intros.
unfold unique.
apply Nat.mod_divides in H2; destruct H2.
exists x.
split.
rewrite Nat.mul_comm; auto.
intros.
rewrite H2 in H4.
rewrite Nat.mul_comm in H4.
apply Nat.mul_cancel_r in H4; auto.
apply valubytes_ne_O.
unfold not; intros.
unfold not in *; apply mod_dem_neq_dem with (a:= length (ByFData fy)) (b:= valubytes); intros; rewrite valubytes_is in *; omega.
Qed.
Proof.
intros.
rewrite H.
apply map_length.
Qed.
Proof.
induction l2; intros.
simpl.
apply emp_star_r.
subst.
unfold mem_except_range in H1.
rewrite app_assoc in H1.
rewrite app_nil_r in H1.
simpl in H1.
rewrite <- plus_n_O in H1.
replace (list2nmem (l1 ++ l3)) with 
        (fun a' : addr =>
       if le_dec (length l1) a' then if lt_dec a' (length l1) then None else list2nmem (l1 ++ l3) a' else list2nmem (l1 ++ l3) a').
auto.
apply functional_extensionality; intros.
destruct (le_dec (length l1) x);
destruct (lt_dec x (length l1)); try reflexivity.
omega.

subst.
rewrite arrayN_isolate with (i := 0).
simpl.
apply sep_star_assoc.
replace (length l1 + 0 + 1) with (length (l1 ++ a :: nil)).
replace (l1 ++ a :: l2 ++ l3) with ((l1 ++ (a :: nil)) ++ l2 ++ l3).
eapply IHl2 with (F:= (F ✶ (emp ✶ (length l1 + 0) |-> a))%pred).
auto.
instantiate (1:= length l2).
reflexivity.
apply sep_star_assoc.
apply sep_star_comm.
apply mem_except_ptsto.
rewrite <- plus_n_O.
unfold list2nmem.
unfold mem_except_range.
erewrite selN_map.
rewrite selN_app.
rewrite selN_app2.
replace (length l1 - length l1) with 0 by omega.
simpl.
rewrite app_length; simpl.
destruct (le_dec (length l1 + 1) (length l1)); try omega; try reflexivity.
omega.
rewrite app_length; simpl; omega.
repeat rewrite app_length; simpl; omega.
apply emp_star_r.
unfold mem_except, mem_except_range.
rewrite <- plus_n_O.
repeat rewrite app_length in *; simpl in *.
replace (fun a' : addr =>
   if addr_eq_dec a' (length l1)
   then None
   else
    if le_dec (length l1 + 1) a'
    then if lt_dec a' (length l1 + 1 + length l2) then None else list2nmem ((l1 ++ a :: nil) ++ l2 ++ l3) a'
    else list2nmem ((l1 ++ a :: nil) ++ l2 ++ l3) a')
    
with (mem_except_range (list2nmem (l1 ++ a :: l2 ++ l3)) (length l1) (S (length l2))).
auto.
unfold mem_except_range.
apply functional_extensionality; intros.

replace ((length l1 + 1 + length l2)) with (length l1 + S (length l2)) by omega.
replace (((l1 ++ a :: nil) ++ l2 ++ l3)) with (l1 ++ a :: l2 ++ l3).

destruct (le_dec (length l1 + 1) x);
destruct (le_dec (length l1) x);
destruct (addr_eq_dec x (length l1)); try omega; try reflexivity.
destruct (lt_dec x (length l1 + S (length l2))); try omega; try reflexivity.

rewrite <- app_assoc.
rewrite <- cons_app.
reflexivity.

rewrite <- app_assoc.
rewrite <- cons_app.
reflexivity.

rewrite app_length; simpl; omega.
simpl; omega.

Unshelve.
auto.
auto.
Qed. 
Proof.
induction l; intros.
simpl in *.
unfold mem_except_range.
rewrite <- plus_n_O.
replace ((fun a' : addr => if le_dec a a' then if lt_dec a' a then None else m a' else m a')) with m.
apply sep_star_comm in H.
apply star_emp_pimpl in H; auto.
apply functional_extensionality; intros.
destruct (le_dec a x);
destruct (lt_dec x a);
try omega; try reflexivity.
replace (mem_except_range m a0 (length (a :: l))) with (mem_except_range (mem_except m a0) (a0 + 1) (length l)).
apply IHl.
rewrite isolateN_fwd with (i:= 0) in H; simpl in H.
rewrite star_emp_pimpl in H.
rewrite <- plus_n_O in H.
apply sep_star_comm in H.
apply sep_star_assoc in H.
apply ptsto_mem_except in H. pred_apply; cancel.
simpl; omega.
apply functional_extensionality; intros.
unfold mem_except, mem_except_range; simpl.
replace (S (length l)) with ( 1 + length l) by omega.
rewrite Nat.add_assoc.
destruct (le_dec (a0 + 1) x);
destruct (lt_dec x (a0 + 1 + length l));
destruct (addr_eq_dec x a0);
destruct (le_dec a0 x);
try omega; try reflexivity.
Grab Existential Variables.
auto.
Qed. 
Proof.
intros.
apply Nat.lt_le_incl.
eapply inlen_bfile with (j:= 0); eauto; try omega.
apply valubytes_ge_O.

2: {
pred_apply.
rewrite <- plus_n_O.
cancel.
}
rewrite valubytes_is in *; omega.
Qed.
Proof.
intros.
apply list2nmem_arrayN_bound in H2 as H''.
destruct H''.
apply length_zero_iff_nil in H3.
assert (X: forall a, a = 0 -> a > 0 -> False). intros. omega.
apply X in H3.  
contradiction.
auto.
eapply le_lt_weaken in H3.
eapply H3.
auto.
Qed.
Proof.
intros.
apply list2nmem_arrayN_bound in H2 as H''.
destruct H''.
apply length_zero_iff_nil in H3.
assert (X: forall a, a = 0 -> a > 0 -> False). intros. omega.
apply X in H3.  
contradiction.
auto.

eapply le_lt_weaken in H3.
2: eauto.
omega.
Qed.
Proof. 
intros.
apply list2nmem_arrayN_bound in H0 as H'.
destruct H'.
rewrite H1 in H; inversion H.
omega.
Qed.
Proof. 
intros.
apply list2nmem_arrayN_bound in H1 as H'.
destruct H'.
pose proof length_old_data_ge_O; eauto.
apply length_zero_iff_nil in H2.
eapply H3 in H; eauto.
inversion H.
omega.
rewrite valubytes_is in *; omega.
Qed.
Proof.
	intros.
	erewrite <- bfile_protobyte_len_eq; eauto.
	erewrite <- unified_byte_protobyte_len; eauto.
	apply bytefile_unified_byte_len; eauto.
	eapply proto_len; eauto.
Qed. 
Proof.
	intros.
	rewrite <- listupd_memupd in H0.
	apply list2nmem_inj in H0.
	symmetry; auto.
	auto.
Qed.
Proof.
	intros.
	apply functional_extensionality; intros.
	unfold mem_except_range; simpl.
	destruct (le_dec a x); simpl.
	destruct (le_dec (S a) x).
	rewrite plus_n_Sm.
	destruct (lt_dec x (a + S n)).
	reflexivity.
	unfold mem_except; simpl.
	destruct (Nat.eq_dec x a).
	omega.
	reflexivity.
	apply Nat.nle_gt in n0.
	inversion n0.
	destruct (lt_dec a (a + S n)).
	rewrite mem_except_eq.
	reflexivity.
	omega.
	omega.
	destruct (le_dec (S a) x).
	omega.
	unfold mem_except.
	destruct (Nat.eq_dec x a).
	omega.
	reflexivity.
Qed.
Proof.
	intros; apply functional_extensionality; intros.
	unfold mem_except_range; simpl; subst.
	destruct (le_dec (length l1) x);
	destruct (lt_dec x ((length l1) + (length l2))); try reflexivity; try omega.
	unfold list2nmem.
	apply Nat.nlt_ge in n.
	repeat rewrite map_app.
	repeat rewrite selN_app2.
	repeat rewrite map_length.
	rewrite H3.
	reflexivity.
	all: repeat rewrite map_length.
	all: subst.
	all: try omega.
	apply Nat.nle_gt in n.
	unfold list2nmem.
	repeat rewrite map_app.
	repeat rewrite selN_app1.
	reflexivity.
	all: repeat rewrite map_length; omega.
Qed.
Proof.
	intros;
	remember (diskIs (mem_except_range (list2nmem l) a b)) as F;
	remember (firstn b (skipn a l)) as x.
	replace l with (firstn a l ++ firstn b (skipn a l) ++ skipn (a + b) l).
	rewrite Heqx; eapply list2nmem_arrayN_middle.
	rewrite firstn_length_l. reflexivity.
	omega.
	instantiate (1:= b).
	rewrite firstn_length_l. reflexivity.
	rewrite skipn_length.
	omega.
	rewrite app_assoc.
	rewrite <- firstn_sum_split.
	rewrite firstn_skipn.
	rewrite HeqF; apply diskIs_id.
	rewrite app_assoc.
	rewrite <- firstn_sum_split.
	rewrite firstn_skipn.
	reflexivity.
Qed.
Proof.
    unfold diskIs.
    intros; symmetry; auto.
Qed.
Proof.
  intros; unfold Mem.upd, mem_except_range.
  destruct H;
  apply functional_extensionality; intros;
  destruct (AEQ x a0); 
  destruct (le_dec a x);
  destruct (lt_dec x (a+b)); try omega; try reflexivity.
Qed.
Proof.
  induction l; intros.
  simpl in *.
  rewrite H.
  rewrite mem_except_range_O.
  cancel.
  destruct b.
  simpl in H; inversion H.
  rewrite arrayN_isolate_hd.
  simpl.
  rewrite <- sep_star_assoc.
  erewrite diskIs_combine_upd.
  replace (S b) with (b + 1) by omega.
  rewrite <- mem_ex_mem_ex_range_head.
  
  rewrite diskIs_combine_upd.
  rewrite upd_mem_except_range_comm.
  apply IHl.
  simpl in H; inversion H; auto.
  left; omega.
  destruct (m a0) eqn:D.
  eapply ptsto_upd' with (v0:= v).
  apply sep_star_comm.
  apply mem_except_ptsto.
  auto.
  apply diskIs_id.
  apply ptsto_upd_disjoint.
  rewrite mem_except_none.
  apply diskIs_id.
  all: auto.
  simpl; omega.
  Grab Existential Variables.
  trivial.
Qed.
Proof.
  induction l'; intros.
  simpl.
  rewrite <- plus_n_O; rewrite firstn_skipn; reflexivity.
  simpl.
  rewrite <- listupd_memupd.
  replace (firstn a0 l ++ a :: l' ++ skipn (a0 + S (length l')) l)
    with (firstn (a0 + 1) (l ⟦ a0 := a ⟧) ++ l' ++ skipn ((a0 + 1) + length l') (l ⟦ a0 := a ⟧)).
  apply IHl'.
  rewrite length_updN.
  simpl in H; omega.
  rewrite updN_firstn_skipn.
  rewrite app_comm_cons.
  rewrite app_assoc.
  rewrite app_assoc.
  rewrite firstn_app_l.
  rewrite firstn_oob.
  rewrite skipn_app_r_ge.
  rewrite skipn_skipn.
  replace (a0 + 1 + length l' - length (firstn a0 l ++ a :: nil) + (a0 + 1))
    with (a0 + S (length l')).
  repeat rewrite app_assoc_reverse.
  rewrite <-cons_app.
  reflexivity.
  all: try (rewrite app_length; rewrite firstn_length_l; simpl in *).
  all: simpl in H; try omega.
Qed.
Proof.
  intros.
  apply diskIs_combine_upd_range in H1.
  apply diskIs_eq in H1.
  rewrite upd_range_list2nmem_comm in H1.
  apply list2nmem_inj in H1.
  rewrite H1.
  repeat rewrite app_length.
  rewrite skipn_length.
  rewrite firstn_length_l.
  all: omega.
Qed.
Proof.
  intros.
  apply diskIs_combine_upd in H0 as H'.
  apply diskIs_eq in H'.
  symmetry in H'; apply list2nmem_upd_updN in H'.
  rewrite H'.
  apply length_updN.
  auto.
Qed.
Proof.
  intros.
  apply diskIs_arrayN_length in H1.
  all: auto.
Qed.
Proof.
  intros.
  apply diskIs_eq in H0.
  rewrite upd_range_list2nmem_comm in H0.
  apply list2nmem_inj in H0.
  all: auto.
Qed.
	Proof.
		intros;
		eapply inlen_bfile; eauto; try omega.
		instantiate (1:= off mod valubytes); apply Nat.mod_upper_bound.
		apply valubytes_ne_O.
    2: {
  		rewrite Nat.mul_comm.
  		rewrite <- Nat.div_mod.
  		eauto.
  		apply valubytes_ne_O.
    }
		omega.
	Qed.
	Proof.
		intros; rewrite Forall_forall; intros.
		repeat destruct H.
		apply valu2list_len.
		apply in_map_iff in H.
		repeat destruct H.
		apply valu2list_len.
	Qed.
	Proof. intros; omega. Qed.
	
	Proof.
	intros;
erewrite <- bytefile_unified_byte_len; eauto.
rewrite Nat.mul_comm; rewrite <- Nat.div_mod.
apply Nat.lt_le_incl; auto.
apply valubytes_ne_O.
	Qed.
	Proof.
	intros;
	erewrite <- bytefile_unified_byte_len; eauto.
	rewrite Nat.mul_comm; rewrite Nat.mul_div_le.
	apply Nat.lt_le_incl; auto.
	apply valubytes_ne_O.
	Qed.
	Proof. intros; subst; apply list2nmem_arrayN_app; auto. Qed.


(* Lemma ptsto_subset_b_to_ptsto: forall m l' F a,
(F ✶ arrayN ptsto_subset_b a l')%pred m ->
exists l'', (F ✶ arrayN (ptsto (V:= byteset)) a l'')%pred m /\ length l' = length l''.
	Proof.
		induction l'; intros.
		simpl in H.
		exists nil.
		simpl; auto.
		rewrite arrayN_isolate_hd in H.
		simpl in H.
		apply sep_star_assoc in H.
		apply IHl' in H.
		destruct H.
		unfold ptsto_subset_b in H.
		simpl in H.
		destruct_lift H.
		apply sep_star_assoc in H.
		replace (a0 |-> (a_1, dummy) ✶ arrayN (ptsto (V:=byteset)) (a0 + 1) x)%pred
			with (a0 |-> (selN ((a_1, dummy)::x) 0 byteset0) ✶ arrayN (ptsto (V:=byteset)) (a0 + 1) (skipn 1 ((a_1, dummy)::x)))%pred in H.
		rewrite <- arrayN_isolate_hd in H.
		exists ((a_1, dummy)::x).
		split; simpl; auto.
		simpl; omega.
		reflexivity.
		simpl; omega.
		Grab Existential Variables.
		apply byteset0.
Qed. *)

	Proof.
		intros.
		destruct l.
		unfold not in H; destruct H; reflexivity.
		reflexivity.
	Qed.
	Proof.
		intros.
		induction l.
		reflexivity.
		simpl.
		rewrite IHl.
		destruct a.
		simpl.
		destruct (split l).
		reflexivity.
	Qed.
	Proof.
		induction l; intros.
		reflexivity.
		pose proof H.
		rewrite arrayN_isolate with (i:= 0) in H.
		simpl in H.
		unfold ptsto_subset_b in H.
		replace (firstn (length (a :: l)) (skipn a0 l')) 
				with ((selN (skipn a0 l') 0 byteset0)::(firstn (length l) (skipn (a0 + 1) l'))).
				
		rewrite <- plus_n_O in H.
		destruct_lift H.
		apply IHl in H as H'.
		destruct H'.
		apply sep_star_comm in H.
		apply sep_star_assoc in H.
		eapply list2nmem_sel in H.
		rewrite skipn_selN.
		rewrite <- plus_n_O.
		rewrite <- H.
		reflexivity.
		rewrite cons_app.
		rewrite <- firstn_1_selN.
		replace (skipn (a0 + 1) l') with (skipn 1 (skipn a0 l')).
		rewrite <- firstn_sum_split.
		reflexivity.
		rewrite skipn_skipn.
		rewrite Nat.add_comm;
		reflexivity.
		unfold not; intros.
		apply length_zero_iff_nil in H1.
		rewrite skipn_length in H1.
		apply ptsto_subset_b_to_ptsto in H0.
		repeat destruct H0.
		apply list2nmem_arrayN_bound in H0.
		destruct H0.
		rewrite H0 in H2; simpl in H2; inversion H2.
		rewrite <- H2 in H0.
		simpl in H0.
		omega.
		simpl; omega.
		Grab Existential Variables.
		apply byteset0.
	Qed. *)

Proof. destruct l; reflexivity. Qed.

	Proof.
		induction l1;	intros.
		simpl in H; symmetry in H; apply length_zero_iff_nil in H; subst.
		reflexivity.
		destruct l1'.
		simpl in H; inversion H.
		simpl.
		rewrite IHl1.
		reflexivity.
		simpl in H; omega.
	Qed.
	Proof.
			induction l1; intros.
			simpl in *.
			symmetry in H; apply length_zero_iff_nil in H; subst.
			simpl; auto.
			destruct l1'.
			simpl in H; inversion H.
			rewrite arrayN_isolate_hd.
			apply sep_star_assoc.
			eapply IHl1.
			simpl in *; omega.
			assert (0 < length (a::l1)).
			simpl; omega.
			apply H1 in H2.
			destruct H2; simpl in *.
			replace (a0 + 1) with (S a0) by omega.
			unfold ptsto_subset_b; pred_apply; cancel.
			
			intros.
			simpl.
			simpl in H1.
			apply lt_n_S in H2.
			apply H1 in H2.
			auto.
			simpl; omega.
			Grab Existential Variables.
			apply byteset0.
		Qed. *)

	Proof.
			induction l; intros.
			simpl in H; inversion H.
			destruct l'.
			simpl in H0; inversion H0.
			destruct i; simpl.
			reflexivity.
			apply IHl; simpl in *; omega.
	Qed.
	Proof. intros; subst; reflexivity. Qed.

(* Lemma ptsto_subset_b_incl: forall l1 l1' m a F,
length l1 = length l1' ->
(F * arrayN (ptsto (V:= byteset)) a l1)%pred m ->
(F * arrayN ptsto_subset_b a l1')%pred m ->
(forall i, i < length l1 -> incl (byteset2list (selN l1 i byteset0)) (byteset2list (selN l1' i byteset0))).
	Proof.
		induction l1; intros.
		simpl in H2; inversion H2.
		destruct l1'.
		simpl in H; inversion H.
		destruct i; simpl.
		rewrite arrayN_isolate_hd in H1.
		unfold ptsto_subset_b in H1.
		destruct_lift H1.
		apply sep_star_comm in H1.
		apply sep_star_assoc in H1.
		apply ptsto_valid' in H1.
	 	
		apply sep_star_comm in H0.
		apply sep_star_assoc in H0.
		apply sep_star_comm in H0.
	 	apply ptsto_valid' in H0.
	 	rewrite H1 in H0.
	 	inversion H0.
	 	subst.
	 	apply H7.
	 	simpl; omega.
	 	eapply IHl1.
	 	auto.

	 	simpl in *.
	 	apply sep_star_assoc in H0; eauto.
	 	simpl in *.
	 	destruct_lift H1.
	 	unfold ptsto_subset_b in H1; destruct_lift H1.
	 	
	 	apply sep_star_comm in H1 as H'.
		apply sep_star_assoc in H'.
	 	apply ptsto_valid' in H'.
	 	
		apply sep_star_comm in H0 as H''.
		apply sep_star_assoc in H''.
		apply sep_star_comm in H''.
	 	apply ptsto_valid' in H''.
	 	rewrite H' in H''.
	 	inversion H''; subst.
	 	apply H1.
	 	simpl in H2; omega.
	 	Grab Existential Variables.
	 	all: apply byteset0.
 	Qed. *)

  	Lemma merge_bs_firstn_skipn: forall a b c l l',
	a + b = c ->
	merge_bs (firstn c l) (firstn c l') = merge_bs (firstn a l) (firstn a l') 
																					++ merge_bs (firstn b (skipn a l)) (firstn b (skipn a l')).
		Proof.
			induction a; intros.
			simpl.
			simpl in H.
			subst; reflexivity.
			simpl.
			destruct l.
			repeat rewrite firstn_nil.
			reflexivity.
			simpl.
			destruct l'.
			simpl.
			repeat rewrite firstn_nil.
			repeat rewrite merge_bs_nil.
			rewrite <- H.
			simpl.
			rewrite <- map_app.
			rewrite firstn_sum_split.
			reflexivity.
			
			simpl.
			rewrite <- H; simpl.
			erewrite IHa with (b:= b).
			reflexivity.
			reflexivity.
		Qed.
	Proof. intros; subst;	apply arrayN_app.	Qed.
	


(* Lemma arrayN_ptsto_subset_b_frame_extract: forall a m l' F,
(F * arrayN ptsto_subset_b a l')%pred m ->
F (mem_except_range m a (length l')).
	Proof.
		intros.
		eapply ptsto_subset_b_to_ptsto in H.
		repeat destruct H.
		apply arrayN_frame_mem_ex_range in H. 
		rewrite H0; auto.
	Qed. *)

	Proof.
		intros.
		erewrite bfile_protobyte_len_eq; eauto.
		apply Nat.lt_le_incl; eapply inlen_bfile;
		unfold rep; repeat eexists; eauto. 
	Qed.
Proof.
intros.
apply Forall_forall; intros.
apply in_firstn_in in H0.
rewrite H in H0.
apply in_map_iff in H0.
destruct H0.
inversion H0.
rewrite <- H1.
apply valuset2bytesets_len.
Qed.
Proof.
  intros.
  rewrite H1; rewrite H0; rewrite H.
  rewrite selN_firstn; auto.
  rewrite between_exists with (a:= a0)(b:= block_off + 1) (c:= valubytes).
  replace (block_off + 1 - 1) with block_off by omega.
  rewrite concat_hom_selN with (k:= valubytes).
  rewrite selN_map with (default':= valuset0).
  unfold valuset2bytesets. simpl.
  destruct  (snd (selN (DFData f) block_off valuset0)) eqn:D.
  replace (snd (DFData f) ⟦ block_off ⟧) with (nil: list valu).
  simpl.
  rewrite v2b_rec_nil.
  rewrite l2b_cons_x_nil.
  erewrite selN_map.
  simpl.
  replace ( block_off * valubytes + a0 mod valubytes - block_off * valubytes )
  with (a0 mod valubytes) by omega.
  reflexivity.
  rewrite valu2list_len; apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  rewrite valu2list_len. reflexivity.


  rewrite valuset2bytesets_rec_cons_merge_bs.
  rewrite merge_bs_selN; simpl.
  replace ( block_off * valubytes + a0 mod valubytes - block_off * valubytes )
  with (a0 mod valubytes) by omega.
  reflexivity.
  rewrite valu2list_len; apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  rewrite map_length.
  rewrite valuset2bytesets_rec_len.
  apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  replace (snd (DFData f) ⟦ block_off ⟧) with (w::l).
  unfold not; intros Hx; inversion Hx.
  rewrite Forall_forall; intros l' Hx; destruct Hx.
  destruct H6.
  apply valu2list_len.
  apply in_map_iff in H6. repeat destruct H6.
  apply valu2list_len.
  auto.
  rewrite <- H; eapply proto_len; eauto.
  apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  replace (block_off + 1 - 1) with block_off. auto.
  omega.
  rewrite Nat.mul_add_distr_r; omega.
  apply valubytes_ne_O.
Qed.
Proof.
  intros.
  rewrite H1; rewrite H0; rewrite H.
  rewrite selN_firstn; auto.
  rewrite between_exists with (a:= a0)(b:= block_off + 1) (c:= valubytes).
  replace (block_off + 1 - 1) with block_off by omega.
  rewrite concat_hom_selN with (k:= valubytes).
  rewrite selN_map with (default':= valuset0).
  unfold valuset2bytesets. simpl.
  destruct  (snd (selN (DFData f) block_off valuset0)) eqn:D.
  destruct H6; reflexivity.
  simpl.
  rewrite valuset2bytesets_rec_cons_merge_bs.
  rewrite merge_bs_selN; simpl.
  replace ( block_off * valubytes + a0 mod valubytes - block_off * valubytes )
  with (a0 mod valubytes) by omega.
  erewrite selN_map.
  replace (snd (DFData f) ⟦ block_off ⟧) with (w::l).
  simpl.
  reflexivity.
  rewrite valuset2bytesets_rec_len.
  apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  replace (snd (DFData f) ⟦ block_off ⟧) with (w::l).
  unfold not; intros Hx; inversion Hx.
  rewrite valu2list_len; apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  rewrite map_length.
  rewrite valuset2bytesets_rec_len.
  apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  replace (snd (DFData f) ⟦ block_off ⟧) with (w::l).
  unfold not; intros Hx; inversion Hx.
  rewrite Forall_forall; intros l' Hx; destruct Hx.
  destruct H7.
  apply valu2list_len.
  apply in_map_iff in H7. repeat destruct H7.
  apply valu2list_len.
  auto.
  rewrite <- H; eapply proto_len; eauto.
  apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  replace (block_off + 1 - 1) with block_off. auto.
  omega.
  rewrite Nat.mul_add_distr_r; omega.
  apply valubytes_ne_O.
Qed.
Proof.
  intros.
  rewrite H1; rewrite H0; rewrite H.
  rewrite selN_firstn; auto.
  rewrite between_exists with (a:= a0)(b:= block_off + 1) (c:= valubytes).
  replace (block_off + 1 - 1) with block_off by omega.
  rewrite concat_hom_selN with (k:= valubytes).
  erewrite selN_map with (default':= valuset0).
  unfold valuset2bytesets.
  erewrite selN_map.
  unfold byteset2list.
  replace (snd (DFData f) ⟦ block_off ⟧) with (nil: list valu).
  simpl.
  rewrite v2b_rec_nil.
  erewrite selN_map.
  reflexivity.
   rewrite valu2list_len; apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  rewrite valu2list_len; reflexivity.
  rewrite valuset2bytesets_rec_len.
  apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  unfold byteset2list, not; intros Hx; inversion Hx.
  auto.
  rewrite <- H; eapply proto_len; eauto.
  apply Nat.mod_upper_bound.
  apply valubytes_ne_O.
  replace (block_off + 1 - 1) with block_off. auto.
  omega.
  rewrite Nat.mul_add_distr_r; omega.
  Unshelve.
  apply valubytes_ne_O.
  apply nil.
  apply byte0.
Qed.
Proof.
  intros.
  rewrite H.
  rewrite selN_firstn.
  reflexivity.
  auto.
Qed.
Proof.
  induction l; intros.
  repeat rewrite skipn_nil.
  reflexivity.
  destruct a0.
  reflexivity.
  destruct l1.
  simpl.
  rewrite IHl.
  rewrite skipn_nil; reflexivity.
  simpl.
  auto.
Qed.
    Proof.
      intros.
      exists m.
      exists (fun x => None).
      split.
      unfold mem_union.
      apply functional_extensionality; intros.
      destruct (m x); auto.
      unfold mem_disjoint.
      unfold not; intros.
      repeat destruct H.
      inversion H0.
    Qed.
Proof.
    intros.
    unfold subset_invariant_bs in *.
    intros.
    pose proof (sep_star_mem_exists bsl').
    pose proof (sep_star_mem_exists bsl).
    split_hypothesis.
    edestruct H; edestruct H0.
    split_hypothesis.
    left.
    unfold sep_star; rewrite sep_star_is; unfold sep_star_impl.
    repeat eexists; repeat split; eauto.
    split_hypothesis.
    
    right; intros.
    unfold sep_star in H9; rewrite sep_star_is in H9; unfold sep_star_impl in H9.
    split_hypothesis.
    unfold sep_star; rewrite sep_star_is; unfold sep_star_impl.
    exists (fun a => match x1 a with
                     | None => None
                     | Some v => bsl' a
                     end).
    exists (fun a => match x2 a with
                     | None => None
                     | Some v => bsl' a
                     end).
    repeat split; eauto.
    apply functional_extensionality; intros.
    unfold mem_union.
    destruct (bsl x3) eqn:D.
    rewrite H6 in D. unfold mem_union in D.
    destruct (x1 x3) eqn:D1.
    destruct (bsl' x3).
    reflexivity.
    destruct (x2 x3); reflexivity.
    rewrite D; reflexivity.
    
    rewrite H6 in D.
    unfold mem_union in D.
    destruct (x1 x3) eqn:D1.
    inversion D.
    
    destruct H5 with (a:= x3).
    rewrite H6 in H10.
    unfold mem_union in H10.
    rewrite D1 in H10; simpl in H10; rewrite D in H10.
    rewrite H10; rewrite D; reflexivity.
    
    destruct H10.
    rewrite H6 in H10.
    unfold mem_union in H10.
    rewrite D1 in H10; simpl in H10; rewrite D in H10.
    destruct H10; reflexivity.
    
    unfold mem_disjoint in *.
    unfold not; intros.
    do 4 destruct H6.
    destruct H3.
    destruct (x x1) eqn:D.
    destruct (x0 x1) eqn:D1.
    exists x1.
    exists p.
    exists p0.
    split; auto.
    inversion H7.
    inversion H6.
    eapply H.
    intros.
    2: eauto.
    unfold isSubset in *; simpl in *; intros.
    
    destruct H1 with (a:= a).
    left.
    unfold mem_union in *.
    rewrite H2 in H6.
    destruct (x a) eqn:D.
    auto.
    reflexivity.
    
    destruct H6.
    rewrite H2 in H7.
    unfold some_strip, mem_union in *.
    destruct (x a) eqn:D.
    right.
    split.
    unfold not; intros Hx; inversion Hx.
    auto.
    left.
    reflexivity. 
    
    eapply H0.
    intros.
    2: eauto.
    unfold isSubset in *; simpl in *; intros.
    
    destruct H1 with (a:= a).
    left.
    unfold mem_union in *.
    rewrite H2 in H6.
    destruct (x0 a) eqn:D.
    unfold mem_disjoint in *.
    unfold not in *.
    destruct (x a) eqn:D1.
    destruct H3.
    exists a, p0, p.
    split; auto.
    auto.
    reflexivity.
    
    destruct H6.
    rewrite H2 in H7.
    unfold some_strip, mem_union in *.
    destruct (x0 a) eqn:D.
    right.
    split.
    unfold not; intros Hx; inversion Hx.
    destruct (x a) eqn:D1.
    destruct H3.
    exists a, p0, p.
    split; auto.
    auto.
    left; reflexivity.
Qed.
  Proof.
    induction l; intros.
    unfold subset_invariant_bs; intros.
    simpl in *.
    unfold emp in *; intros.
    destruct H with (a:= a0).
    rewrite H0 in H1; auto.
    repeat destruct H1.
    apply H0.
    
    simpl in *.
    apply subset_invariant_bs_union.
    unfold subset_invariant_bs; intros.
    unfold ptsto_subset_b in *;
    destruct_lift H0.
    
    destruct H with (a:= a0).
    apply emp_star in H0 as H'.
    apply ptsto_valid' in H'.
    
    
    exists dummy.
    rewrite H' in H1.
    apply sep_star_lift_apply'.
    apply emp_star.
    apply sep_star_comm.
    apply mem_except_ptsto.
    auto.
    
    assert (forall AT AEQ V (m: @Mem.mem AT AEQ V), m = Mem.empty_mem -> emp m).
    intros.
    rewrite H2.
    apply emp_empty_mem.
    apply H2.
    unfold Mem.empty_mem.
    apply functional_extensionality; intros.
    unfold mem_except.
    destruct (addr_eq_dec x a0).
    reflexivity.
    
    destruct H with (a:= x).
    apply ptsto_ne with (a':= x) in H0 as Hx.
    rewrite H4; rewrite Hx; reflexivity.
    unfold not; intros.
    apply n; omega.
    
    
    destruct H4.
    apply ptsto_ne with (a':= x) in H0 as Hx.
    rewrite Hx in H4.
    destruct H4; reflexivity.
    unfold not; intros.
    apply n; omega.
    auto.
    
    (* part2 *)
    destruct H1.
    apply emp_star in H0 as H'.
    apply ptsto_valid' in H'.
    rewrite H' in H2; simpl in H2.
    
    
    exists (a_1::dummy).
    apply sep_star_lift_apply'.
    apply emp_star.
    apply sep_star_comm.
    apply mem_except_ptsto.
    auto.
    
    assert (forall AT AEQ V (m: @Mem.mem AT AEQ V), m = Mem.empty_mem -> emp m).
    intros.
    rewrite H4.
    apply emp_empty_mem.
    apply H4.
    unfold Mem.empty_mem.
    apply functional_extensionality; intros.
    unfold mem_except.
    destruct (addr_eq_dec x a0).
    reflexivity.
   
   destruct H with (a:= x).
    apply ptsto_ne with (a':= x) in H0 as Hx.
    rewrite H5; rewrite Hx; reflexivity.
    unfold not; intros; apply n; omega.
    
    
    destruct H5.
    apply ptsto_ne with (a':= x) in H0 as Hx.
    rewrite Hx in H5.
    destruct H5; reflexivity.
    unfold not; intros; apply n; omega.
    unfold incl; intros.
    apply H3.
    repeat destruct H4.
    apply in_eq.
    apply in_eq.
    apply in_cons.
    auto.
    auto.
    
    
    unfold sep_star in H2; rewrite sep_star_is in H2; unfold sep_star_impl in H2.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H3.
    destruct H4.
    
    unfold_sep_star.
    exists (fun a => match x a with
                     | None => None
                     | Some v => bsl' a
                     end).
    exists (fun a => match x0 a with
                     | None => None
                     | Some v => bsl' a
                     end).
    repeat split.
    apply functional_extensionality; intros.
    unfold mem_union.
    destruct (bsl x1) eqn:D.
    rewrite H2 in D. unfold mem_union in D.
    destruct (x x1) eqn:D1.
    destruct (bsl' x1).
    reflexivity.
    destruct (x0 x1); reflexivity.
    rewrite D; reflexivity.
    
    rewrite H2 in D.
    unfold mem_union in D.
    destruct (x x1) eqn:D1.
    inversion D.
    
    destruct H1 with (a:= x1).
    rewrite H2 in H6.
    unfold mem_union in H6.
    rewrite D1 in H6; simpl in H6; rewrite D in H6.
    rewrite H6; rewrite D; reflexivity.
    
    destruct H6.
    rewrite H2 in H6.
    unfold mem_union in H6.
    rewrite D1 in H6; simpl in H6; rewrite D in H6.
    destruct H6; reflexivity.
    
    unfold mem_disjoint in *.
    unfold not; intros.
    do 4 destruct H6.
    destruct H3.
    destruct (x x1) eqn:D.
    destruct (x0 x1) eqn:D1.
    exists x1.
    exists p.
    exists p0.
    split; auto.
    inversion H7.
    inversion H6.
    eapply H.
    intros.
    2: eauto.
    unfold isSubset in *; simpl in *; intros.
    
    destruct H1 with (a:= a).
    left.
    unfold mem_union in *.
    rewrite H2 in H6.
    destruct (x a) eqn:D.
    auto.
    reflexivity.
    
    destruct H6.
    rewrite H2 in H7.
    unfold some_strip, mem_union in *.
    destruct (x a) eqn:D.
    right.
    split.
    unfold not; intros Hx; inversion Hx.
    auto.
    left.
    reflexivity. 
    
    eapply H0.
    intros.
    2: eauto.
    unfold isSubset in *; simpl in *; intros.
    
    destruct H1 with (a:= a).
    left.
    unfold mem_union in *.
    rewrite H2 in H6.
    destruct (x0 a) eqn:D.
    unfold mem_disjoint in *.
    unfold not in *.
    destruct (x a) eqn:D1.
    destruct H3.
    exists a, p0, p.
    split; auto.
    auto.
    reflexivity.
    
    destruct H6.
    rewrite H2 in H7.
    unfold some_strip, mem_union in *.
    destruct (x0 a) eqn:D.
    right.
    split.
    unfold not; intros Hx; inversion Hx.
    destruct (x a) eqn:D1.
    destruct H3.
    exists a, p0, p.
    split; auto.
    auto.
    left; reflexivity.
Qed.
  Proof.
    induction l; intros.
    unfold subset_invariant_bs; intros.
    simpl in *.
    unfold emp in *; intros.
    destruct H with (a:= a0).
    rewrite H0 in H1; auto.
    repeat destruct H1.
    apply H0.
    
    simpl in *.
    apply subset_invariant_bs_union.
    unfold subset_invariant_bs; intros.
    unfold ptsto_subset_b in *;
    destruct_lift H0.
    
    destruct H with (a:= a0).
    apply emp_star in H0 as H'.
    apply ptsto_valid' in H'.
    
    
    exists dummy.
    rewrite H' in H1.
    apply sep_star_lift_apply'.
    apply emp_star.
    apply sep_star_comm.
    apply mem_except_ptsto.
    auto.
    
    assert (forall AT AEQ V (m: @Mem.mem AT AEQ V), m = Mem.empty_mem -> emp m).
    intros.
    rewrite H2.
    apply emp_empty_mem.
    apply H2.
    unfold Mem.empty_mem.
    apply functional_extensionality; intros.
    unfold mem_except.
    destruct (addr_eq_dec x a0).
    reflexivity.
    
    destruct H with (a:= x).
    apply ptsto_ne with (a':= x) in H0 as Hx.
    rewrite H4; rewrite Hx; reflexivity.
    unfold not; intros.
    apply n; omega.
    
    
    destruct H4.
    apply ptsto_ne with (a':= x) in H0 as Hx.
    rewrite Hx in H4.
    destruct H4; reflexivity.
    unfold not; intros.
    apply n; omega.
    auto.
    
    (* part2 *)
    destruct H1.
    apply emp_star in H0 as H'.
    apply ptsto_valid' in H'.
    rewrite H' in H2; simpl in H2.
    
    
    exists (a_1::dummy).
    apply sep_star_lift_apply'.
    apply emp_star.
    apply sep_star_comm.
    apply mem_except_ptsto.
    auto.
    
    assert (forall AT AEQ V (m: @Mem.mem AT AEQ V), m = Mem.empty_mem -> emp m).
    intros.
    rewrite H4.
    apply emp_empty_mem.
    apply H4.
    unfold Mem.empty_mem.
    apply functional_extensionality; intros.
    unfold mem_except.
    destruct (addr_eq_dec x a0).
    reflexivity.
   
   destruct H with (a:= x).
    apply ptsto_ne with (a':= x) in H0 as Hx.
    rewrite H5; rewrite Hx; reflexivity.
    unfold not; intros; apply n; omega.
    
    
    destruct H5.
    apply ptsto_ne with (a':= x) in H0 as Hx.
    rewrite Hx in H5.
    destruct H5; reflexivity.
    unfold not; intros; apply n; omega.
    unfold incl; intros.
    apply H3.
    repeat destruct H4.
    apply in_eq.
    apply in_eq.
    apply in_cons.
    auto.
    auto.
Qed.
  Proof.
    intros.
    apply ptsto_subset_b_to_ptsto in H0.
    repeat destruct H0.
    apply list2nmem_arrayN_bound in H0.
    destruct H0.
    rewrite H0 in H1; simpl in H1.
    omega.
    omega.
  Qed. *)


Proof.
  intros.
  destruct sz.
  inversion H.
  simpl in H.
  unfold bsplit1_dep, bsplit2_dep in H; simpl in H.
  inversion H.
  unfold bsplit1.
  eq_rect_simpl.
  unfold natToWord.
  simpl.
  unfold byte0.
  reflexivity.
Qed.
Proof.
  intros.
  rewrite H.
  rewrite H0; apply firstn_exact.
Qed.
Proof. intros; subst; apply list2nmem_app; auto. Qed.



(* Lemma subset_invariant_bs_apply: forall (F:pred) l a,
subset_invariant_bs F ->
F (list2nmem l) ->
F (list2nmem (firstn a l ++ merge_bs (map fst (skipn a l)) (skipn a l))).
Proof.
  intros.
  unfold subset_invariant_bs in H.
  eapply H.
  2: apply H0.
  intros.
  unfold isSubset; intros.
  destruct (le_dec a (length l)).
  destruct (lt_dec a0 a).
  left.
  unfold list2nmem.
  repeat erewrite selN_map.
  apply some_eq.
  rewrite selN_app1.
  rewrite selN_firstn.
  reflexivity.
  auto.
  rewrite firstn_length_l; auto.
  omega.
  rewrite app_length.
  rewrite firstn_length_l.
  omega.
  auto.
  
  destruct (lt_dec a0 (length l)).
  right.
  split.
  unfold list2nmem, not; erewrite selN_map. intros Hx; inversion Hx.
  auto.
  unfold list2nmem.
  erewrite selN_map. 
  rewrite selN_app2.
  rewrite merge_bs_selN.
  erewrite selN_map.
  repeat rewrite skipn_selN.
  repeat rewrite firstn_length_l.
  repeat rewrite <- le_plus_minus.
  apply some_eq.
  unfold some_strip.
  repeat erewrite selN_map.
  reflexivity.
  all: try rewrite firstn_length_l.
  all: try rewrite map_length.
  all: try rewrite skipn_length.
  all: try omega.
  rewrite app_length.
  rewrite merge_bs_length.
  rewrite map_length.
  rewrite skipn_length.
  rewrite firstn_length_l.
  omega.
  auto.
  left.
  unfold list2nmem.
  repeat rewrite selN_oob.
  reflexivity.
  rewrite map_length; omega.
  rewrite map_length.
  rewrite app_length.
  rewrite merge_bs_length.
  rewrite map_length.
  rewrite skipn_length.
  rewrite firstn_length_l.
  omega.
  omega.
  rewrite skipn_oob.
  rewrite firstn_oob.
  simpl.
  rewrite app_nil_r.
  left.
  reflexivity.
  all: omega.
  Grab Existential Variables.
  all: apply byteset0.
Qed.
	Proof.
		intros.
		rewrite H0.
		rewrite firstn_firstn.
		rewrite Nat.min_l.
		reflexivity.
		auto.
	Qed.
		 Proof.
		 	intros.
		 	eapply le_trans.
		 	instantiate (1:= length (UByFData ufy) - valubytes).
		 	omega.
		 	rewrite H1.
		 	rewrite H0.
		 	rewrite H.
		 	rewrite concat_hom_length with (k:= valubytes).
		 	rewrite map_length.
		 	rewrite firstn_length_l.
		 	rewrite Nat.mul_sub_distr_r in H2.
		 	simpl in H2.
		 	rewrite <- plus_n_O in H2.
		 	apply Nat.lt_le_incl.
		 	auto.
	 		rewrite concat_hom_length with (k:= valubytes).
		 	rewrite map_length.
		 	eapply bfile_bytefile_length; eauto.
		 	rewrite <- H.
		 	eapply proto_len; eauto.
		 	rewrite <- H.
		 	eapply proto_len; eauto.
	 	Qed.
	Proof. 
		intros.
		rewrite mod_minus in H2.
		assert (length (ByFData fy) <= length (DFData f) * valubytes).
		eapply bfile_bytefile_length; eauto.
		rewrite H2 in *.
		apply lt_mult_weaken in H3.
		apply le_mult_weaken in H4.
		apply eq_rect_word_mult_helper.
		omega.
		apply valubytes_ge_O.
		apply valubytes_ne_O.
	Qed.
Proof.
	intros.
	unfold get_sublist.
	rewrite H0.
	rewrite concat_hom_skipn.
	replace valubytes with (1* valubytes) by omega.
	rewrite concat_hom_firstn.
	rewrite firstn1.
	rewrite skipn_selN.
	rewrite <- plus_n_O. reflexivity.
	eapply proto_skip_len; eauto.
	eapply proto_len; eauto.
Qed.
	Proof.
		intros.
		erewrite unified_byte_protobyte_len with (k:= valubytes); eauto.
		erewrite bfile_protobyte_len_eq; eauto.
		eapply bfile_bytefile_length_eq; eauto.
		instantiate (1:= length (ByFData fy)).
		omega.
		eapply proto_len; eauto.
	Qed.
  Proof.
    intros.
	  apply H.
	  rewrite <- H0; rewrite H1; simpl.
	  rewrite wordToNat_natToWord_idempotent'; auto.
	  pose proof mod_minus_lt_0.
	  pose proof valubytes_ne_O.
	  apply H4 with (a:= length (ByFData fy')) in H5 as H'.
	  omega.

	  eapply goodSize_trans.
	  2: apply H2.
	  apply plus_le_compat_l.
	  apply mod_ne_0 in H3; auto.
	  omega.
	  apply valubytes_ne_O.
  Qed.
	Proof.
    intros.
    pose proof valubytes_ne_O as Hv.
	  rewrite <- H; rewrite H0; simpl.
	  rewrite wordToNat_natToWord_idempotent'; auto.
	  rewrite Nat.add_sub_assoc. 
	  rewrite Nat.add_sub_swap.
	  rewrite mod_minus.
	  replace (length (ByFData fy') / valubytes * valubytes + valubytes)
		  with ((length (ByFData fy') / valubytes + 1) * valubytes).
	  apply Nat.mod_mul; auto.
	  rewrite Nat.mul_add_distr_r.
	  omega.
	  auto.
	  apply Nat.mod_le; auto.
	  apply mod_upper_bound_le'; auto.
	  eapply goodSize_trans.
	  2: apply H1.
	  apply plus_le_compat_l.
	  apply mod_ne_0 in H2; auto.
	  omega.
  Qed.
  Proof.
    intros.
	
	rewrite Forall_forall; intros.
	apply in_app_iff in H.
	repeat destruct H.
	apply in_map_iff in H.
	repeat destruct H;
	apply valuset2bytesets_len.
	apply valuset2bytesets_len.
  Qed.
  Proof.
    intros.
    apply mod_ne_0 in H0; auto.
    omega.
  Qed.
  Proof.
    induction a; intros; simpl.
    rewrite <- minus_n_O.
    reflexivity.
    destruct n; simpl.
    reflexivity.
    rewrite list_zero_pad_expand; simpl.
    apply IHa.
  Qed.
	Proof. 
		induction a. reflexivity.
		simpl.
		rewrite IHa; reflexivity.
	Qed.
	Proof. intros; omega. Qed.
	
		Lemma list2nmem_arrayN_app_general: forall A (F: pred) a (l l' l'': list A),
	F (list2nmem l) ->
	a = length l ->
	l' = l'' ->
	(F * arrayN (ptsto (V:= A)) a l')%pred (list2nmem (l ++ l'')).
	Proof.
	  intros; subst.
	  apply list2nmem_arrayN_app; auto.
  Qed.
Proof.
	induction a; intros; simpl.
	reflexivity.
	rewrite list_zero_pad_expand.
	rewrite app_assoc_reverse.
	rewrite IHa.
	symmetry; apply list_zero_pad_expand.
Qed.
Proof.
	intros; rewrite Forall_forall; intros.
	apply in_map_iff in H.
	repeat destruct H.
	apply valuset2bytesets_len.
Qed.
Proof.
	intros.
	rewrite concat_hom_length with (k:= valubytes).
	rewrite map_length; reflexivity.
	apply Forall_map_vs2bs.
Qed.
Proof.
	intros; rewrite skipn_oob.
	reflexivity.
	apply le_n.
Qed.
Proof.
	intros; rewrite <- H; rewrite H0; simpl;
	rewrite wordToNat_natToWord_idempotent'; auto.
Qed.
	Proof.
		intros.
		induction a.
		reflexivity.
		unfold natToWord in *.
		simpl.
		unfold bsplit1_dep, bsplit2_dep; simpl.
		unfold bsplit1, bsplit2.
		eq_rect_simpl.
		simpl.
		rewrite list_zero_pad_expand.
		rewrite IHa.
		simpl.
		reflexivity.
	Qed.
  Proof.
    unfold valu0; simpl.
    unfold valu2list.
    rewrite bytes2valu2bytes.
  	apply bsplit_list_0_list_zero_pad_eq.
	Qed.
  Proof.
  	unfold valuset2bytesets; simpl.
  	rewrite v2b_rec_nil.
  	rewrite l2b_cons_x_nil.
	rewrite valu2list_valu0.
	rewrite merge_bs_nil.
	reflexivity.
	symmetry; apply valu2list_len.
	Qed.
Proof.
	induction l.
	unfold synced_list; reflexivity.
	simpl.
	unfold synced_list in *. simpl.
	rewrite IHl; reflexivity.
Qed.
Proof.
	induction l.
	reflexivity.
	simpl.
	rewrite IHl; reflexivity.
Qed.
Proof.
	unfold valuset2bytesets; simpl.
	rewrite v2b_rec_nil.
	rewrite l2b_cons_x_nil.
	rewrite valu2list_valu0.
	apply merge_bs_map_x_nil_eq.
	symmetry; apply valu2list_len.
Qed.
Proof.
	induction l1; intros; try reflexivity.
	simpl.
	rewrite IHl1.
	reflexivity.
Qed.
Proof.
	induction a.
	reflexivity.
	simpl.
	rewrite valuset2bytesets_valu0.
	rewrite IHa.
	rewrite merge_bs_nil_app.
	rewrite list_zero_pad_nil_app.
	reflexivity.
Qed.
Proof. intros; omega. Qed.

Proof.
  intros.
  apply mod_ne_0 in H; omega.
Qed.
Proof.
  intros.
  rewrite Nat.add_sub_assoc.
  rewrite Nat.add_sub_swap.
  rewrite Nat.mod_add.
  apply mod_minus_mod.
  all: auto.
  apply Nat.mod_le; auto.
  destruct c; try omega.
  simpl.
  eapply le_trans.
  apply mod_upper_bound_le'; eauto.
  apply le_plus_l.
Qed.
Proof.
  intros.
  destruct a.
  rewrite Nat.div_0_l in H0; auto.
  omega.
Qed.
Proof.
  intros.
  apply div_ge_0 in H0; auto.
  omega.
Qed.
Proof. intros; split; omega. Qed.

Proof.
  intros.
  apply Nat.div_exact in H1; auto.
  rewrite H0 in H1; simpl in H1.
  rewrite Nat.mul_0_r in H1; auto.
Qed.
Proof.
	intros.
	replace (b - a mod b) with (1 * b - a mod b) by omega.
	apply mod_plus_minus_0; eauto.
Qed.
Proof.
	intros.
	eapply goodSize_trans.
	2: eauto.
	apply plus_le_compat_l.
	apply Nat.nlt_ge in H0; apply H0.
Qed.
Proof.
  intros.
  rewrite H1.
  apply firstn_oob.
  rewrite H2.
  erewrite <- bfile_protobyte_len_eq; eauto.
  erewrite unified_byte_protobyte_len; eauto.
  eapply proto_len; eauto.
Qed.
Proof.
	intros.
	rewrite H.
	rewrite selN_map with (default' := valuset0); auto.
	rewrite mapfst_valuset2bytesets.
	reflexivity.
Qed.
Proof.
	intros.
	unfold bytesets2valuset.
	unfold byteset2list; simpl.
	destruct bsl eqn:D.
	unfold not in H; destruct H; reflexivity.
	simpl.
	rewrite list2valu2list.
	unfold selN'.
	rewrite map_map; simpl.
	reflexivity.
	simpl.
	rewrite map_length.
	rewrite map_length.
	simpl in H0; auto.
Qed.
Proof.
  intros.
  unfold rep.
  apply sync_invariant_sep_star; auto.
Qed.