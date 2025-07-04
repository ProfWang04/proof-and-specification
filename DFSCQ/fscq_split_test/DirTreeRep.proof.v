  Proof.
    unfold rep; intros.
    norml; unfold stars; simpl.
    rewrite BFILE.rep_length_pimpl at 1.
    cancel.
  Qed.
  Proof.
    intros.
    unfold rep in *.
    destruct_lift H.
    eapply pimpl_apply; [ | eapply BFILE.rep_safe_unused; eauto; pred_apply; cancel ].
    cancel.
  Qed.
  Proof.
    intros.

    unfold rep in *.
    destruct_lift H.

    erewrite <- BFILE.rep_used_block_eq with (m := m).
    2: pred_apply; cancel.
    2: eauto.
    f_equal.
    f_equal.

    rewrite subtree_extract in * by eassumption.
    simpl in *.
    apply eq_sym.
    eapply BFILE.rep_used_block_eq_Some_helper.

    destruct_lifts.
    assert (inum < Datatypes.length dummy) as Hlt by ( eapply list2nmem_inbound; pred_apply; cancel ).

    pose proof (list2nmem_sel_inb dummy BFILE.bfile0 Hlt) as Hx.
    eapply pimpl_trans in H2; [ | apply pimpl_refl | ].
    eapply ptsto_valid in H2.
    rewrite Hx in H2; clear Hx.
    2: cancel.
    inversion H2; clear H2.
    rewrite H4; simpl.
    auto.
  Qed.
  Proof.
    induction tree using dirtree_ind2; simpl; intros.
    destruct_lift H0.
    eapply IAlloc.ino_valid_goodSize; eauto.
    unfold tree_dir_names_pred in H1; destruct_lift H1.
    eapply IAlloc.ino_valid_goodSize; eauto.
  Qed.
  Proof.
    unfold rep; intros.
    destruct_lift H0.
    rewrite subtree_extract in H0 by eauto.
    simpl in H0; destruct_lift H0; auto.
  Qed.
  Proof.
    unfold BFILE.mscs_same_except_log; unfold rep; intros.
    intuition msalloc_eq.
    apply pimpl_refl.
  Qed.
  Proof.
    split; eapply mscs_same_except_log_rep'; eauto.
    unfold BFILE.mscs_same_except_log in *; intuition eauto.
  Qed.