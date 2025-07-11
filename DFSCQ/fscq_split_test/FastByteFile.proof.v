  Proof.
    unfold items_per_valu.
    rewrite valulen_is, valubytes_is.
    reflexivity.
  Qed.
  Proof.
    unfold block_items.
    unfold items_per_valu.
    rewrite valubytes_is.
    reflexivity.
  Qed.
  Proof.
    intros.
    apply roundup_ge.
    rewrite valubytes_is.
    (* produces a nicer proof term than omega *)
    apply gt_Sn_O.
  Qed.
  Proof.
    intros.
    rewrite H.
    apply list2nmem_array.
  Qed.
  Proof. cancel. Qed.

  Lemma list2nmem_arrayN_xyz_frame : forall (A:Type) (l:list A)
    off len,
    off + len <= length l ->
    (arrayN 0 (firstn off l) *
    arrayN (off+len) (skipn (off+len) l) *
    arrayN off (firstn len (skipn off l)))%pred (list2nmem l).
  Proof.
    intros.
    apply sep_star_abc_to_acb.
    rewrite arrayN_combine by LOG.solve_lengths.
    apply arrayN_combine.
    LOG.solve_lengths.
    apply list2nmem_array_eq'.
    rewrite <- firstn_sum_split.
    apply firstn_skipn.
  Qed.
   Proof.
    unfold read_bytes, rep, bytes_rep.
    time step. (* 15s *)
    step.
    step.
    step.
    step.

    eapply goodSize_word_bound.
    eapply le_trans.
    apply divup_lt_arg.
    apply Nat.lt_le_incl; eauto.

    erewrite array_items_num_blocks; eauto.
    apply divup_mono.
    eapply le_trans.
    apply Nat.lt_le_incl; eauto.
    apply firstn_length_l_iff; auto.

    step.
    rewrite H15.
    rewrite <- firstn_double_skipn
      with (len2 := # (INODE.ISize (BFILE.BFAttr f)))
      by omega.
    apply list2nmem_arrayN_xyz_frame.
    omega.

    step.
    rewrite le_plus_minus_r by omega.
    eapply goodSize_word_bound.
    eapply le_trans.
    apply divup_lt_arg.
    eauto.

    rewrite le_plus_minus_r by omega.
    erewrite BFileRec.array_items_num_blocks; eauto.
    apply divup_mono.
    apply firstn_length_l_iff; auto.

    step.
    rewrite H15.
    rewrite <- firstn_double_skipn
      with (len2 := # (INODE.ISize (BFILE.BFAttr f)))
      by omega.
    apply list2nmem_arrayN_xyz_frame.
    rewrite H4.
    omega.

    step.
    (* off out of bounds *)
    apply emp_star_r.
    apply list2nmem_array.

    (* len = 0 *)
    step.
    apply emp_star_r.
    apply list2nmem_array.
  Qed.
  Proof.
    unfold update_bytes.
    time step. (* 40s *)
    inversion H6 as [allbytes Hrepconj].
    inversion Hrepconj as [Hbytes_rep Hrepconj']; clear Hrepconj.
    inversion Hbytes_rep as [Hrecrep Hallbytes_goodSize].
    (* TODO: replace this with filelen f *)
    set (flen := # (INODE.ISize (BFILE.BFAttr f))) in *.

    time step. (* 50s *)
    - instantiate (Fx0 := (Fx * arrayN flen
        (skipn flen allbytes))%pred).
      rewrite <- firstn_skipn with (l := allbytes) (n := flen) at 2.
      replace (firstn flen allbytes).
      replace flen with (length bytes) at 1.
      apply list2nmem_arrayN_app with (l' := skipn flen allbytes) in H5.
      pred_apply; cancel.
      cancel.
    - reflexivity.
    - unfold BFileRec.hidden.
      rewrite Rec.array_of_word_length with (ft := byte_type).
      auto.
    - unfold BFileRec.hidden in *.
      fold byte in *.
      step.
      * unfold rep.
        exists ilist'.
        split; [|split]; eauto.
        split; auto.
        eapply wordToNat_natToWord_bound.
        eapply BFileRec.bfrec_bound with (itemtype := byte_type); eauto.
        split.
        subst.
        apply firstn_length_l.
        replace (length ilist').
        replace (BFILE.BFAttr f').
        apply firstn_length_l_iff; auto.
        replace (length ilist').
        replace (BFILE.BFAttr f').
        auto.
      * replace (BFILE.BFAttr f').
        apply firstn_length_l_iff in H10.
        fold flen.
        match goal with
        | [ H : _ (list2nmem ilist') |- _ ] => rename H into Hilist'
        end.
        rewrite <- firstn_skipn with (l := ilist') (n := flen) in Hilist'.
        assert (length (firstn flen ilist') = flen) as Hflen.
        apply firstn_length_l; omega.

        eapply pimpl_apply in Hilist'; [|apply sep_star_abc_to_acb].
        rewrite <- Hflen in Hilist' at 1.
        assert (Htails_eq := Hilist').
        apply list2nmem_arrayN_end_eq in Htails_eq; auto.
        rewrite Htails_eq in Hilist'.
        apply list2nmem_arrayN_app_iff in Hilist'.
        assumption.
        exact ($ 0).
        autorewrite with lengths; omega.
    - (* no-op case len = 0 *)
      step.
      assert (olddata = nil) by (apply length_nil; omega).
      subst olddata.
      simpl.
      pred_apply; cancel.
  Qed.
   Proof.
     unfold grow_file, rep, bytes_rep.
     time step. (* 30s *)
     step.
     time step. (* 10s *)

     fold (filelen f) in *.
     instantiate (Fi := arrayN 0 allbytes).
     apply list2nmem_array.
     apply firstn_length_l_iff in H6.
     unfold ge.
     fold (filelen f) in H10.
     fold byte.
     replace (length allbytes).
     fold (roundup (filelen f) valubytes).
     rewrite block_items_ok.
     apply roundup_mono.
     apply Nat.lt_le_incl.
     unfold filelen.
     apply lt_word_lt_nat; auto.

     assert (filelen f < newlen) as Hnewlen.
     apply lt_word_lt_nat; auto.
     assert (Hflenround := roundup_valu_ge (filelen f)).
     assert (Hnewlenround := roundup_valu_ge newlen).
     assert (roundup (filelen f) valubytes <= roundup newlen valubytes) as
      Hnewlen_round.
     apply roundup_mono; omega.
     assert (filelen f <= length allbytes) as Hflen_all.
     replace (length allbytes).
     apply roundup_valu_ge.
     assert (Init.Nat.min (filelen f) (length allbytes) =
      filelen f) as Hlen_all_min.
     apply Nat.min_l; auto.

     step.
     time step. (* 60s *)
     step.

     time step. (* 80s *)
     fold (filelen f) in *.
     apply firstn_length_l_iff in H6.
     instantiate (Fx0 := arrayN 0 (firstn (filelen f) allbytes)).
     instantiate (olddata0 := skipn (filelen f) (allbytes ++ a7)).
     replace (firstn (filelen f) allbytes) with
      (firstn (filelen f) (allbytes ++ a7)) at 1.
     apply list2nmem_arrayN_firstn_skipn.
     apply firstn_app_l; omega.
     reflexivity.
     unfold BFileRec.hidden.
     fold (filelen f).
     assert (Hlen := Rec.array_of_word_length
      byte_type (roundup newlen valubytes - filelen f) ($ 0)).
     simpl in Hlen.
     fold byte in *.
     rewrite Hlen; clear Hlen.
     fold (filelen f) in *.
     assert (length (allbytes ++ a7) = roundup newlen valubytes)
      as Hallbytes'len.
     rewrite app_length.
     replace (length a7).
     unfold alloc_items.
     rewrite block_items_ok.
     replace (length allbytes).
     fold (roundup (filelen f) valubytes).
     omega.
     rewrite skipn_length.
     omega.
     omega.
     fold (filelen f).
     omega.

     step.
     time step. (* 15s *)
     apply pimpl_or_r; right.
     cancel.
     fold (filelen f) in *.
     rewrite wordToNat_natToWord_idempotent'; auto.
     exists (firstn (filelen f) allbytes ++
      repeat $0 (roundup newlen valubytes - filelen f)).
     assert (ilist' =
      firstn (filelen f) allbytes ++
      repeat $ (0) (roundup newlen valubytes - filelen f)) as Hilist'.
     eapply pimpl_apply in H25.
     eapply list2nmem_array_eq in H25.
     replace ilist'.
     reflexivity.
     rewrite Rec.of_word_zero_list.
     replace (@Rec.of_word byte_type $0) with
      (natToWord 8 0) by reflexivity.
     apply arrayN_combine.
     rewrite firstn_length_l by auto.
     reflexivity.
     fold (roundup newlen valubytes).
     autorewrite with lengths.
     rewrite Hlen_all_min.
     rewrite <- Hilist'.
     intuition.

     apply wordToNat_natToWord_idempotent'.
     replace (filelen f + (roundup newlen valubytes - filelen f))
      with (length ilist').
     eapply goodSize_bound.
     eapply BFileRec.bfrec_bound with (itemtype := byte_type); eauto.
     replace ilist'.
     autorewrite with lengths.
     omega.
     replace ilist'.
     (* split repeat into two parts - those that bring the length up to newlen,
        and then the rest that make it roundup newlen *)
     replace (roundup newlen valubytes - filelen f) with
      (newlen - filelen f + (roundup newlen valubytes - newlen)) by omega.
     rewrite <- repeat_app.
     rewrite app_assoc.
     rewrite firstn_app_l by (autorewrite with lengths; omega).
     rewrite firstn_oob by (autorewrite with lengths; omega).
     reflexivity.

     step.
     step.

     assert (filelen f = newlen) as Hflen.
     case_eq (wlt_dec (INODE.ISize (BFILE.BFAttr f)) ($ (newlen))); intros.
     contradiction.
     assert (filelen f >= newlen).
     erewrite <- wordToNat_natToWord_idempotent'; eauto.
     unfold filelen.
     apply le_word_le_nat.
     rewrite natToWord_wordToNat.
     auto.
     omega.
     apply pimpl_or_r; right.
     cancel.
     unfold filelen.
     rewrite natToWord_wordToNat.
     instantiate (fdata' := (BFILE.BFData f)).
     destruct f.
     destruct BFAttr.
     auto.
     exists allbytes.
     fold (filelen f).
     rewrite minus_diag.
     simpl.
     rewrite app_nil_r.
     rewrite wordToNat_natToWord_idempotent'
      with (n := filelen f) by auto.
     auto.

   Grab Existential Variables.
   all: try exact nil.
   all: try exact emp.
   exact BFILE.bfile0.
  Qed.
  Proof.
    unfold append, write_bytes.
    time step. (* 50s *)
    inversion H7 as [allbytes Hrepconj].
    inversion Hrepconj as [Hbytes_rep Hrepconj']; clear Hrepconj.
    inversion Hrepconj' as [Hbytes Hrepconj'']; clear Hrepconj'.
    inversion Hrepconj'' as [Hbyteslen Hallbyteslen]; clear Hrepconj''.
    inversion Hbytes_rep as [Hrecrep Hallbytes_goodSize].
    fold (filelen f) in *.
    assert (filelen f <= length allbytes).
    rewrite <- Hallbyteslen.
    apply roundup_valu_ge.

    step.
    time step. (* 10s *)

    unfold filelen.
    auto.

    step.
    time step. (* 165s -> 7.5s !!! *)
    step.
    time step. (* 165s -> 13s *)

    instantiate (Fx0 := (Fi * arrayN (filelen f) (repeat $0 (off - filelen f)))%pred).
    instantiate (olddata0 := repeat $0 len).
    fold (filelen f) in *.
    eapply pimpl_apply with (p := (Fi *
      arrayN (filelen f) (repeat $0 (off + len - filelen f)))%pred).
    cancel.
    replace (off + len - filelen f) with (off - filelen f + len) by omega.
    rewrite <- repeat_app.
    apply arrayN_combine.
    rewrite repeat_length.
    omega.
    replace (filelen f) at 1.
    apply list2nmem_arrayN_app.
    auto.

    autorewrite with lengths.
    reflexivity.

    time step. (* 15s *)
    step.
    (* just the first part of step *)
    eapply pimpl_ok2; eauto with prog.
    intros; norm; [cancel|].
    subst.
    (* we derive len = 0 before step creates several subgoals. *)
    assert (filelen f >= off + len).
    apply not_wlt_ge in H15.
    apply le_word_le_nat'; auto.
    assert (len = 0) by omega.
    subst len.
    intuition; eauto.
    instantiate (Fx0 := Fi).
    instantiate (olddata0 := nil).
    pred_apply; cancel.
    auto.

    time step.
    eapply pimpl_or_r; right; cancel; eauto.
    (* there are no zeroes, since we're appending nothing *)
    replace (off - filelen f) with 0 by omega.
    pred_apply; cancel.

    Grab Existential Variables.
    all: auto.
  Qed.