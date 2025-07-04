Lemma compute_xparams_ok : forall data_bitmaps inode_bitmaps log_descr_blocks magic,
    goodSize addrlen magic ->
    goodSize addrlen (1 +
          data_bitmaps * valulen +
          inode_bitmaps * valulen / INODE.IRecSig.items_per_val +
          inode_bitmaps + data_bitmaps + data_bitmaps +
          1 + log_descr_blocks + log_descr_blocks * PaddedLog.DescSig.items_per_val) ->
    fs_xparams_ok (compute_xparams data_bitmaps inode_bitmaps log_descr_blocks magic).
  Proof.
    unfold fs_xparams_ok.
    unfold log_xparams_ok, inode_xparams_ok, balloc_xparams_ok.
    unfold compute_xparams; simpl.
    intuition.
    all: eapply goodSize_trans; try eassumption.
    all: lia.
  Qed.
Lemma S_minus_1_helper : forall n a b,
    S (n + 1 + a + b) - 1 - n = S (a + b).
  Proof.
    intros; omega.
  Qed.

  Lemma S_minus_1_helper2 : forall n,
    S n - 1 = n.
  Proof.
    intros; omega.
  Qed.


  Ltac equate_log_rep :=
    match goal with
    | [ r : BFILE.memstate,
        H : context [ compute_xparams ?a1 ?a2 ?a3 ?a4 ],
        Hi: context [IAlloc.Alloc.rep _ _ _ _ ?x_]
        |- LOG.rep ?xp ?F ?d ?ms _ _ =p=> LOG.rep ?xp' ?F' ?d' ?ms' _ _ * _ ] =>
        equate d d'; equate ms' (MSLL (
        BFILE.mk_memstate (MSAlloc r) ms (MSAllocC r) (IAlloc.MSCache x_) (MSICache r) (MSCache r) (MSDBlocks r)
        ));
        equate xp' (FSXPLog (compute_xparams a1 a2 a3 a4))
    | [ r : BFILE.memstate,
        H : context [ compute_xparams ?a1 ?a2 ?a3 ?a4 ]
        |- LOG.rep ?xp ?F ?d ?ms _ _ =p=> LOG.rep ?xp' ?F' ?d' ?ms' _ _ * _ ] =>
        equate d d'; equate ms' (MSLL (
        BFILE.mk_memstate (MSAlloc r) ms (MSAllocC r) (IAlloc.Alloc.freelist0) (MSICache r) (MSCache r) (MSDBlocks r)
        ));
        equate xp' (FSXPLog (compute_xparams a1 a2 a3 a4))
    end.

  Theorem mkfs_ok : forall cachesize data_bitmaps inode_bitmaps log_descr_blocks,
    {!!< disk,
     PRE:vm,hm
       arrayS 0 disk *
       [[ cachesize <> 0 /\ data_bitmaps <> 0 /\ inode_bitmaps <> 0 ]] *
       [[ data_bitmaps <= valulen * valulen /\ inode_bitmaps <= valulen * valulen ]] *
       [[ length disk = 1 +
          data_bitmaps * valulen +
          inode_bitmaps * valulen / INODE.IRecSig.items_per_val +
          inode_bitmaps + data_bitmaps + data_bitmaps +
          1 + log_descr_blocks + log_descr_blocks * PaddedLog.DescSig.items_per_val ]] *
       [[ goodSize addrlen (length disk) ]]
     POST:vm',hm' RET:r exists ms fsxp d sm,
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL ms) sm hm' *
       [[ vm' = vm ]] *
       ( [[ isError r ]] \/ exists ilist frees,
         [[ r = OK (ms, fsxp) ]] *
         [[[ d ::: rep fsxp emp (TreeDir (FSXPRootInum fsxp) nil) ilist frees ms sm ]]] )
     CRASH:hm'
       any
     >!!} mkfs cachesize data_bitmaps inode_bitmaps log_descr_blocks.
  Proof.
    unfold mkfs.
    safestep.

    prestep.
    norml; unfold stars; simpl.
    denote! (arrayS _ _ _) as Hx.
    eapply arrayN_isolate_hd in Hx.
    unfold ptsto_subset in Hx at 1.
    safecancel.
    apply compute_xparams_ok.
    apply SB.goodSize_magic_number.
    denote (length disk = _) as Heq; rewrite Heq in *; auto.
    auto.

    (* LOG.init *)
    prestep. norm. cancel.
    intuition simpl. pred_apply.
    (* split LHS into log region and data region *)
    erewrite arrayN_split at 1.
    simpl.
    rewrite sep_star_comm.
    apply sep_star_assoc.

    rewrite skipn_length.
    setoid_rewrite skipn_length with (n := 1).
    substl (length disk).
    apply S_minus_1_helper.

    rewrite firstn_length.
    setoid_rewrite skipn_length with (n := 1).
    substl (length disk).
    rewrite Nat.min_l.
    rewrite Nat.sub_0_r; auto.
    rewrite S_minus_1_helper2.
    generalize (data_bitmaps * valulen + inode_bitmaps * valulen / INODE.IRecSig.items_per_val); intros.
    generalize (log_descr_blocks * PaddedLog.DescSig.items_per_val); intros.
    omega.

    eapply goodSize_trans; [ | eauto ].
    rewrite skipn_length.
    setoid_rewrite skipn_length with (n := 1).
    substl (length disk).
    generalize (data_bitmaps * valulen + inode_bitmaps * valulen / INODE.IRecSig.items_per_val); intros.
    generalize (log_descr_blocks * PaddedLog.DescSig.items_per_val); intros.
    omega.
    auto.
    auto.
    step.
    rewrite Nat.sub_0_r in *.

    (* BFILE.init *)
    step.

    (* IAlloc.alloc *)
    step.
    step.
    step.
    step.

    (* LOG.flushsync *)
    step.
    step.

    rewrite latest_pushd.
    equate_log_rep.
    cancel. or_r.
    unfold rep. cancel.

    denote (_ =p=> freeinode_pred) as Hy.
    denote (freeinode_pred =p=> _) as Hz.

    rewrite <- Hy in Hz.
    2: apply repeat_length with (x := BFILE.bfile0).


    assert (1 < length (repeat BFILE.bfile0 (inode_bitmaps * valulen
       / INODE.IRecSig.items_per_val * INODE.IRecSig.items_per_val))) as Hlen.
    rewrite repeat_length; omega.

    specialize (Hz _ (list2nmem_array _)).
    pred_apply; cancel.
    pose proof (list2nmem_ptsto_cancel BFILE.bfile0 _ Hlen).
    unfold tree_dir_names_pred.
    cancel.
    unfold BFILE.freepred in *. subst.
    apply DirTreePred.SDIR.bfile0_empty.
    apply emp_empty_mem.
    eapply Forall_repeat.
    eauto.

    (* failure cases *)
    apply pimpl_any.
    step.
    step.
    step.
    equate_log_rep.
    cancel.
    or_l; cancel.

    apply pimpl_any.
    step.
    step.
    equate_log_rep.
    cancel.
    or_l; cancel.

    apply pimpl_any.
    step.
    equate_log_rep.
    cancel.
    or_l; cancel.

    all: try solve [ try xcrash; apply pimpl_any ].
    substl (length disk).
    apply gt_Sn_O.

  Unshelve.
    all: try easy.
    try exact ($0, nil).
  Qed.
Theorem recover_ok : forall cachesize,
    {< fsxp cs ds,
     PRE:hm
       LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs hm *
       [[ cachesize <> 0 ]]
     POST:hm' RET:r exists ms fsxp',
       [[ fsxp' = fsxp ]] * [[ r = OK (ms, fsxp') ]] *
       exists d n sm, [[ n <= length (snd ds) ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL ms) sm hm' *
       [[ sm = sm_synced ]] *
       [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]] *
       [[ BFILE.MSinitial ms ]]
     XCRASH:hm'
       LOG.before_crash (FSXPLog fsxp) (SB.rep fsxp) ds hm'
     >} recover cachesize.
  Proof.
    unfold recover, LOG.after_crash; intros.
    eapply pimpl_ok2; monad_simpl.
    eapply BUFCACHE.init_recover_ok.
    intros; norm. cancel.
    intuition simpl. eauto.

    prestep. norml.
    denote ((crash_xform _) d') as Hx.
    apply crash_xform_sep_star_dist in Hx.
    rewrite SB.crash_xform_rep in Hx.
    rewrite LOG.after_crash_idem' in Hx; eauto.
    destruct_lift Hx; denote (crash_xform (crash_xform _)) as Hx.
    apply crash_xform_idem_l in Hx.

    norm. cancel.
    intuition.
    pred_apply.
    apply sep_star_comm; eauto.

    step.
    prestep. norm. cancel.
    unfold LOG.after_crash; norm. cancel.
    intuition simpl.
    pred_apply; norml.
    unfold stars; simpl.

    norm. cancel.
    rewrite LOG.rep_inner_hashmap_subset.
    eassign (SB.rep fsxp).
    cancel.
    or_l; cancel.
    auto.
    intuition simpl; eauto.
    safecancel.
    rewrite LOG.rep_inner_hashmap_subset.
    or_r; cancel.
    auto.
    eauto.
    auto.
    intuition.

    step.
 
    prestep. norm.
    2: intuition idtac.
    cancel.
    intuition simpl; eauto.
    intuition simpl; eauto.
    intuition simpl; eauto.

    xcrash.

    eapply LOG.crash_xform_cached_before; eauto.

    xcrash.

    denote (SB.rep) as Hsb. rewrite SB.rep_magic_number in Hsb. destruct_lift Hsb.

    step.

    xcrash.
    unfold LOG.before_crash.
    denote or as Hor; apply sep_star_or_distr in Hor.
    destruct Hor as [ Hor | Hor ];
    rewrite LOG.rep_inner_hashmap_subset in Hor; eauto.

    rewrite LOG.rep_inner_notxn_pimpl in Hor.
    destruct_lift Hor.
    norm. cancel.
    intuition.
    pred_apply.
    safecancel.

    rewrite LOG.rep_inner_rollbacktxn_pimpl in Hor.
    norm. cancel.
    intuition.
    pred_apply.
    safecancel.

    xcrash.
    unfold LOG.before_crash.
    denote or as Hor; apply sep_star_or_distr in Hor.
    destruct Hor as [ Hor | Hor ];
    rewrite LOG.rep_inner_hashmap_subset in Hor; eauto.

    rewrite LOG.rep_inner_notxn_pimpl in Hor.
    destruct_lift Hor.
    norm. cancel.
    intuition.
    pred_apply.
    safecancel.

    rewrite LOG.rep_inner_rollbacktxn_pimpl in Hor.
    norm. cancel.
    intuition.
    pred_apply.
    safecancel.
    Unshelve. all: eauto.
  Qed.

  Hint Extern 1 ({{_}} Bind (recover _) _) => apply recover_ok : prog.

  Ltac recover_ro_ok := intros;
    repeat match goal with
      | [ |- forall_helper _ ] => unfold forall_helper; intros; eexists; intros
      | [ |- corr3 ?pre' _ _ ] => eapply corr3_from_corr2_rx; eauto with prog
      | [ |- corr3 _ _ _ ] => eapply pimpl_ok3; intros
      | [ |- corr2 _ _ ] => step
      | [ H: crash_xform ?x =p=> ?x |- context [ crash_xform ?x ] ] => rewrite H
      | [ H: diskIs _ _ |- _ ] => unfold diskIs in *
      | [ |- pimpl (crash_xform _) _ ] => progress autorewrite with crash_xform
    end.

  Hint Extern 0 (okToUnify (LOG.idempred _ _ _ _) (LOG.idempred _ _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (LOG.after_crash _ _ _ _ _) (LOG.after_crash _ _ _ _ _)) => constructor : okToUnify.


  (* Specs and proofs *)

  Theorem file_getattr_ok : forall fsxp inum mscs,
  {< ds sm pathname Fm Ftop tree f ilist frees,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
         [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
         [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
  POST:hm' RET:^(mscs',r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
         [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]] *
         [[ r = DFAttr f /\ MSAlloc mscs' = MSAlloc mscs /\ MSCache mscs' = MSCache mscs ]]
  CRASH:hm'
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
  >} file_get_attr fsxp inum mscs.
  Proof.
    unfold file_get_attr; intros.
    step.
    safestep.
    safestep.
    eassumption.
    eapply pimpl_ok2; monad_simpl.
    apply LOG.commit_ro_ok.
    cancel.
    step.
    step.
    cancel.
    subst; pimpl_crash; cancel.
    rewrite LOG.notxn_intact. rewrite LOG.intact_idempred. reflexivity.
    rewrite LOG.intact_idempred.
    pimpl_crash; cancel.
    pimpl_crash. norml. clear H. safecancel.
    rewrite LOG.notxn_intact. rewrite LOG.intact_idempred. reflexivity.
    Unshelve. all: exact tt.
  Qed.

  Hint Extern 1 ({{_}} Bind (file_get_attr _ _ _) _) => apply file_getattr_ok : prog.

  Theorem file_get_sz_ok : forall fsxp inum mscs,
  {< ds sm pathname Fm Ftop tree f ilist frees,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
         [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
         [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
  POST:hm' RET:^(mscs',r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
         [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]] *
         [[ r = INODE.ABytes (DFAttr f) /\ MSAlloc mscs' = MSAlloc mscs ]]
  CRASH:hm'
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
  >} file_get_sz fsxp inum mscs.
  Proof.
    unfold file_get_sz; intros.
    step.
    step.
    step.
    step.
    Unshelve. all: exact tt.
  Qed.

  Hint Extern 1 ({{_}} Bind (file_get_sz _ _ _) _) => apply file_get_sz_ok : prog.

  Ltac xcrash_solve :=
    repeat match goal with
      | [ H: forall _ _ _,  _ =p=> (?crash _) |- _ =p=> (?crash _) ] => eapply pimpl_trans; try apply H; cancel
      | [ |- crash_xform (LOG.rep _ _ _ _ _ _) =p=> _ ] => rewrite LOG.notxn_intact; cancel
      | [ H: crash_xform ?rc =p=> _ |- crash_xform ?rc =p=> _ ] => rewrite H; xform_norm
    end.


  (* Dumb and fast version of intuition *)
  Ltac intuition' :=
    match goal with
    | [|- _ /\ _]  => split; intuition'
    | [|- True] => auto
    | _ => idtac
  end.

  (* Try to simplify a pimpl with idempred on the left side. *)
  Ltac simpl_idempred_l :=
    simpl;
    repeat xform_dist;
    repeat xform_deex_l;
    xform_dist;
    rewrite crash_xform_lift_empty;
    norml; unfold stars; simpl;
    match goal with
    | [ H: crash_xform ?x =p=> crash_xform _ |- context[crash_xform ?x] ] => rewrite H
    end;
    repeat xform_dist;
    try rewrite sep_star_or_distr;
    rewrite LOG.crash_xform_idempred.

  (* Try to simplify a pimpl with idempred on the right side. *)
  Ltac simpl_idempred_r :=
      recover_ro_ok;
      (norml; unfold stars; simpl);
      (norm'r; unfold stars; simpl);
      try (cancel);
      intuition';
      repeat xform_dist;
      repeat rewrite crash_xform_idem.


  Theorem read_fblock_ok : forall fsxp inum off mscs,
    {< ds sm Fm Ftop tree pathname f Fd vs ilist frees,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
           [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
           [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
           [[[ (DFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs', r)
           LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
           [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]] *
           [[ r = fst vs /\ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} read_fblock fsxp inum off mscs.
  Proof.
    unfold read_fblock; intros.
    step.
    safestep.
    safestep.
    all: try eassumption.
    eapply pimpl_ok2; monad_simpl.
    apply LOG.commit_ro_ok.
    cancel.
    step.
    step.
    pimpl_crash; cancel.
    rewrite LOG.notxn_intact.
    apply LOG.intact_idempred.
    pimpl_crash; cancel.
    apply LOG.intact_idempred.
    pimpl_crash. norml. clear H. cancel.
    apply LOG.notxn_idempred.
    Unshelve. all: exact tt.
  Qed.


  Hint Extern 1 ({{_}} Bind (read_fblock _ _ _ _) _) => apply read_fblock_ok : prog.

  Theorem file_set_attr_ok : forall fsxp inum attr mscs,
  {< ds sm pathname Fm Ftop tree f ilist frees,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
         [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
         [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
  POST:hm' RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      ([[ isError ok  ]] *
       (LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
        [[ BFILE.mscs_same_except_log mscs mscs' ]] *
        [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]]) \/
      ([[ ok = OK tt  ]] * exists d tree' f' ilist',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') sm hm' *
        [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees mscs' sm)]]] *
        [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
        [[ f' = mk_dirfile (DFData f) attr ]] *
        [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                        ilist' (BFILE.pick_balloc frees  (MSAlloc mscs')) tree' ]] *
        [[ BFILE.treeseq_ilist_safe inum ilist ilist' ]])
     )
  XCRASH:hm'
    LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
    exists d tree' f' ilist' mscs',
    [[ MSAlloc mscs' = MSAlloc mscs ]] *
    LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) hm' *
    [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees mscs' sm)]]] *
    [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
    [[ f' = mk_dirfile (DFData f) attr ]] *
    [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                    ilist' (BFILE.pick_balloc frees  (MSAlloc mscs')) tree' ]] *
    [[ BFILE.treeseq_ilist_safe inum ilist ilist' ]]
  >} file_set_attr fsxp inum attr mscs.
  Proof.
    unfold file_set_attr; intros.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    or_l; cancel.
    unfold BFILE.mscs_same_except_log; intuition.
    xcrash_solve.
    xcrash_solve.
    {
      rewrite LOG.recover_any_idempred; cancel.
      or_r; cancel.
      xform_norm; cancel.
      xform_norm; cancel.
      xform_norm; cancel.
      xform_norm; cancel.
      xform_norm; safecancel.
      2: reflexivity.
      eauto.
    }
    xcrash_solve.
    rewrite LOG.intact_idempred. xform_norm. cancel.
    xcrash_solve.
    rewrite LOG.intact_idempred. xform_norm. cancel.
  Qed.


  Hint Extern 1 ({{_}} Bind (file_set_attr _ _ _ _) _) => apply file_set_attr_ok : prog.

  Theorem file_truncate_ok : forall fsxp inum sz mscs,
    {< ds sm Fm Ftop tree pathname f ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:hm' RET:^(mscs', r)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
         ([[ isError r ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
          [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]] \/
      [[ r = OK tt ]] * exists d tree' f' ilist' frees',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') sm hm' *
        [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm)]]] *
        [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
        [[ f' = mk_dirfile (setlen (DFData f) sz ($0, nil)) (DFAttr f) ]] *
        [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                        ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
        [[ sz >= Datatypes.length (DFData f) -> BFILE.treeseq_ilist_safe inum ilist ilist' ]] )
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      exists d tree' f' ilist' frees' mscs',
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) hm' *
      [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm)]]] *
      [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
      [[ f' = mk_dirfile (setlen (DFData f) sz ($0, nil)) (DFAttr f) ]] *
      [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                        ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
      [[ sz >= Datatypes.length (DFData f) -> BFILE.treeseq_ilist_safe inum ilist ilist' ]]
    >} file_truncate fsxp inum sz mscs.
  Proof.
    unfold file_truncate; intros.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    xcrash_solve.
    {
      or_r; cancel.
      rewrite LOG.recover_any_idempred.
      xform_normr.
      safecancel.
      eauto.
    }
    step.
    step.
    xcrash_solve.
    rewrite LOG.intact_idempred. xform_norm. cancel.
    xcrash_solve.
    rewrite LOG.intact_idempred. xform_norm. cancel.
    xcrash_solve.
    rewrite LOG.intact_idempred. xform_norm. cancel.
  Unshelve.
    all: easy.
  Qed.

  Hint Extern 1 ({{_}} Bind (file_truncate _ _ _ _) _) => apply file_truncate_ok : prog.


  Ltac latest_rewrite := unfold latest, pushd; simpl.

  Theorem update_fblock_d_ok : forall fsxp inum off v mscs,
    {< ds sm Fm Ftop tree pathname f Fd vs frees ilist,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs')
      exists tree' f' ds' sm' bn,
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       [[ ds' = dsupd ds bn (v, vsmerge vs) ]] *
       [[ BFILE.block_belong_to_file ilist bn inum off ]] *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ MSCache mscs' = MSCache mscs ]] *
       [[ MSAllocC mscs' = MSAllocC mscs ]] *
       [[ MSIAllocC mscs' = MSIAllocC mscs ]] *
       (* spec about files on the latest diskset *)
       [[[ ds'!! ::: (Fm  * rep fsxp Ftop tree' ilist frees mscs' sm') ]]] *
       [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
       [[[ (DFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]] *
       [[ DFAttr f' = DFAttr f ]] *
       [[ dirtree_safe ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree
                       ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree' ]]
    XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
       exists bn, [[ BFILE.block_belong_to_file ilist bn inum off ]] *
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (dsupd ds bn (v, vsmerge vs)) hm'
   >} update_fblock_d fsxp inum off v mscs.
  Proof.
    unfold update_fblock_d; intros.
    step.
    step.
    prestep.
    (* extract dset_match from (rep ds), this is useful for proving crash condition *)
    rewrite LOG.active_dset_match_pimpl at 1.
    norm. cancel.
    xcrash_solve.
    intuition.
    latest_rewrite.
    pred_apply; cancel.
    eauto.
    eauto.
    safestep.
    step.
    step.
    xcrash_solve.

    - xform_normr; cancel.
      or_r; xform_normr; cancel.
      apply LOG.notxn_idempred.
      eauto.

    - cancel.
      repeat xcrash_rewrite.
      xform_norm.
      rewrite LOG.recover_any_idempred.
      or_l; cancel.
      rewrite LOG.recover_any_idempred.
      or_r; cancel; xform_normr; cancel.

    - cancel.
      repeat xcrash_rewrite.
      xform_norm; cancel.
      rewrite LOG.notxn_intact, LOG.intact_idempred.
      xform_normr; cancel.
    Unshelve.
      all: easy.
  Qed.

  Hint Extern 1 ({{_}} Bind (update_fblock_d _ _ _ _ _) _) => apply update_fblock_d_ok : prog.


  Theorem file_sync_ok: forall fsxp inum mscs,
    {< ds sm Fm Ftop tree pathname f ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:hm' RET:^(mscs')
      exists ds' sm' tree' al,
        [[ MSAlloc mscs = MSAlloc mscs' ]] *
        [[ MSCache mscs = MSCache mscs' ]] *
        [[ MSAllocC mscs = MSAllocC mscs' ]] *
        [[ MSIAllocC mscs = MSIAllocC mscs' ]] *
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
        [[ ds' = dssync_vecs ds al]] *
        [[ length al = length (DFData f) /\ forall i, i < length al ->
              BFILE.block_belong_to_file ilist (selN al i 0) inum i ]] *
        [[[ ds'!! ::: (Fm * rep fsxp Ftop tree' ilist frees mscs' sm')]]] *
        [[ tree' = update_subtree pathname (TreeFile inum  (synced_dirfile f)) tree ]] *
        [[ dirtree_safe ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree
                        ilist (BFILE.pick_balloc frees (MSAlloc mscs')) tree' ]]
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
   >} file_sync fsxp inum mscs.
  Proof.
    unfold file_sync; intros.
    step.
    step.
    prestep; norm. cancel. intuition.
    latest_rewrite.
    pred_apply; cancel.
    eauto.
    step.
    step.
    step.
    - xcrash_solve.
      rewrite <- crash_xform_idem.
      rewrite LOG.crash_xform_intact_dssync_vecs_idempred.
      rewrite SB.crash_xform_rep.
      xcrash.
    - xcrash_solve.
      rewrite LOG.recover_any_idempred.
      xcrash.
    - xcrash_solve.
      rewrite LOG.intact_idempred.
      xcrash.
    Unshelve.
      all: constructor.
  Qed.

  Hint Extern 1 ({{_}} Bind (file_sync _ _ _) _) => apply file_sync_ok : prog.


  Theorem tree_sync_ok: forall fsxp  mscs,
    {< ds sm Fm Ftop tree ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]] 
    POST:hm' RET:^(mscs')
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (ds!!, nil)) (MSLL mscs') sm hm' *
      [[ MSAlloc mscs' = negb (MSAlloc mscs) ]] *
      [[ MSCache mscs' = MSCache mscs ]] *
      [[ MSICache mscs' = MSICache mscs ]] *
      [[ MSAllocC mscs' = MSAllocC mscs ]] *
      [[ MSIAllocC mscs' = MSIAllocC mscs ]] *
      [[ MSDBlocks mscs' = MSDBlocks mscs ]]
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
   >} tree_sync fsxp mscs.
  Proof.
    unfold tree_sync; intros.
    step.
    step using auto.
    step.
    step.
    xcrash_solve.
    rewrite LOG.recover_any_idempred.
    cancel.
  Unshelve.
    all: constructor.
  Qed.

  Hint Extern 1 ({{_}} Bind (tree_sync _ _) _) => apply tree_sync_ok : prog.

  Theorem tree_sync_noop_ok: forall fsxp  mscs,
    {< ds sm Fm Ftop tree ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]]
    POST:hm' RET:^(mscs')
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
      [[ MSAlloc mscs' = negb (MSAlloc mscs) ]]
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
   >} tree_sync_noop fsxp mscs.
  Proof.
    unfold tree_sync_noop; intros.
    step.
    step.
    xcrash_solve.
    rewrite LOG.recover_any_idempred.
    cancel.
  Qed.

  Hint Extern 1 ({{_}} Bind (tree_sync_noop _ _) _) => apply tree_sync_noop_ok : prog.


  Theorem lookup_ok: forall fsxp dnum fnlist mscs,
    {< ds sm Fm Ftop tree ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
      [[ dirtree_inum tree = dnum]] *
      [[ dirtree_isdir tree = true ]]
    POST:hm' RET:^(mscs', r)
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]] *
      [[ (isError r /\ None = find_name fnlist tree) \/
         (exists v, r = OK v /\ Some v = find_name fnlist tree)%type ]] *
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]]
    CRASH:hm'  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
     >} lookup fsxp dnum fnlist mscs.
  Proof.
    unfold lookup; intros.
    step.
    step.
    (* `step` here is really slow *)
    prestep. cancel.
    eapply pimpl_ok2; monad_simpl.
    apply LOG.commit_ro_ok.
    cancel.
    step.
    step.
    subst; pimpl_crash; cancel.
    apply LOG.notxn_idempred.
    step.
    step.
    cancel. apply LOG.notxn_idempred.
    cancel. apply LOG.intact_idempred.
    cancel. apply LOG.notxn_idempred.
  Unshelve.
    all: constructor.
  Qed.

  Hint Extern 1 ({{_}} Bind (lookup _ _ _ _) _) => apply lookup_ok : prog.

  Theorem create_ok : forall fsxp dnum name mscs,
    {< ds sm pathname Fm Ftop tree tree_elem ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
      [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs',r)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      ([[ isError r ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
       [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]]
      \/ exists inum,
       [[ r = OK inum ]] * exists d tree' ilist' frees',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') sm hm' *
       [[ tree' = tree_graft dnum tree_elem pathname name (TreeFile inum dirfile0) tree ]] *
       [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
       [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                       ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]])
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      exists d inum tree' ilist' frees' mscs',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) hm' *
      [[ tree' = tree_graft dnum tree_elem pathname name (TreeFile inum dirfile0) tree ]] *
      [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
      [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                       ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
      [[ MSAlloc mscs' = MSAlloc mscs ]]
    >} create fsxp dnum name mscs.
  Proof.
    unfold create; intros.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    xcrash_solve.
    or_r; cancel.
    repeat (cancel; progress xform_norm).
    safecancel.
    2: reflexivity. cancel.
    rewrite LOG.recover_any_idempred; cancel.
    pred_apply; cancel.
    auto.
    auto.
    step.
    step.
    xcrash_solve. xform_norm. or_l. rewrite LOG.intact_idempred. cancel.
    xcrash_solve. xform_norm. or_l. rewrite LOG.intact_idempred. cancel.
    xcrash_solve. xform_norm. or_l. rewrite LOG.intact_idempred. cancel.
  Unshelve.
    all: constructor.
  Qed.

  Hint Extern 1 ({{_}} Bind (create _ _ _ _ ) _) => apply create_ok : prog.



  Theorem rename_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
    {< ds sm Fm Ftop tree cwd tree_elem ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
      [[ find_subtree cwd tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
         ([[ isError ok ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]] \/
      [[ ok = OK tt ]] * 
        rename_rep ds mscs' sm Fm fsxp Ftop tree tree_elem ilist frees cwd dnum srcpath srcname dstpath dstname hm')
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      exists d tree' srcnum srcents dstnum dstents subtree pruned renamed ilist' frees' mscs',
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) hm' *
      rename_rep_inner d frees' ilist' tree' srcnum srcents subtree pruned dstnum dstents renamed mscs' sm Fm fsxp Ftop tree tree_elem ilist frees cwd dnum srcpath srcname dstpath dstname
    >} rename fsxp dnum srcpath srcname dstpath dstname mscs.
  Proof.
    unfold rename, rename_rep, rename_rep_inner; intros.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    xcrash. or_r. cancel.
    repeat (cancel; progress xform_norm).
    safecancel.
    rewrite LOG.recover_any_idempred. cancel.
    2: pred_apply; cancel.
    all: eauto.
    step.
    step.
    xcrash. or_l. rewrite LOG.notxn_idempred. cancel.
    xcrash. or_l. rewrite LOG.intact_idempred. cancel.
    xcrash. or_l. rewrite LOG.notxn_idempred. cancel.
  Unshelve.
    all: constructor.
  Qed.

  Hint Extern 1 ({{_}} Bind (rename _ _ _ _ _ _ _) _) => apply rename_ok : prog.


  Theorem delete_ok : forall fsxp dnum name mscs,
    {< ds sm pathname Fm Ftop tree tree_elem frees ilist,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm) ]]] *
      [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs', ok)
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     ([[ isError ok ]] *
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
                [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs' sm) ]]] \/
      [[ ok = OK tt ]] * exists d tree' ilist' frees',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') sm hm' *
        [[ tree' = update_subtree pathname
                      (delete_from_dir name (TreeDir dnum tree_elem)) tree ]] *
        [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
        [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                        ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
        [[ forall inum def', inum <> dnum -> In inum (tree_inodes tree) ->
           In inum (tree_inodes tree') ->
           selN ilist inum def' = selN ilist' inum def' ]])
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      exists d tree' ilist' frees' mscs',
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) hm' *
      [[ tree' = update_subtree pathname
                    (delete_from_dir name (TreeDir dnum tree_elem)) tree ]] *
      [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
      [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                      ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]] *
      [[ forall inum def', inum <> dnum ->
           (In inum (tree_inodes tree') \/ (~ In inum (tree_inodes tree))) ->
          selN ilist inum def' = selN ilist' inum def' ]]
    >} delete fsxp dnum name mscs.
  Proof.
    unfold delete; intros.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    xcrash. or_r.
    repeat (cancel; progress xform_norm).
    safecancel. rewrite LOG.recover_any_idempred. cancel.
    3: pred_apply; cancel.
    all: eauto.
    step.
    step.
    xcrash. or_l. rewrite LOG.notxn_idempred. cancel.
    xcrash. or_l. rewrite LOG.intact_idempred. cancel.
    xcrash. or_l. rewrite LOG.notxn_idempred. cancel.
  Unshelve.
    all: constructor.
  Qed.

  Hint Extern 1 ({{_}} Bind (delete _ _ _ _) _) => apply delete_ok : prog.

End AFS.
