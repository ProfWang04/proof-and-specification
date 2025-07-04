  Proof.
    unfold namei.
    step.

    (* Prove loop entry: fndone = nil *)
    rewrite app_nil_l; eauto.
    pred_apply; cancel.
    reflexivity.

    assert (tree_names_distinct tree).
    eapply rep_tree_names_distinct with (m := list2nmem m).
    pred_apply. unfold rep. cancel.

    (* Lock up the initial memory description, because our memory stays the
     * same, and without this lock-up, we end up with several distinct facts
     * about the same memory.
     *)

    all: denote! (_ (list2nmem m)) as Hm0; rewrite <- locked_eq in Hm0.

    destruct_branch.
    step.

    (* isdir = true *)
    destruct tree0; simpl in *; subst; intuition.
    step.
    denote (tree_dir_names_pred) as Hx.
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    safestep; eauto.

    (* Lock up another copy of a predicate about our running memory. *)
    denote! (_ (list2nmem m)) as Hm1; rewrite <- locked_eq in Hm1.
    denote (dirlist_pred) as Hx; assert (Horig := Hx).
    destruct_branch.

    (* dslookup = Some _: extract subtree before [cancel] *)
    prestep.
    norml; unfold stars; simpl; inv_option_eq; msalloc_eq.
    destruct a2.

    (* subtree is a directory *)
    rewrite tree_dir_extract_subdir in Hx by eauto; destruct_lift Hx.
    norm. cancel. intuition simpl.
    rewrite cons_app. rewrite app_assoc. reflexivity.

    3: pred_apply; cancel.
    pred_apply; cancel.
    eapply pimpl_trans; [ eapply pimpl_trans | ].
    2: eapply subtree_absorb with
          (xp := fsxp) (fnlist := fndone) (tree := tree)
          (subtree := TreeDir n l0) (subtree' := TreeDir n l0); eauto.
    simpl; unfold tree_dir_names_pred; cancel; eauto.

    rewrite update_subtree_same; eauto.

    eapply pimpl_trans.
    eapply subtree_extract with
          (xp := fsxp) (fnlist := fndone ++ [elem])
          (subtree := TreeDir a1 dummy5).

    erewrite find_subtree_app by eauto.
    eauto.
    reflexivity.

    pred_apply; cancel.

    auto. auto.
    rewrite cons_app. rewrite app_assoc.
    erewrite find_subtree_app. reflexivity.
    erewrite find_subtree_app by eauto. eauto.
    erewrite find_subtree_app by eauto. eauto.
    eauto.

    (* subtree is a file *)
    rewrite tree_dir_extract_file in Hx by eauto. destruct_lift Hx.
    norm; unfold stars; simpl. cancel.
    intuition idtac.
    rewrite cons_app. rewrite app_assoc. reflexivity.
    3: pred_apply; cancel.
    pred_apply; cancel.
    eassign (TreeFile a1 dummy5).
    3: auto. 3: auto.

    eapply pimpl_trans; [ eapply pimpl_trans | ].
    2: eapply subtree_absorb with
          (xp := fsxp) (fnlist := fndone) (tree := tree)
          (subtree := TreeDir n l0) (subtree' := TreeDir n l0); eauto.
    simpl; unfold tree_dir_names_pred; cancel; eauto.

    rewrite update_subtree_same; eauto.

    eapply pimpl_trans.
    eapply subtree_extract with
          (xp := fsxp) (fnlist := fndone ++ [elem])
          (subtree := TreeFile a1 dummy5).

    erewrite find_subtree_app by eauto.
    eauto.
    reflexivity.

    pred_apply; cancel.

    rewrite cons_app. rewrite app_assoc.
    erewrite find_subtree_app. reflexivity.

    erewrite find_subtree_app by eauto. eauto.
    erewrite find_subtree_app by eauto. eauto.
    eauto.

    (* dslookup = None *)
    prestep. norm; msalloc_eq. cancel. intuition idtac.
    all: try solve [ exfalso; congruence ].
    rewrite cons_app. rewrite app_assoc. reflexivity.
    2: pred_apply; cancel.
    pred_apply; cancel.

    eapply pimpl_trans; [ | eapply pimpl_trans ].
    2: eapply subtree_absorb with (xp := fsxp) (fnlist := fndone) (tree := tree) (subtree' := TreeDir n l0).
    cancel. unfold tree_dir_names_pred. cancel; eauto.
    eauto. eauto. eauto.

    rewrite update_subtree_same by eauto. cancel.
    erewrite <- find_subtree_none; eauto.
    eauto.
    cancel.

    prestep. norm; msalloc_eq. cancel. intuition idtac.
    rewrite cons_app. rewrite app_assoc. reflexivity.
    all: try solve [ exfalso; congruence ].
    2: pred_apply; cancel.
    pred_apply; cancel.

    eapply pimpl_trans; [ | eapply pimpl_trans ].
    2: eapply subtree_absorb with (xp := fsxp) (fnlist := fndone) (tree := tree) (subtree' := tree0).
    cancel. eauto. eauto. eauto.
    rewrite update_subtree_same by eauto. cancel.
    denote (find_subtree) as Hx; rewrite Hx.
    destruct tree0; intuition.
    eauto.

    step.
    rewrite cons_app. rewrite app_assoc. reflexivity.

    (* Ret : OK *)
    assert (tree_names_distinct tree).
    eapply rep_tree_names_distinct with (m := locked (list2nmem m)).
    pred_apply. unfold rep. cancel.

    step; msalloc_eq.

    rewrite subtree_absorb.
    rewrite update_subtree_same.
    cancel.
    all: eauto.

    right; eexists; intuition.
    denote! (find_subtree (fndone ++ _) _ = _) as Hx.
    unfold find_name; rewrite Hx.
    destruct tree0; reflexivity.

    left; intuition.
    denote (find_subtree (fndone ++ _) _ = _) as Hx.
    unfold find_name; rewrite Hx; eauto.

    Grab Existential Variables.
    all: try exact unit.
    all: try exact None.
    all: intros; try exact tt.
    all: try congruence.
  Qed.
  Proof.
    unfold mkdir, rep.
    step.
    subst; simpl in *.
    denote tree_dir_names_pred as Hx;
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    unfold IAlloc.MSLog in *.
    step.
    eapply IAlloc.ino_valid_goodSize; eauto.
    destruct_branch; [ | step ].
    prestep; norml; inv_option_eq; msalloc_eq.

    cancel.
    match goal with a: IAlloc.Alloc.memstate |- _
      => destruct a; cbn in *; subst
    end.
    or_r; cancel.

    unfold tree_dir_names_pred at 1. cancel; eauto.
    denote (dummy1 =p=> _) as Hx. rewrite Hx.
    unfold tree_dir_names_pred; cancel.
    denote (BFILE.freepred _) as Hy. unfold BFILE.freepred in Hy. subst.
    apply SDIR.bfile0_empty.
    apply emp_empty_mem.
    apply sep_star_comm. apply ptsto_upd_disjoint. auto. auto.

    msalloc_eq.
    eapply dirlist_safe_mkdir; auto.

    Unshelve.
    all: try eauto; exact emp; try exact nil; try exact empty_mem; try exact BFILE.bfile0.
  Qed.
  Proof.
    intros; eapply pimpl_ok2. apply mkdir_ok'.
    unfold rep; cancel.
    rewrite subtree_extract; eauto. simpl. instantiate (tree_elem0 := tree_elem). cancel.
    step.
    apply pimpl_or_r; right. cancel.
    rewrite <- subtree_absorb; eauto.
    cancel.
    eapply dirlist_safe_subtree; eauto.
  Qed.
  Proof.
    unfold mkfile, rep.
    step.
    subst; simpl in *.

    denote tree_pred as Ht;
    rewrite subtree_extract in Ht; eauto.
    assert (tree_names_distinct (TreeDir dnum tree_elem)).
    eapply rep_tree_names_distinct with (m := list2nmem m).
    pred_apply; unfold rep; cancel.

    simpl in *.
    denote tree_dir_names_pred as Hx;
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    unfold IAlloc.MSLog in *.
    step.
    unfold SDIR.rep_macro.
    eapply IAlloc.ino_valid_goodSize; eauto.

    destruct_branch; [ | step ].
    prestep; norml; inv_option_eq.

    cancel.
    match goal with a: IAlloc.Alloc.memstate |- _
      => destruct a; cbn in *; subst
    end.
    msalloc_eq.
    or_r; cancel.
    eapply dirname_not_in; eauto.

    rewrite <- subtree_absorb; eauto.
    cancel.
    unfold tree_dir_names_pred.
    cancel; eauto.
    denote (dummy1 =p=> _) as Hx; rewrite Hx.
    unfold BFILE.freepred.
    rewrite dirlist_pred_split; simpl; cancel.
    apply tree_dir_names_pred'_app; simpl.
    apply sep_star_assoc; apply emp_star_r.
    apply ptsto_upd_disjoint; auto.

    eapply dirlist_safe_subtree; eauto.
    msalloc_eq.
    eapply dirlist_safe_mkfile; eauto.

    pred_apply.
    denote (dummy1 =p=> _) as Hx; rewrite Hx; unfold BFILE.freepred.
    cancel.

    eapply dirname_not_in; eauto.

    Unshelve.
    all: eauto.
  Qed.
  Proof.
    unfold mkfile; intros.
    eapply pimpl_ok2. apply mkfile_ok'.
    cancel.
    eauto.
    step.

    or_r; cancel.
    rewrite tree_graft_not_in_dirents; auto.
    rewrite <- tree_graft_not_in_dirents; auto.
  Qed.
  Proof.
    destruct x; tauto.
  Qed.
  Proof.
    destruct x; tauto.
  Qed.
  Proof.
    unfold delete, rep.

    (* extract some basic facts from rep *)
    intros; eapply pimpl_ok2; monad_simpl; eauto with prog; intros; norm'l.
    assert (tree_inodes_distinct (TreeDir dnum tree_elem)) as HiID.
    eapply rep_tree_inodes_distinct with (m := list2nmem m).
    pred_apply; unfold rep; cancel.
    assert (tree_names_distinct (TreeDir dnum tree_elem)) as HdID.
    eapply rep_tree_names_distinct with (m := list2nmem m).
    pred_apply; unfold rep; cancel.

    (* lookup *)
    subst; simpl in *.
    denote tree_dir_names_pred as Hx;
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    safecancel. 2: eauto.
    unfold SDIR.rep_macro.
    cancel; eauto.

    denote! (_ (list2nmem m)) as Hm0; rewrite <- locked_eq in Hm0.
    step.
    step.
    step.

    (* unlink *)
    step.

    (* is_file: prepare for reset *)
    prestep. norml.
    denote dirlist_pred as Hx.
    erewrite dirlist_extract with (inum := a0) in Hx; eauto.
    destruct_lift Hx.
    destruct dummy4; simpl in *; try congruence; subst.
    denote dirlist_pred_except as Hx; destruct_lift Hx; auto.
    cancel.

    (* is_file: prepare for free *)
    prestep. norml; msalloc_eq.
    denote dirlist_pred as Hx.
    erewrite dirlist_extract with (inum := n) in Hx; eauto.
    destruct_lift Hx.
    denote dirlist_pred_except as Hx; destruct_lift Hx; auto.
    unfold IAlloc.MSLog in *; cancel.
    match goal with H: (_ * ptsto ?a _)%pred ?m |- context [ptsto ?a]
      => exists m; solve [pred_apply; cancel]
    end.

    (* post conditions *)
    step.
    or_r; safecancel.
    denote (pimpl _ freepred') as Hx; rewrite <- Hx.
    rewrite dir_names_delete with (dnum := dnum); eauto.
    rewrite dirlist_pred_except_delete; eauto.
    cancel.
    eauto.
    apply dirlist_safe_delete; auto.

    (* inum inside the new modified tree *)
    denote! (tree_dir_names_pred' _ _) as Hy.
    eapply find_dirlist_exists in Hy as Hy'.
    deex.
    denote dirlist_combine as Hx.
    eapply tree_inodes_distinct_delete in Hx as Hx'; eauto.
    eassumption.

    (* inum outside the original tree *)
    denote! (forall _ _, (_ = _ -> False) -> _ = _) as Hz.
    eapply Hz.
    intro; subst.
    denote! (In _ _ -> False) as Hq.
    eapply Hq.
    denote ((name |-> (_, false))%pred) as Hy.
    eapply find_dirlist_exists in Hy as Hy'; eauto.
    deex.
    denote (dirtree_inum _ = dirtree_inum _ ) as Hd.
    rewrite Hd.
    eapply find_dirlist_tree_inodes; eauto.

    cancel.
    cancel.

    unfold IAlloc.MSLog in *; cancel.
    or_l. cancel.

    (* case 2: is_dir: check empty *)
    prestep.
    intros; norm'l.
    denote dirlist_pred as Hx; subst_bool.
    rewrite dirlist_extract_subdir in Hx; eauto; simpl in Hx.
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    cancel. eauto.

    step.
    step.
    step.
    step.
    step. msalloc_eq.
    cancel.
    exists (list2nmem flist'). eexists.
    pred_apply. cancel.
    unfold IAlloc.MSLog in *.
    step.

    (* post conditions *)
    or_r; cancel.
    denote (pimpl _ freepred') as Hx; rewrite <- Hx.
    denote (tree_dir_names_pred' _ _) as Hz.
    erewrite (@dlist_is_nil _ _ _ _ _ Hz); eauto.
    rewrite dirlist_pred_except_delete; eauto.
    rewrite dir_names_delete with (dnum := dnum).
    cancel. eauto. eauto. eauto.
    reflexivity.
    apply dirlist_safe_delete; auto.

    (* inum inside the new modified tree *)
    eapply find_dirlist_exists in H9 as H9'.
    deex.
    denote dirlist_combine as Hx.
    eapply tree_inodes_distinct_delete in Hx as Hx'; eauto.
    eassumption.

    (* inum outside the original tree *)
    denote (selN _ _ _ = selN _ _ _) as Hs.
    denote (In _ (dirlist_combine _ _)) as Hi.
    denote (tree_dir_names_pred' tree_elem) as Ht.
    apply Hs.
    intro; subst.
    eapply Hi.
    eapply find_dirlist_exists with (inum := a0) in Ht as Ht'.
    deex.
    eapply find_dirlist_tree_inodes; eauto.
    eassumption.

    step.
    step.
    cancel; auto.
    cancel; auto.

    Unshelve.
    all: try match goal with | [ |- DirTreePred.SDIR.rep _ _ ] => eauto end.
    all: try exact unit.
    all: try solve [repeat constructor].
    all: eauto.
    all: try exact string_dec.
  Qed.
  Proof.
    unfold read, rep.
    intros. prestep. norml.
    rewrite subtree_extract in * by eauto.
    cbn [tree_pred] in *. destruct_lifts.
    cancel.

    eapply list2nmem_inbound; eauto.
    step; msalloc_eq.
    cancel.

    rewrite <- subtree_fold by eauto.
    pred_apply. cancel.

    cancel; eauto.
  Qed.
  Proof.
    unfold dwrite, rep.
    intros. prestep. norml.
    rewrite subtree_extract in * by eauto.
    cbn [tree_pred] in *. destruct_lifts.
    cancel.
    eapply list2nmem_inbound; eauto.
    prestep. norm. cancel.
    intuition auto; msalloc_eq.
    pred_apply; cancel.

    rewrite <- subtree_absorb by eauto.
    cancel.
    auto.

    eapply dirlist_safe_subtree; eauto.
    apply dirtree_safe_file.
  Qed.
  Proof.
    unfold datasync, rep.
    intros. prestep. norml.
    rewrite subtree_extract in * by eauto.
    cbn [tree_pred] in *. destruct_lifts.
    cancel.
    step; msalloc_eq.
    cancel.

    rewrite <- subtree_absorb by eauto.
    pred_apply. cancel.

    eapply dirlist_safe_subtree; eauto.
    apply dirtree_safe_file.
  Qed.
  Proof.
    unfold sync, rep.
    hoare.
  Qed.
  Proof.
    unfold sync_noop, rep.
    hoare.
  Qed.
  Proof.
    unfold truncate, rep.
    intros. prestep. norml.
    rewrite subtree_extract in * by eauto.
    cbn [tree_pred] in *. destruct_lifts.
    cancel.
    step; msalloc_eq.
    or_r.
    cancel.
    rewrite <- subtree_absorb by eauto. cancel.

    eapply dirlist_safe_subtree; eauto.
    apply dirtree_safe_file_trans; auto.
  Qed.
  Proof.
    unfold getlen, rep.
    intros. prestep. norml.
    rewrite subtree_extract in * by eauto.
    cbn [tree_pred] in *. destruct_lifts.
    cancel.
    step; msalloc_eq.
    cancel.
    rewrite <- subtree_fold by eauto. pred_apply; cancel.
    cancel; eauto.
  Qed.
  Proof.
    unfold getattr, rep.
    intros. prestep. norml.
    rewrite subtree_extract in * by eauto.
    cbn [tree_pred] in *. destruct_lifts.
    cancel.
    step; msalloc_eq.
    cancel.
    rewrite <- subtree_fold by eauto. pred_apply; cancel.
    cancel; eauto.
  Qed.
  Proof.
    unfold setattr, rep.
    intros. prestep. norml.
    rewrite subtree_extract in * by eauto.
    cbn [tree_pred] in *. destruct_lifts.
    cancel.
    step; msalloc_eq.
    cancel.
    rewrite <- subtree_absorb by eauto.
    pred_apply; cancel.
    eapply dirlist_safe_subtree; eauto.
    apply dirtree_safe_file_trans; auto.
  Qed.
  Proof.
    intros; eapply pimpl_ok2. apply delete_ok'.

    intros; norml; unfold stars; simpl.
    rewrite rep_tree_distinct_impl in *.
    unfold rep in *; cancel.

    rewrite subtree_extract; eauto. simpl. instantiate (tree_elem0:=tree_elem). cancel.
    step.
    apply pimpl_or_r; right. cancel.
    rewrite <- subtree_absorb; eauto.
    cancel.
    eapply dirlist_safe_subtree; eauto.
    denote (dirlist_combine tree_inodes _) as Hx.
    specialize (Hx inum def' H4).
    intuition; try congruence.

    destruct_lift H0.
    edestruct tree_inodes_pathname_exists. 3: eauto.
    eapply tree_names_distinct_update_subtree; eauto.
    eapply tree_names_distinct_delete_from_list.
    eapply tree_names_distinct_subtree; eauto.

    eapply tree_inodes_distinct_update_subtree; eauto.
    eapply tree_inodes_distinct_delete_from_list.
    eapply tree_inodes_distinct_subtree; eauto.
    simpl. eapply incl_cons2.
    eapply tree_inodes_incl_delete_from_list.

    (* case A: inum inside tree' *)

    repeat deex.
    destruct (pathname_decide_prefix pathname x); repeat deex.

    (* case 1: in the directory *)
    erewrite find_subtree_app in *; eauto.
    eapply H11.

    eapply find_subtree_inum_present in H16; simpl in *.
    intuition. exfalso; eauto.

    (* case 2: outside the directory *)
    eapply H9.
    intro.
    edestruct tree_inodes_pathname_exists with (tree := TreeDir dnum tree_elem) (inum := dirtree_inum subtree).
    3: eassumption.

    eapply tree_names_distinct_subtree; eauto.
    eapply tree_inodes_distinct_subtree; eauto.

    destruct H20.
    destruct H20.

    eapply H6.
    exists x0.

    edestruct find_subtree_before_prune_general; eauto.

    eapply find_subtree_inode_pathname_unique.
    eauto. eauto.
    intuition eauto.
    erewrite find_subtree_app; eauto.
    intuition congruence.

    (* case B: outside original tree *)
    eapply H11; eauto.
    right.
    contradict H7; intuition eauto. exfalso; eauto.
    eapply tree_inodes_find_subtree_incl; eauto.
    simpl; intuition.
  Unshelve.
    all: eauto.
  Qed.
  Proof.
    unfold rename, rep.

    (* extract some basic facts *)
    prestep; norm'l.
    assert (tree_inodes_distinct (TreeDir dnum tree_elem)) as HnID.
    eapply rep_tree_inodes_distinct with (m := list2nmem m).
    pred_apply; unfold rep; cancel.
    assert (tree_names_distinct (TreeDir dnum tree_elem)) as HiID.
    eapply rep_tree_names_distinct with (m := list2nmem m).
    pred_apply; unfold rep; cancel.

    (* namei srcpath, isolate root tree file before cancel *)
    subst; simpl in *.
    denote tree_dir_names_pred as Hx; assert (Horig := Hx).
    unfold tree_dir_names_pred in Hx; destruct_lift Hx.
    cancel.

    (* BFILE.rep in post condition of namei doesn't unify with  BFILE.rep in context, 
       because namei may change cache content and promises a new BFILE.rep in its post
       condition, which we should use from now on. Should we clear the old BFILE.rep? *)
    denote! (_ (list2nmem m)) as Hm0; rewrite <- locked_eq in Hm0.

    instantiate (tree := TreeDir dnum tree_elem).
    unfold rep; simpl.
    unfold tree_dir_names_pred; cancel.
    all: eauto.

    (* lookup srcname, isolate src directory before cancel *)
    destruct_branch; [ | step ].
    destruct_branch; destruct_branch; [ | step ].

    prestep; norm'l.

    (* lock the old BFILE.rep again, but not the new one. *)
    denote! ( (Fm * BFILE.rep _ _ _ _ _ _ _ (MSCache mscs) _ _ * _)%pred (list2nmem m)) as Hm0; rewrite <- locked_eq in Hm0.

    intuition; inv_option_eq; repeat deex; destruct_pairs.
    denote find_name as Htree.
    apply eq_sym in Htree.
    apply find_name_exists in Htree.
    destruct Htree. intuition.

    denote find_subtree as Htree; assert (Hx := Htree).
    apply subtree_extract with (xp := fsxp) in Hx.
    denote tree_dir_names_pred as Hy; assert (Hsub := Hy).
    eapply pimpl_trans in Hsub; [ | | eapply pimpl_sep_star; [ apply pimpl_refl | apply Hx ] ];
      [ | cancel ]. clear Hx.
    destruct x; simpl in *; subst; try congruence.
    unfold tree_dir_names_pred in Hsub.
    destruct_lift Hsub.
    denote (_ |-> _)%pred as Hsub.

    safecancel.
    cancel. 2: eauto.

    (* unlink src *)
    step.

    (* lock an old BFILE.rep *)
    denote! ( ((Fm * BFILE.rep _ _ _ _ _ _ _ (MSCache a) _ _) * _)%pred (list2nmem m)) as Hm1; rewrite <- locked_eq in Hm1.

    (* namei for dstpath, find out pruning subtree before step *)
    denote (tree_dir_names_pred' l0 _) as Hx1.
    denote (_ |-> (_, _))%pred as Hx2.
    pose proof (ptsto_subtree_exists _ Hx1 Hx2) as Hx.
    destruct Hx; intuition.

    step; msalloc_eq.
    cancel.
    {
      cancel.
      match goal with |- context [(?inum_ |-> _)%pred] =>
        eapply pimpl_trans; [ eapply pimpl_trans; [ |
        eapply subtree_prune_absorb with (inum := inum_) (ri := dnum) (re := tree_elem) (xp := fsxp) (path := srcpath)
        ] | ]
      end.
      all: eauto using dir_names_pred_delete'.
      cancel.
    }
    rewrite tree_prune_preserve_inum; auto.
    rewrite tree_prune_preserve_isdir; auto.

    (* fold back predicate for the pruned tree in hypothesis as well  *)
    denote (list2nmem flist0) as Hinterm.
    apply helper_reorder_sep_star_2 in Hinterm.
    erewrite subtree_prune_absorb in Hinterm; eauto.
    2: apply dir_names_pred_delete'; auto.
    apply helper_reorder_sep_star_2 in Hinterm.
    rename x into mvtree.

    (* lookup dstname *)
    destruct_branch; [ | step ].
    destruct_branch; destruct_branch; [ | step ].

    (* lock an old BFILE.rep; we have a new one from namei *)
    denote! ( (_* BFILE.rep _ _ _ _ _ _ _ (MSCache a0) _ _)%pred (list2nmem m)) as Hm2; rewrite <- locked_eq in Hm2.

    prestep; norm'l.
    intuition; inv_option_eq; repeat deex; destruct_pairs.

    denote find_name as Hpruned.
    apply eq_sym in Hpruned.
    apply find_name_exists in Hpruned.
    destruct Hpruned. intuition.

    denote (list2nmem dummy9) as Hinterm1.
    denote find_subtree as Hpruned; assert (Hx := Hpruned).
    apply subtree_extract with (xp := fsxp) in Hx.
    assert (Hdst := Hinterm1); rewrite Hx in Hdst; clear Hx.
    destruct x; simpl in *; subst; try congruence; inv_option_eq.
    unfold tree_dir_names_pred in Hdst.
    destruct_lift Hdst.

    safecancel. eauto.

    denote! ( (Fm * _ * BFILE.rep _ _ _ _ _ _ _ (MSCache a4) _ _)%pred (list2nmem m')) as Hm3; rewrite <- locked_eq in Hm3.

    (* grafting back *)
    destruct_branch.

    (* case 1: dst exists, try delete *)
    prestep.
    norml; msalloc_eq.
    unfold stars; simpl; inv_option_eq.
    denote (tree_dir_names_pred' _ _) as Hx3.
    denote (_ |-> (_, _))%pred as Hx4.
    pose proof (ptsto_subtree_exists _ Hx3 Hx4) as Hx.
    destruct Hx; intuition.

    denote! ( ((Fm * BFILE.rep _ _ _ _ _ _ (MSAllocC a1) _ _ _) * _)%pred (list2nmem m')) as Hm4; rewrite <- locked_eq in Hm4.

    (* must unify [find_subtree] in [delete]'s precondition with
       the root tree node.  have to do this manually *)
    unfold rep; norm. cancel. intuition.
    pred_apply; norm. cancel. intuition.
    eassign (tree_prune v_1 l0 srcpath srcname (TreeDir dnum tree_elem)).
    (* it would have been nice if we could have used Hinterm, as the old
       proof did, but flist has changed because of caching, and we need to
       use the latest flist and fold things back together again. *)
    2: eauto.
    pred_apply.
    cancel.
    rewrite helper_reorder_sep_star_3.
    rewrite fold_back_dir_pred; eauto.
    rewrite helper_reorder_sep_star_4.
    rewrite subtree_fold; eauto. 
    cancel.

    (* now, get ready for link *)
    destruct_branch; [ | step ].
    prestep; norml; inv_option_eq; msalloc_eq.
    denote mvtree as Hx. assert (Hdel := Hx).
    setoid_rewrite subtree_extract in Hx at 2.
    2: subst; eapply find_update_subtree; eauto.
    simpl in Hx; unfold tree_dir_names_pred in Hx; destruct_lift Hx.

    denote! ( _ (list2nmem m')) as Hm5; rewrite <- locked_eq in Hm5.
    cancel.
    eauto.

    eapply tree_pred_ino_goodSize; eauto.

    pred_apply' Hdel; cancel.

    safestep; msalloc_eq.
    or_l; cancel.
    or_r; cancel; eauto.
    eapply subtree_graft_absorb_delete; eauto.
    msalloc_eq.
    eapply dirtree_safe_rename_dest_exists; eauto.

    (* case 1: in the new tree *)
    denote BFILE.treeseq_ilist_safe as Hsafe.
    unfold BFILE.treeseq_ilist_safe in Hsafe; destruct Hsafe as [Hsafe0 Hsafe1].
    rewrite <- Hsafe1 by auto.

    denote (selN ilist _ _ = selN ilist' _ _) as Hi.
    eapply Hi; eauto.

    eapply prune_graft_preserves_inodes; eauto.

    (* case 2: out of the original tree *)
    denote BFILE.treeseq_ilist_safe as Hsafe.
    unfold BFILE.treeseq_ilist_safe in Hsafe; destruct Hsafe as [Hsafe0 Hsafe1].
    rewrite <- Hsafe1 by auto.

    denote (selN ilist _ _ = selN ilist' _ _) as Hi.
    eapply Hi; eauto.
    right. intros HH.
    eapply tree_inodes_incl_delete_from_dir in HH; eauto.
    unfold tree_prune in *.
    cbn in *; intuition.

    cancel.

    (* dst is None *)
    safestep.
    safestep.
    eapply tree_pred_ino_goodSize; eauto.
    denote (_ (list2nmem flist1)) as H'.
    pred_apply' H'; cancel.   (* Hinterm as above *)

    safestep; msalloc_eq.
    or_l; cancel.
    or_r; cancel; eauto.

    rewrite helper_reorder_sep_star_5.
    eapply subtree_graft_absorb; eauto.
    msalloc_eq.
    eapply dirtree_safe_rename_dest_none; eauto.
    eapply notindomain_not_in_dirents; eauto.

    denote BFILE.treeseq_ilist_safe as Hsafe.
    unfold BFILE.treeseq_ilist_safe in Hsafe; destruct Hsafe as [Hsafe0 Hsafe1].
    apply Hsafe1; auto.

    denote BFILE.treeseq_ilist_safe as Hsafe.
    unfold BFILE.treeseq_ilist_safe in Hsafe; destruct Hsafe as [Hsafe0 Hsafe1].
    apply Hsafe1; auto.

    cancel.
    cancel; auto.

    cancel.
    Unshelve.
    all: try exact unit.
    all: try solve [repeat econstructor].
    all: try eauto.
    all: cbv [Mem.EqDec]; decide equality.
  Qed.
  Proof.
    intros; eapply pimpl_ok2. apply rename_cwd_ok.

    intros; norml; unfold stars; simpl.
    rewrite rep_tree_distinct_impl in *.
    unfold rep in *; cancel.
    rewrite subtree_extract; eauto. simpl. instantiate (tree_elem0:=tree_elem). cancel.
    step.
    apply pimpl_or_r; right. cancel; eauto.
    rewrite <- subtree_absorb; eauto.
    cancel.
    rewrite tree_graft_preserve_inum; auto.
    rewrite tree_prune_preserve_inum; auto.
    rewrite tree_graft_preserve_isdir; auto.
    rewrite tree_prune_preserve_isdir; auto.
    eapply dirlist_safe_subtree; eauto.

    denote! (((Fm * BFILE.rep _ _ _ _ _ _ _ _ _ _) * IAlloc.rep _ _ _ _ _)%pred _) as Hm'.
    eapply pimpl_apply in Hm'.
    eapply rep_tree_names_distinct in Hm' as Hnames.
    eapply rep_tree_inodes_distinct in Hm' as Hinodes.
    2: unfold rep; cancel.
    2: rewrite <- subtree_absorb.
    2: cancel. 2: apply pimpl_refl. 2: eauto.
    2: rewrite tree_graft_preserve_inum; auto.
    2: rewrite tree_prune_preserve_inum; auto.
    2: rewrite tree_graft_preserve_isdir; auto.
    2: rewrite tree_prune_preserve_isdir; auto.

    edestruct tree_inodes_pathname_exists. 3: eauto. all: eauto.
    repeat deex.
    destruct (pathname_decide_prefix pathname x); repeat deex.

    (* case 1: inum inside tree' *)
    erewrite find_subtree_app in *; eauto.

    (* case 2: inum outside tree' *)
    denote (selN ilist _ _ = selN ilist' _ _) as Hilisteq.
    eapply Hilisteq; eauto.
    right. intros.

    denote ([[ tree_names_distinct _ ]]%pred) as Hlift. destruct_lift Hlift.
    edestruct find_subtree_update_subtree_oob_general; eauto.
    edestruct tree_inodes_pathname_exists with (tree := TreeDir dnum tree_elem) (inum := dirtree_inum subtree0) as [pn_conflict ?].
    eapply tree_names_distinct_subtree; [ | eauto ]; eauto.
    eapply tree_inodes_distinct_subtree; [ | | eauto ]; eauto.
    simpl; intuition.

    denote! (exists _, find_subtree _ _ = _ /\ dirtree_inum _ = dirtree_inum _) as Hx.
    destruct Hx.

    denote! (~ (exists _, _ = _ ++ _)) as Hsuffix.
    eapply Hsuffix.
    exists pn_conflict.

    eapply find_subtree_inode_pathname_unique with (tree := tree).
    eauto. eauto.

    intuition eauto.
    erewrite find_subtree_app by eauto; intuition eauto.
    intuition congruence.

  Grab Existential Variables.
    all: try exact unit.
    all: intros; eauto using BFILE.MSIAlloc.
    all: try solve [do 5 econstructor].
    all: try (cbv [Mem.EqDec]; decide equality).
    all: try exact emp.
    all: intros; try exact True.
  Qed.