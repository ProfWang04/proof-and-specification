Proof.
  destruct a.
  destruct b; destruct b0; destruct b1; destruct b2;
  destruct b3; destruct b4; destruct b5; destruct b6; reflexivity.
Qed.
Proof.
  intros.
  shatter_word b.
  destruct x; destruct x0; destruct x1; destruct x2;
  destruct x3; destruct x4; destruct x5; destruct x6; reflexivity.
Qed.
Proof.
  reflexivity.
Qed.
Proof.
  induction nbytes; simpl; intros.
  rewrite word0. reflexivity.
  rewrite byte2ascii2byte. rewrite IHnbytes. rewrite combine_split. reflexivity.
Qed.
Proof.
  induction nbytes; simpl; intros.
  destruct s; simpl in *; congruence.
  destruct s; simpl in *; try congruence.
  rewrite split1_combine.
  rewrite split2_combine.
  rewrite IHnbytes by congruence.
  rewrite ascii2byte2ascii.
  reflexivity.
Qed.
Proof.
  induction nbytes; simpl; eauto.
Qed.
Proof.
  induction nbytes; simpl.
  reflexivity.
  destruct s; simpl; eauto.
Qed.
Proof.
  induction nbytes; simpl; intros.
  destruct s; simpl in *; try congruence; omega.
  destruct s; simpl in *; try congruence.
  inversion H0.
  destruct (ascii_dec a zero); try congruence.
  rewrite IHnbytes; eauto.
  omega.
Qed.
Proof.
  intros.
  inversion H; clear H; try congruence.
  clear H1 s0.
  inversion H0; clear H0; subst.
  induction s; simpl.
  reflexivity.
  inversion H1; subst.
  f_equal.
  apply IHs; auto.
Qed.
Proof.
  induction s; intros; subst; simpl in *.
  reflexivity.
  destruct (ascii_dec a zero); subst.
  - f_equal.
    rewrite <- pad_zero_string; auto.
  - inversion H0.
    inversion H; congruence.
    rewrite IHs; auto.
Qed.
Proof.
  unfold string2name.
  induction nbytes; simpl; eauto.
  intros.
  destruct s; simpl.
  - clear IHnbytes.
    induction nbytes; simpl.
    rewrite ascii2byte_zero; reflexivity.
    rewrite IHnbytes.
    rewrite ascii2byte_zero.
    repeat match goal with
    | [ |- context[natToWord ?len 0] ] => replace (natToWord len 0) with (wzero len) by reflexivity
    end.
    rewrite combine_wzero.
    reflexivity.
  - f_equal; eauto.
Qed.
Proof.
  unfold string2name, name2string.
  intros.
  rewrite padstring2name2padstring by apply string_pad_length.
  rewrite string_pad_unpad; eauto.
Qed.
Proof.
  unfold string2name, name2string.
  intros.
  rewrite string_unpad_pad; auto.
  rewrite name2padstring2name; auto.
  apply name2padstring_length.
Qed.
Proof.
  induction n; simpl; intros; constructor; auto.
Qed.
Proof.
  induction s; destruct nbytes eqn:Hn; simpl; intros.
  repeat constructor.
  repeat constructor.
  apply zerostring_pad_empty.
  repeat constructor.
  apply WFScons.
  apply IHs.
  omega.
  inversion H0; auto.
  inversion H0; auto.
Qed.
Proof.
  intros.
  inversion H; auto.
  exfalso; apply H0.
  inversion H1; auto.
Qed.
Proof.
  induction nbytes; intros.
  constructor.
  simpl.
  destruct (ascii_dec (byte2ascii (split1 8 (nbytes * 8) s)) zero) eqn:Heq.
  constructor.
  apply NoZeroCons; auto.
  apply IHnbytes.
  simpl in H.
  eapply wellformedpadstring_inv; eauto.
Qed.
Proof.
  induction s; simpl; firstorder.
  destruct (ascii_dec a zero); simpl; omega.
Qed.
Proof.
  intros.
  erewrite <- name2padstring_length with (name := s).
  apply string_unpad_length.
Qed.
  Proof.
    intros; inversion H.
    constructor.
    apply name2padstring_unpad_length.
    apply wellformed_nozero; auto.
  Qed.
  Proof.
    intros; inversion H.
    constructor.
    unfold sname2wname.
    rewrite <- string2name_string2name'.
    unfold string2name.
    rewrite padstring2name2padstring.
    apply stringpad_wellformed; auto.
    apply string_pad_length.
  Qed.
  Proof.
    split; [split | split ].
    apply wname_valid_sname_valid; auto.
    unfold sname2wname; rewrite <- string2name_string2name'.
    apply name2string2name.
    inversion H; auto.
    apply sname_valid_wname_valid; auto.
    inversion H.
    unfold sname2wname; rewrite <- string2name_string2name'.
    apply string2name2string; auto.
  Qed.
  Proof.
    apply cond_inverse_sym.
    apply dirname_cond_inverse.
  Qed.
  Proof.
    eapply cond_inv2bij.
    apply dirname_cond_inverse.
  Qed.
  Proof.
    eapply cond_inv2bij.
    apply dirname_cond_inverse'.
  Qed.
  Proof.
    intros.
    destruct (dirname_cond_inverse) as [_ H'].
    cbv [cond_right_inverse cond_inverse] in *.
    edestruct H'; eauto.
  Qed.
  Proof.
    intros.
    destruct (dirname_cond_inverse) as [H' _].
    cbv [cond_left_inverse cond_inverse] in *.
    edestruct H'; eauto.
  Qed.
  Proof.
    induction s.
    intuition; constructor.

    simpl.
    destruct (ascii_dec a zero); split; intros.
    inversion H.
    inversion H.
    exfalso; auto.
    constructor; auto.
    apply IHs; auto.
    inversion H.
    apply IHs; auto.
  Qed.
  Proof.
    unfold is_valid_sname; intros.
    rewrite Bool.andb_true_iff.

    split; intros.
    destruct H.
    constructor.
    destruct (le_dec (length s) namelen); simpl; try congruence.
    apply is_nozero_nozero; auto.

    inversion H; split.
    apply is_nozero_nozero; auto.
    destruct (le_dec (length s) namelen); simpl; try congruence.
  Qed.
  Proof.
    induction s; simpl; intros; auto.
    split; try constructor; auto.
    destruct (ascii_dec a zero); subst; simpl; split; intros.
    constructor; apply IHs; auto.
    inversion H; apply IHs; auto.
    inversion H.
    inversion H; exfalso.
    apply n; auto.
  Qed.
  Proof.
    generalize namelen.
    induction n; intros; simpl.
    split; repeat constructor.

    destruct (ascii_dec (byte2ascii (split1 8 (n * 8) w)) zero) eqn:Heq;
      simpl; split; try rewrite Heq; try rewrite e; intros; auto.
    repeat constructor.
    apply is_zerostring_zerostring; auto.
    inversion H; inversion H0; try congruence.
    apply is_zerostring_zerostring; auto.
    apply WFScons; auto.
    apply IHn; auto.
    apply IHn.
    eapply wellformedpadstring_inv; eauto.
  Qed.
  Proof.
    split; intros.
    constructor; apply is_valid_wname_valid'; auto.
    inversion H; apply is_valid_wname_valid'; auto.
  Qed.
  Proof.
    intros.
    destruct (is_valid_wname (name2padstring namelen w)) eqn:Heq.
    left; apply is_valid_wname_valid; auto.
    right; intro; contradict Heq.
    apply is_valid_wname_valid in H; congruence.
  Qed.
  Proof.
    intros.
    destruct (is_valid_sname s) eqn:Heq.
    left; apply is_valid_sname_valid; auto.
    right; intro; contradict Heq.
    apply is_valid_sname_valid in H; congruence.
  Qed.
  Proof.
    unfold rep, mem_atrans; intros.
    repeat deex.
    pose proof (DIR.rep_mem_eq H1 H3); subst.
    apply functional_extensionality; intro s.
    destruct (sname_valid_dec s).

    replace s with (wname2sname (sname2wname s)).
    rewrite <- H7. rewrite <- H4. auto.
    eapply cond_inv_domain_right with (f' := sname2wname); eauto.
    eapply cond_inv_domain_right with (f' := sname2wname); eauto.
    eapply cond_inv_rewrite_right; eauto.

    assert (notindomain s m1).
    destruct (indomain_dec s m1); eauto.
    apply H5 in i; congruence.
    assert (notindomain s m2).
    destruct (indomain_dec s m2); eauto.
    apply H2 in i; congruence.
    congruence.
  Qed.
  Proof.
    unfold lookup.
    hoare.

    or_l; cancel.
    resolve_valid_preds.
    eapply mem_atrans_inv_notindomain; eauto.

    or_r; cancel.
    resolve_valid_preds.
    eapply mem_atrans_inv_ptsto; eauto.

    or_l; cancel.
    resolve_valid_preds; auto.
    apply notindomain_not_indomain; auto.
  Qed.
  Proof.
    induction l; simpl; intros.
    eapply mem_atrans_emp; eauto.

    unfold readmatch at 1, readdir_trans at 1; simpl.
    apply mem_except_ptsto; auto.
    eapply mem_atrans_indomain; eauto.
    eapply sep_star_ptsto_indomain; eauto.
    eapply ptsto_valid; eauto.

    apply sep_star_ptsto_indomain in LP as Hx.
    eapply ptsto_mem_except in LP.
    eapply IHl; eauto.
    apply OK in Hx.
    eapply mem_atrans_mem_except; eauto.

    intros; apply OK.
    eapply indomain_mem_except_indomain; eauto.
    intros; apply OK2.
    eapply indomain_mem_except_indomain; eauto.
  Qed.
  Proof.
    unfold readdir.
    safestep. eauto.
    step.
    eapply readdir_trans_addr_ok; eauto.
  Qed.
  Proof.
    unfold unlink.
    hoare; resolve_valid_preds.

    subst; eexists.
    split; [ eauto | split ]; [ intros ? Hx | split; [ intros ? Hx | ] ].
    apply indomain_mem_except_indomain in Hx; auto.
    apply indomain_mem_except_indomain in Hx; auto.
    eapply mem_ainv_mem_except; eauto.
    apply mem_except_notindomain.
    eapply mem_atrans_inv_indomain; eauto.

    rewrite <- notindomain_mem_eq.
    subst; eexists.
    apply notindomain_not_indomain; eauto.
    apply notindomain_not_indomain; eauto.
  Qed.
  Proof.
    intros. intros m H'.
    replace m with dmap in * by eauto using DIR.rep_mem_eq.
    rewrite is_valid_sname_valid in *.
    eapply sname_valid_wname_valid in H as ?.
    eapply mem_atrans_inv_notindomain; eauto.
    eauto using mem_atrans_cond_inv.
  rewrite wname2sname_sname2wname; auto.
  Qed.
  Proof.
    unfold link.
    hoare.
    eauto using link_dir_rep_pimpl_notindomain.

    or_r; resolve_valid_preds; cancel.
    subst; eexists.
    split; [ eauto | split ]; [ intros ? Hx | split; [ intros ? Hx | ] ].
    destruct (weq w (sname2wname name)); subst.
    eapply cond_inv_domain_right with (PA := wname_valid); eauto.
    apply indomain_upd_ne in Hx; auto.
    destruct (string_dec s name); subst; auto.
    apply indomain_upd_ne in Hx; auto.

    eapply mem_ainv_mem_upd; eauto.
    apply ptsto_upd_disjoint; auto.
    eauto. eauto.
  Qed.
  Proof.
    unfold rep.
    exists empty_mem.
    intuition.
    apply DIR.bfile0_empty.
    inversion H; discriminate.
    inversion H; discriminate.
    firstorder.
  Qed.
  Proof.
    unfold rep. intros. repeat deex.
    unfold indomain in *.
    assert (sname_valid name) by eauto.
    erewrite <- wname2sname_sname2wname with (name := name) in H0 by eauto.
    rewrite <- H4 in *.
    eauto using DIR.rep_no_0_inum.
    eauto using sname_valid_wname_valid.
  Qed.
  Proof.
    intros.
    apply eq_sym.
    eapply rep_mem_eq; eauto.

    unfold rep in *; intros.
    repeat deex.
    assert (dmap0 = dmap).
    eapply DIR.crash_eq; eauto.
    subst.
    eexists; intuition; eauto.
  Qed.
  Proof.
    unfold rep; intros.
    repeat deex.
    eexists; intuition eauto.
    eapply DIR.crash_rep; eauto.
  Qed.