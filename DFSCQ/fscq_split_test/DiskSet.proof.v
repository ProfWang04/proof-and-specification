Proof.
  unfold dsupd; intros.
  rewrite d_map_latest; auto.
Qed.
Proof.
  unfold dsupd; intros.
  rewrite d_map_fst; auto.
Qed.
Proof.
  unfold dsupd; intros.
  rewrite d_map_nthd; auto.
Qed.
Proof.
  unfold dssync; intros.
  rewrite d_map_latest; auto.
Qed.
Proof.
  unfold dssync; intros.
  rewrite d_map_nthd; auto.
Qed.
Proof.
  unfold dsupd_vecs; intros.
  rewrite d_map_latest; auto.
Qed.
Proof.
  unfold dsupd_vecs; intros.
  rewrite d_map_nthd; auto.
Qed.
Proof.
  unfold dsupd_vecs; intros.
  simpl; auto.
Qed.
Proof.
  unfold dssync_vecs; intros.
  rewrite d_map_latest; auto.
Qed.
Proof.
  unfold dssync_vecs; intros.
  rewrite d_map_nthd; auto.
Qed.
Proof.
  intros; rewrite dssync_latest.
  unfold vssync; rewrite length_updN; auto.
Qed.
Proof.
  intros; rewrite dsupd_latest.
  rewrite length_updN; auto.
Qed.
Proof.
  intros; rewrite dsupd_vecs_latest.
  rewrite vsupd_vecs_length; auto.
Qed.
Proof.
  intros; rewrite dssync_vecs_latest.
  rewrite vssync_vecs_length; auto.
Qed.
Proof.
  unfold nthd; intuition; simpl.
  destruct n.
  rewrite Nat.sub_0_r; auto.
  destruct (length ds - n) eqn:?.
  omega.
  replace (length ds - S n) with n0 by omega; auto.
Qed.
Proof.
  unfold dssync_vecs, d_map.
  intros.
  destruct vs; cbn; f_equal.
  eapply vssync_vecs_nop.
  rewrite Forall_forall in *.
  intuition.
  unfold ds_synced in *.
  specialize (H x); intuition.
  inversion H1; auto.
  rewrite <- map_id.
  eapply map_ext_in.
  rewrite Forall_forall in *.
  unfold ds_synced in *.
  intuition; cbn in *.
  eapply vssync_vecs_nop.
  rewrite Forall_forall.
  intros x; specialize (H x); intuition.
  rewrite Forall_forall in *.
  cbn in *; intuition.
Qed.
Proof.
  unfold dssync, d_map.
  destruct d; cbn -[vssync]; intros.
  f_equal.
  rewrite vssync_comm.
  auto.
  repeat rewrite map_map.
  eapply map_ext_in; intros.
  rewrite vssync_comm; auto.
Qed.
Proof.
  unfold dssync_vecs, dssync.
  intros.
  cbn.
  destruct vs; unfold d_map; cbn.
  f_equal.
  rewrite map_map.
  auto.
Qed.
Proof.
  induction l; cbn; intros.
  repeat rewrite dssync_vecs_nop by constructor.
  auto.
  repeat rewrite dssync_vecs_cons.
  rewrite dssync_comm.
  rewrite IHl.
  auto.
Qed.
Proof.
  induction l; cbn.
  rewrite dssync_vecs_nop; auto.
  constructor.
  intros.
  repeat rewrite dssync_vecs_cons.
  repeat rewrite dssync_vecs_dssync_comm.
  congruence.
Qed.
Proof.
  intros.
  induction H; cbn; auto.
  repeat rewrite ?dssync_vecs_cons, ?dssync_vecs_dssync_comm.
  f_equal; auto.
  repeat rewrite ?dssync_vecs_cons.
  rewrite dssync_comm.
  reflexivity.
  congruence.
Qed.
  Proof.
    induction 1; simpl; firstorder.
  Qed.
  Proof.
    induction 1; simpl in *; intros; firstorder.
    rewrite <- IHReplaySeq; firstorder.
  Qed.
  Proof.
    induction n; simpl; intros; auto.
    destruct ds.
    apply repaly_seq_latest in H; rewrite <- H.
    destruct l; intuition.
    pose proof (replay_seq_length H).
    inversion H; auto; subst; simpl in *.
    specialize (IHn (d0, ds0)).
    apply IHn; simpl; auto; omega.
  Qed.
  Proof.
    unfold nthd; intros.
    destruct n; simpl.
    rewrite selN_oob, skipn_oob by omega; auto.
    erewrite <- replay_seq_length by eauto.
    destruct (lt_dec (length (snd ds)) (S n)).
    replace (length (snd ds) - S n) with 0 by omega; simpl.
    rewrite <- repaly_seq_latest by auto.
    unfold latest; destruct ds; simpl.
    destruct l0; firstorder.
    apply replay_seq_selN; auto; omega.
  Qed.
  Proof.
    induction l; simpl; auto; intros.
    rewrite replay_disk_length; auto.
  Qed.
  Proof.
    intros.
    erewrite repaly_seq_latest; eauto.
    rewrite fold_right_replay_disk_length; auto.
  Qed.
  Proof.
    intros.
    erewrite replay_seq_nthd; eauto.
    rewrite fold_right_replay_disk_length; auto.
  Qed.
  Proof.
    induction 1; intros.
    constructor.
    inversion H1; subst.
    unfold dsupd, d_map; simpl.
    constructor.
    rewrite <- replay_disk_updN_comm by auto.
    destruct ds; auto.
    apply IHReplaySeq; auto.
  Qed.
  Proof.
    induction 1; simpl; subst.
    constructor.
    unfold dsupd, d_map; simpl.
    constructor.
    2: apply IHReplaySeq; auto.
    destruct ds; simpl;
    rewrite replay_disk_updN_comm by auto;
    rewrite replay_disk_ents_remove_updN; auto.
  Qed.
  Proof.
    induction 1; intros.
    constructor.
    unfold dssync, d_map; simpl.
    constructor.
    2: apply IHReplaySeq; auto.
    destruct ds; subst; simpl;
    rewrite replay_disk_vssync_comm_list; auto.
  Qed.
  Proof.
    induction 1; intros.
    constructor.
    inversion H1; subst.
    unfold dsupd_vecs, d_map; simpl.
    constructor; auto.
    rewrite replay_disk_vsupd_vecs_disjoint by auto.
    destruct ds; auto.
  Qed.
  Proof.
    induction 1; intros.
    constructor.
    inversion H1; subst.
    unfold dssync_vecs, d_map; simpl.
    constructor; auto.
    rewrite replay_disk_vssync_vecs_disjoint by auto.
    destruct ds; auto.
  Qed.
  Proof.
    induction 1; simpl; subst.
    constructor.
    unfold dssync_vecs, d_map; simpl.
    constructor.
    2: apply IHReplaySeq; auto.
    destruct ds; simpl;
    rewrite <- replay_disk_vssync_vecs_comm_list; auto.
  Qed.
Proof.
  intros p p' Hp ds ds' Hds Hpd.
  unfold diskset_pred in *; subst; eauto.
Qed.
Proof.
  intros p p' Hp ds ds' Hds Hpd.
  unfold diskset_pred in *; subst; eauto.
Qed.
Proof.
  intros p p' Hp ds ds' Hds Hpd.
  inversion Hp.
  unfold diskset_pred in *; subst; eauto.
Qed.
Proof.
  intros p p' Hp ds ds' Hds Hpd.
  inversion Hp.
  unfold diskset_pred in *; subst; eauto.
Qed.
Proof.
  unfold diskset_pred; intros.
  apply d_in_d_map in H1; deex.
  eauto.
Qed.