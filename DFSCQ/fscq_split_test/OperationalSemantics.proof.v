  Proof.
    unfold possible_sync; intros.
    destruct (AEQ a a0); subst; autorewrite with upd;
      intuition eauto.
    specialize (H a0); intuition auto.
    right; repeat eexists; eauto.
    repeat deex.
    right; repeat eexists; eauto.
  Qed.
  Proof.
    unfold possible_sync, sync_mem; intros.
    specialize (H a).
    destruct (m a) as [ [] | ];
    destruct (m' a) as [ [] | ];
      subst; intuition eauto;
      try congruence;
      repeat deex;
      inv_opt;
      right.
    do 3 eexists; intuition eauto.
  Qed.
  Proof.
    intros.
    inversion H0; subst; repeat sigT_eq; eauto.
    - exists m; intuition eauto.
      specialize (H a); intuition auto; repeat deex; try congruence.
      assert (v = v0) by congruence; subst.
      eauto.
    - pose proof (H a); intuition auto; try congruence.
      repeat deex.
      assert (v = v1) by congruence.
      assert (x = l') by congruence.
      subst.
      exists (upd m a (v0, v1::l)).
      intuition eauto.
    - pose proof (H a); intuition auto; try congruence.
      repeat deex.
      eauto.
      exists (upd m a vs').
      destruct vs'.
      intuition eauto.
  Qed.
Proof.
  split; induction 1; eauto.
Qed.
Proof.
  destruct out, out'; simpl; intuition idtac;
    repeat deex;
    match goal with
    | [ H: @eq (outcome _) _ _ |- _ ] => inversion H; subst
    end; eauto.
Qed.
Proof.
  destruct out; simpl; eauto.
Qed.
Proof.
  destruct out, out'; intros; simpl in *; repeat deex; try congruence; eauto.
  inversion H0; subst; eauto.
  inversion H0; subst; eauto.
Qed.
Proof.
  constructor; hnf; intros; eauto using outcome_obs_le_refl, outcome_obs_le_trans.
Qed.
Proof.
  unfold possible_sync; intros.
  specialize (H a); intuition eauto; try congruence.
  repeat deex.
  assert (v = v0) by congruence; subst.
  assert (l' = vs') by congruence; subst.
  eauto.
Qed.
Proof.
  intros.
  inversion H0; subst; repeat sigT_eq; eauto.
  - (* Read *)
    eapply possible_sync_in_domain in H10; eauto; deex.
    eauto.
  - eapply possible_sync_in_domain in H10; eauto; deex.
    eexists; split.
    constructor; eauto.
    eapply possible_sync_respects_upd; eauto.
  - destruct vs, vs'.
    eapply possible_sync_in_domain in H10; eauto; deex.
    eexists; split.
    econstructor; eauto.
    eapply possible_sync_respects_upd; eauto.
Qed.
Proof.
  unfold possible_sync; intros.
  specialize (H a); intuition eauto;
    repeat deex; congruence.
Qed.
Proof.
  inversion 1; intros; subst; repeat sigT_eq; eauto.
Qed.
Proof.
  intros.
  generalize dependent d.
  induction H; subst; intros; simpl.
  - eauto 10.
  - eauto 10.
  - eauto 10.
  - eauto 10.
  - eapply step_sync_later in H0; eauto; deex.
    eexists; intuition eauto.
  - specialize (IHR1 _ H1); deex.
    simpl in *; deex.
    specialize (IHR2 _ H5); deex.
    eauto 10.
  - specialize (IHR _ H0); deex.
    simpl in *; subst.
    eauto 10.
  - specialize (IHR _ H0); deex.
    simpl in *; deex.
    eauto 10.
  - eapply fail_step_sync_later in H; eauto.
  - inversion H; subst; repeat sigT_eq; eauto 10.
Qed.
Proof.
  induction 1; intros; repeat deex; eauto.
  - eexists; intuition eauto.
    simpl.
    eauto.
  - destruct out'0; simpl in *; repeat deex; try congruence.
    inversion H5; subst.
    (* m ---> m0, m0 ~~> d', d' ---> out' <= out *)
    eapply exec_eq_sync_later in H4; eauto; deex.
    simpl in *; deex.
    assert (possible_sync (AEQ:=addr_eq_dec) d d') by eauto.
    eapply exec_eq_sync_later in H1; eauto; deex.
    apply outcome_obs_ge_ok in H9.
    eauto.
  - destruct out'; simpl in *; repeat deex; try congruence.
    eauto.
  - destruct out'; simpl in *; repeat deex; try congruence.
    inversion H2; subst.
    eexists; intuition eauto.
    simpl; eauto.
Qed.
Proof.
  split;
    destruct out, out'; simpl; intros;
      repeat deex;
      match goal with
      | [ H: @eq (recover_outcome _ _) _ _ |- _ ] =>
        inversion H; subst
      end; eauto.
Qed.
Proof.
  split; induction 1; eauto.
Qed.
Proof.
  induction 1; simpl;
    repeat match goal with
           | [ H: Exec.R possible_sync _ _ _ _ _ |- _ ] =>
             apply exec_sync_obs_irrelevant in H; simpl in H
           | [ H: outcome_obs_le _ _ |- _ ] =>
             apply outcome_obs_ge_ok in H; progress simpl in H
           | [ H: routcome_disk_R _ _ _ |- _ ] =>
             apply routcome_disk_R_conv_ok in H; progress simpl in H
           | [ H: possible_sync ?m ?m',
                  H': possible_crash ?m' ?m'' |- _ ] =>
             lazymatch goal with
             | [ H: possible_crash m m'' |- _ ] => fail
             | _ => pose proof possible_crash_possible_sync_trans H H'
             end
           | _ => progress subst
           | _ => deex
           end;
    try solve [ eexists; intuition eauto; simpl; eauto ].
Qed.
  Proof.
    unfold flush_disk; intros.
    destruct (d a) as [ [? ?] | ]; auto.
    exists (length l).
    rewrite firstn_all.
    eauto.
  Qed.
  Proof.
    unfold flush_disk; intros.
    specialize (H a).
    specialize (H0 a).
    destruct (d a) as [ [? ?] | ];
      destruct (d' a) as [ [? ?] | ];
      repeat deex;
      inv_opt;
      try congruence.
    rewrite firstn_firstn in H0.
    eauto.
  Qed.
  Proof.
    unfold incl.
    apply ListUtils.in_firstn_in.
  Qed.
  Proof.
    unfold flush_disk, possible_sync; intros.
    specialize (H a).
    destruct (d a); eauto.
    right.
    destruct p; deex; eauto 10.
  Qed.
  Proof.
    unfold discard_buffers.
    exists (fun a =>
         match d a with
         | None => None
         | Some (v, vs) =>
           Some (diskval v vs, nil)
         end).
    intros.
    destruct (d a); auto.
    destruct p; auto.
  Qed.
  Proof.
    unfold discard_buffers; intros.
    extensionality a.
    specialize (H a).
    specialize (H0 a).
    destruct (d a) as [ [? ?] | ]; congruence.
  Qed.
  Proof.
    unfold flush_disk; intros.
    specialize (H0 a).
    rewrite H in H0; eauto.
  Qed.
  Proof.
    unfold outcome_obs_le, outcome_disk_R; split; intros;
      destruct out; eauto.
  Qed.
  Proof.
    induction 1; simpl; intros;
      intuition (repeat deex; eauto 10).
  Qed.
  Proof.
    unfold pexec; intros; deex.
    eauto using exec_flush_to_exec.
  Qed.
  Proof.
    unfold outcome_disk_R, outcome_disk_R_conv; split; intros;
      destruct out, out'; repeat deex; try congruence.
    inversion H0; eauto.
    inversion H0; eauto.
    inversion H0; eauto.
    inversion H0; eauto.
  Qed.
  Proof.
    induction l; simpl; intros.
    rewrite firstn_nil; eauto.
    destruct n; simpl; eauto.
    destruct (IHl n a); simpl; eauto.
  Qed.
  Proof.
    unfold flush_disk, discard_buffers, possible_crash; intros.
    specialize (H a).
    specialize (H0 a).
    destruct (d a) as [ [? ?] | ];
      destruct (d' a) as [ [? ?] | ];
      repeat deex;
      inv_opt;
      try congruence;
      eauto.
    right.
    repeat eexists; eauto.
    apply diskval_firstn_in_list.
  Qed.
  Proof.
    induction 1; simpl;
      repeat match goal with
             | [ H: pexec _ _ _ _ _ |- _ ] =>
               apply pexec_to_exec in H; simpl in H; deex
             | [ H: outcome_disk_R _ _ _ |- _ ] =>
               apply outcome_disk_R_conv_ok in H; progress simpl in H
             | [ H: routcome_disk_R _ _ _ |- _ ] =>
               apply routcome_disk_R_conv_ok in H; progress simpl in H
             | [ H: flush_disk ?d ?d',
                    H' : discard_buffers ?d' ?d'' |- _ ] =>
               lazymatch goal with
               | [ H: possible_crash d d'' |- _ ] => fail
               | _ => pose proof (discard_flush_is_crash H H')
               end
             | _ => progress subst
             | _ => deex
             end;
      try solve [ eexists; intuition eauto; simpl; eauto ].
  Qed.