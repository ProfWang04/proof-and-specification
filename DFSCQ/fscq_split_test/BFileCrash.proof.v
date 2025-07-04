Proof.
  unfold file_crash; intros; repeat deex; simpl in *.
  apply possible_crash_list_synced_list_eq in H1; subst.
  eauto.
Qed.
Proof.
  intros.
  exists (fun a => match ma a with | None => None | Some v => m' a end).
  exists (fun a => match mb a with | None => None | Some v => m' a end).
  repeat split.

  - unfold mem_union; apply functional_extensionality; intros.
    case_eq (ma x); case_eq (mb x); case_eq (m' x); auto.
    intros; unfold possible_fmem_crash in *.
    destruct (H x).
    destruct H4; congruence.
    repeat deex. unfold mem_union in H5.
    rewrite H2 in H5. rewrite H3 in H5. congruence.
  - unfold mem_disjoint; intro; repeat deex.
    case_eq (ma a); case_eq (mb a); intros.
    firstorder.
    rewrite H1 in H3; congruence.
    rewrite H4 in H2; congruence.
    rewrite H4 in H2; congruence.
  - unfold possible_fmem_crash in *; intro a.
    case_eq (ma a); intros; [right|left]; auto.
    pose proof (mem_union_addr a H0 H1).
    destruct (H a); destruct H3; try congruence.
    repeat deex. do 2 eexists. intuition eauto.
    congruence.
  - unfold possible_fmem_crash in *; intro a.
    case_eq (mb a); intros; [right|left]; auto.
    rewrite mem_disjoint_comm in H0.
    pose proof (mem_union_addr a H0 H1); rewrite mem_union_comm in H2 by auto.
    destruct (H a); destruct H3; try congruence.
    repeat deex. do 2 eexists. intuition eauto.
    congruence.
Qed.
Proof.
  unfold mem_disjoint, possible_fmem_crash; intros.
  intro Hnot.
  repeat deex.
  destruct (H0 a); destruct (H1 a); try intuition congruence.
  repeat deex.
  apply H.
  do 3 eexists; eauto.
Qed.
Proof.
  unfold possible_fmem_crash, mem_union; intros.
  destruct (H a); destruct (H0 a).
  - destruct H1. destruct H2.
    rewrite H1 in *; rewrite H2 in *; rewrite H3 in *; rewrite H4 in *.
    intuition.
  - destruct H1. repeat deex.
    rewrite H1 in *; rewrite H2 in *; rewrite H3 in *; rewrite H4 in *.
    right. do 2 eexists. intuition.
  - repeat deex.
    rewrite H1 in *; rewrite H2 in *.
    right. do 2 eexists. intuition.
  - repeat deex.
    rewrite H1 in *; rewrite H3 in *; rewrite H4 in *.
    right. do 2 eexists. intuition.
Qed.
Proof.
  unfold_sep_star.
  unfold flist_crash_xform, piff, pimpl.
  split; intros; repeat deex.
  - edestruct possible_fmem_crash_mem_union; eauto.
    repeat deex.
    do 2 eexists. intuition eauto.
  - eexists. split.
    do 2 eexists. intuition idtac. 2: eauto. 2: eauto.
    eapply possible_fmem_crash_disjoint; eauto.
    eapply possible_fmem_crash_union; eauto.
Qed.
Proof.
  unfold flist_crash_xform, ptsto, pimpl, possible_fmem_crash, and, lift; intros.
  repeat deex.
  specialize (H1 a) as H1a; intuition; try congruence; repeat deex.
  exists f'.
  eapply sep_star_lift_apply'.
  2: congruence.
  intuition (try congruence).
  specialize (H1 a') as H1a'; intuition; try congruence.
  repeat deex; try congruence. rewrite H2 in * by eauto. congruence.
Qed.
Proof.
  unfold lift_empty, flist_crash_xform, possible_fmem_crash, piff, pimpl; split; intros; repeat deex.
  - specialize (H1 a); intuition; repeat deex; congruence.
  - eexists; intuition eauto.
Qed.
Proof.
  unfold emp, flist_crash_xform, possible_fmem_crash, piff, pimpl; split; intros; repeat deex.
  - specialize (H1 a); intuition; repeat deex; congruence.
  - eexists; intuition eauto.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  intros; unfold flist_crash_xform, possible_fmem_crash.
  eexists; intuition eauto.
  destruct (lt_dec a (length f)).
  - right. unfold flist_crash in *.
    do 2 eexists.
    unfold list2nmem.
    erewrite selN_map by omega.
    erewrite selN_map by ( erewrite <- flist_crash_length by eauto; omega ).
    intuition eauto.
    eapply forall2_selN; auto.
  - left. unfold list2nmem. repeat rewrite selN_oob; auto; rewrite map_length.
    erewrite <- flist_crash_length by eauto. omega. omega.
Grab Existential Variables.
  all: exact BFILE.bfile0.
Qed.
Proof.
  firstorder.
Qed.