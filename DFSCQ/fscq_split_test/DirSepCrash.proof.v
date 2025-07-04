Proof.
  intros.
  exists (fun a => match ma a with | None => None | Some v => m' a end).
  exists (fun a => match mb a with | None => None | Some v => m' a end).
  repeat split.

  - unfold mem_union; apply functional_extensionality; intros.
    case_eq (ma x); case_eq (mb x); case_eq (m' x); auto.
    intros; unfold possible_flatmem_crash in *.
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
  - unfold possible_flatmem_crash in *; intro a.
    case_eq (ma a); intros; [right|left]; auto.
    pose proof (mem_union_addr a H0 H1).
    destruct (H a); destruct H3; try congruence.
    repeat deex. do 2 eexists. intuition eauto.
    congruence.
  - unfold possible_flatmem_crash in *; intro a.
    case_eq (mb a); intros; [right|left]; auto.
    rewrite mem_disjoint_comm in H0.
    pose proof (mem_union_addr a H0 H1); rewrite mem_union_comm in H2 by auto.
    destruct (H a); destruct H3; try congruence.
    repeat deex. do 2 eexists. intuition eauto.
    congruence.
Qed.
Proof.
  unfold mem_disjoint, possible_flatmem_crash; intros.
  intro Hnot.
  repeat deex.
  destruct (H0 a); destruct (H1 a); try intuition congruence.
  repeat deex.
  apply H.
  do 3 eexists; eauto.
Qed.
Proof.
  unfold possible_flatmem_crash, mem_union; intros.
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
  unfold flatmem_crash_xform, piff, pimpl.
  split; intros; repeat deex.
  - edestruct possible_flatmem_crash_mem_union; eauto.
    repeat deex.
    do 2 eexists. intuition eauto.
  - eexists. split.
    do 2 eexists. intuition idtac. 2: eauto. 2: eauto.
    eapply possible_flatmem_crash_disjoint; eauto.
    eapply possible_flatmem_crash_union; eauto.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  unfold flatmem_crash_xform, ptsto, pimpl, possible_flatmem_crash, and, lift; intros.
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
  unfold lift_empty, flatmem_crash_xform, possible_flatmem_crash, piff, pimpl; split; intros; repeat deex.
  - specialize (H1 a); intuition; repeat deex; congruence.
  - eexists; intuition eauto.
Qed.
Proof.
  unfold emp, flatmem_crash_xform, possible_flatmem_crash, piff, pimpl; split; intros; repeat deex.
  - specialize (H1 a); intuition; repeat deex; congruence.
  - eexists; intuition eauto.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  intros; unfold flatmem_crash_xform, possible_flatmem_crash.
  eexists; intuition eauto.
  unfold dir2flatmem2.
  case_eq (find_subtree a f); intros.
  - right.
    eapply DTCrash.tree_crash_find_name in H1; eauto.
    deex.
    rewrite H2; clear H2.
    destruct d.
    + inversion H3; subst.
      do 2 eexists.
      intuition.
      constructor; eauto.
    + inversion H3; subst.
      do 2 eexists.
      intuition.
      constructor.
  - right.
    eapply DTCrash.tree_crash_find_none in H1; eauto.
    rewrite H1; clear H1.
    do 2 eexists.
    intuition eauto.
    constructor.
Qed.
Proof.
  unfold flatmem_crash_xform, ptsto, possible_flatmem_crash, pimpl; intros.
  deex.
  - specialize (H1 pn); intuition; try congruence.
    repeat deex.
    rewrite H in H1. inversion H1; subst.
    inversion H4. congruence.
  - specialize (H1 a'); intuition; try congruence.
    repeat deex.
    rewrite H2 in H3.
    congruence.
    eauto.
Qed.
Proof.
  unfold flatmem_crash_xform, ptsto, possible_flatmem_crash, pimpl; intros.
  deex.
  - specialize (H1 pn); intuition; try congruence.
    repeat deex.
    rewrite H in H1. inversion H1; subst.
    inversion H4. congruence.
  - specialize (H1 a'); intuition; try congruence.
    repeat deex.
    rewrite H2 in H3.
    congruence.
    eauto.
Qed.
Proof.
  unfold flatmem_crash_xform, ptsto, possible_flatmem_crash, pimpl; intros.
  deex.
  specialize (H1 pn) as H1'; intuition; try congruence.
  repeat deex.
  rewrite H in H3. inversion H3; subst.
  inversion H5. subst.
  eexists.
  eapply sep_star_lift_apply'; eauto.
  intuition.
  specialize (H1 a').
  intuition.
  repeat deex.
  rewrite H2 in H6; try congruence; eauto.
Qed.
Proof.
  firstorder.
Qed.