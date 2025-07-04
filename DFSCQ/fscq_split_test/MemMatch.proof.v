    Proof.
      intros H x y P1 P2 H0.
      pose proof (H x P1) as [P3 P4].
      rewrite <- P4.
      rewrite H0.
      apply H.
      auto.
    Qed.
    Proof.
      intros H y P1.
      pose proof (H y P1) as [P2 P3].
      rewrite <- P3.
      exists (f' y); intuition.
    Qed.
    Proof.
      intros [H1 H2].
      constructor.
      eapply cond_left_inv_inj; eauto.
      eapply cond_right_inv_surj; eauto.
    Qed.
    Proof.
      intros; apply H; auto.
    Qed.
    Proof.
      intros; apply H; auto.
    Qed.
    Proof.
      intros; apply H; auto.
    Qed.
    Proof.
      intros; apply H; auto.
    Qed.
Proof.
  firstorder.
Qed.
Proof.
  intros.
  eapply cond_inv2bij.
  apply cond_inverse_sym; eauto.
Qed.
  Proof using MTrans AP1_ok.
    intros.
    apply AP1_ok in H.
    rewrite <- (MTrans H); auto.
  Qed.
  Proof using MTrans AP1_ok.
    intros; unfold mem_atrans, mem_except; intro x.
    destruct (AEQ1 x a); destruct (AEQ2 (atrans x) (atrans a));
      subst; auto; try tauto.
    destruct (indomain_dec x m1); auto.
    contradict n.
    apply H; auto.
  Qed.
    Proof using MTrans HInv.
      intros.
      replace a with (atrans (ainv a)) by (apply HInv; auto).
      assert (AP1 (ainv a)) as Hx by (apply HInv; auto).
      rewrite <- (MTrans Hx); auto.
    Qed.
    Proof using MTrans HInv.
      intros.
      apply any_sep_star_ptsto.
      eapply mem_ainv_any; eauto.
      eapply ptsto_valid'; eauto.
    Qed.
    Proof using MTrans HInv.
      unfold notindomain; intros.
      eapply mem_ainv_any; eauto.
    Qed.
    Proof using MTrans HInv.
      unfold indomain; intros.
      destruct H; eexists.
      eapply mem_ainv_any; eauto.
    Qed.
    Proof using MTrans HInv AP2_ok AP2_dec.
      unfold emp; intros.
      destruct (AP2_dec a).

      replace a with (atrans (ainv a)).
      apply mem_ainv_any; auto.
      replace (atrans (ainv a)) with a; auto.
      apply eq_sym; apply HInv; auto.
      apply HInv; auto.

      destruct (indomain_dec a m2); auto.
      contradict H0.
      apply AP2_ok; auto.
    Qed.
    Proof using MTrans HInv AP1_ok.
      intros; unfold mem_atrans, mem_except; intro x.
      destruct (AEQ1 x (ainv a)); destruct (AEQ2 (atrans x) a);
        try subst; auto; try tauto.

      contradict n.
      apply HInv; auto.
      destruct (indomain_dec x m1); auto.
      contradict n.
      apply eq_sym.
      apply HInv; auto.
    Qed.
    Proof using MTrans HInv.
      intros; unfold mem_atrans, Mem.upd; intro x.
      destruct (AEQ1 x (ainv a)); destruct (AEQ2 (atrans x) a); auto.
      contradict n; subst.
      apply HInv; auto.

      intros; subst.
      contradict n.
      erewrite cond_inv_rewrite_left; eauto.
    Qed.
    Proof using HInv MTrans.
      cbv [mem_atrans cond_inverse cond_left_inverse cond_right_inverse] in *.
      destruct HInv as [_ H'].
      intros a ?; specialize (H' a).
      rewrite MTrans by intuition.
      f_equal. intuition.
    Qed.