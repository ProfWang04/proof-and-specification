  Proof.
    split; intros.
    - inv_exec.
      inv_exec; eauto.
    - eauto.
  Qed.
  Proof.
    split; intros.
    - inv_exec.
      inv_exec; eauto.
    - eauto.
  Qed.
  Proof.
    split; intros.
    - inv_exec.
      inv_exec; eauto.
    - eauto.
  Qed.
  Proof.
    split; intros.
    - inv_exec; eauto.
      inv_exec; eauto.
    - destruct out; eauto.
  Qed.
  Proof.
    split; intros.
    - inv_exec; eauto;
        inv_exec; eauto.
    - inv_exec; eauto.
      inv_exec; eauto.
  Qed.
  Proof.
    unfold corr2; intros.
    match goal with
    | [ H: _ ~= _ |- _ ] =>
      edestruct H; eauto
    end.
  Qed.