Proof.
  intros; destruct p; eauto.
Qed.
Proof.
  intros; do 3 destruct p; eauto.
Qed.
Proof.
  intros; do 7 destruct p; eauto 10.
Qed.
Proof.
  intros.
  pose proof (destruct_eight x) as Hd. do 8 destruct Hd as [? Hd]. subst.
  pose proof (destruct_four x0) as Hd. do 4 destruct Hd as [? Hd]. subst.
  pose proof (destruct_two x) as Hd. do 2 destruct Hd as [? Hd]. subst.
Abort.