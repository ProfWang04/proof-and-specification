Proof.
  unfold bcombine, bsplit1, bsplit2, eq_rec_r, eq_rec.
  intros.
  autorewrite with bytehints.
  reflexivity.
Qed.
Proof.
  unfold bcombine, bsplit1, bsplit2, eq_rec_r, eq_rec.
  intros.
  autorewrite with bytehints.
  reflexivity.
Qed.
Proof.
  unfold bcombine, bsplit1, bsplit2, eq_rec_r, eq_rec.
  intros.
  autorewrite with bytehints.
  reflexivity.
Qed.
Proof.
  induction l.
  unfold bsplit_list, bcombine_list. reflexivity.
  simpl; unfold bsplit2_dep.
  simpl; rewrite bsplit2_bcombine.
  rewrite IHl.
  unfold bsplit1_dep.
  simpl; rewrite bsplit1_bcombine.
  unfold byte2bytes.
  reflexivity.
Qed.
Proof.
  intros; unfold bsplit_list.
  induction sz. 
  reflexivity. 
  simpl; rewrite IHsz. 
  reflexivity.
Qed.
Proof. intros. rewrite H. reflexivity. Qed.

Proof.
intros.
induction sz; simpl.
eq_rect_simpl.
unfold bytes0.
simpl.
rewrite word0.
reflexivity.

simpl in H.
inversion H.
rewrite IHsz with (H:= H1).
destruct H1.
unfold byte2bytes.
simpl.
unfold bsplit1_dep, bsplit2_dep; simpl.
rewrite bcombine_bsplit.
eq_rect_simpl.
reflexivity.
Qed.
Proof.
  unfold valu2bytes, bytes2valu, eq_rec_r, eq_rec.
  intros.
  rewrite eq_rect_word_mult.
  rewrite eq_rect_nat_double.
  generalize dependent v.
  rewrite valubytes_is.
  rewrite valulen_is.
  intros.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.
Proof.
  unfold valu2bytes, bytes2valu, eq_rec_r, eq_rec.
  intros.
  rewrite eq_rect_word_mult.
  rewrite eq_rect_nat_double.
  generalize dependent v.
  rewrite valubytes_is.
  rewrite valulen_is.
  intros.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.
Proof. intros. rewrite H. reflexivity. Qed.

Proof. intros; reflexivity. Qed.

Proof.
intros.
simpl.
unfold bsplit1_dep.
reflexivity.
Qed.
Proof.
  intros.
  unfold byte2bytes.
  unfold word2bytes.
  eq_rect_simpl.
  reflexivity.
Qed.