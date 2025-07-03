Require Import Mem.
Require Import ListUtils.
Require Import List Omega Ring Word Pred PredCrash.
Require Import Prog Hoare SepAuto BasicProg.
Require Import FunctionalExtensionality.
Require Import WordAuto.
Require Import AsyncDisk.

Import ListNotations.

Set Implicit Arguments.
Set Default Proof Using "Type".


(** * A generic array predicate: a sequence of consecutive points-to facts *)

Section GenArray.

  Variable V VP : Type.
  Variable pts : addr -> V -> @pred addr addr_eq_dec VP.

  Infix "|-?->" := pts (at level 35) : pred_scope.

  Fixpoint arrayN (a : addr) (vs : list V) : @pred _ addr_eq_dec _ :=
    match vs with
      | nil => emp
      | v :: vs' => a |-?-> v * arrayN (S a) vs'
    end%pred.

  Lemma arrayN_unify : forall (a b : list V) s,
    a = b -> arrayN s a =p=> arrayN s b.
  Proof.
    intros; subst; auto.
  Qed.

  Lemma arrayN_one: forall v,
      0 |-?-> v <=p=> arrayN 0 [v].
  Proof.
    split; cancel.
  Qed.

  Lemma isolateN_fwd' : forall vs i a (default : V),
    i < length vs
    -> arrayN a vs =p=> arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
       * arrayN (a + i + 1) (skipn (S i) vs).
  Proof.
    induction vs; simpl; intuition.

    inversion H.

    destruct i; simpl.

    replace (a0 + 0) with (a0) by omega.
    replace (a0 + 1) with (S a0) by omega.
    cancel.

    eapply pimpl_trans; [ apply pimpl_sep_star; [ apply pimpl_refl | apply IHvs ] | ]; clear IHvs.
    instantiate (1 := i); omega.
    simpl.
    replace (S (a0 + i)) with (a0 + S i) by omega.
    replace (S (a0 + i + 1)) with (a0 + S i + 1) by omega.
    cancel.
  Qed.

  Theorem isolateN_fwd : forall (default : V) a i vs,
    i < length vs
    -> arrayN a vs =p=> arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
       * arrayN (a + i + 1) (skipn (S i) vs).
  Proof.
    intros.
    eapply pimpl_trans; [ apply isolateN_fwd' | ].
    eassumption.
    apply pimpl_refl.
  Qed.

  Lemma isolateN_bwd' : forall vs i a (default : V),
    i < length vs
    -> arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
       * arrayN (a + i + 1) (skipn (S i) vs)
    =p=> arrayN a vs.
  Proof.
    induction vs; simpl; intuition.

    inversion H.

    destruct i; simpl.

    replace (a0 + 0) with (a0) by omega.
    replace (a0 + 1) with (S a0) by omega.
    cancel.

    eapply pimpl_trans; [ | apply pimpl_sep_star; [ apply pimpl_refl | apply IHvs ] ]; clear IHvs.
    2: instantiate (1 := i); omega.
    simpl.
    replace (a0 + S i) with (S (a0 + i)) by omega.
    cancel.
  Qed.

  Theorem isolateN_bwd : forall (default : V) a i vs,
    i < length vs
    -> arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
       * arrayN (a + i + 1) (skipn (S i) vs)
    =p=> arrayN a vs.
  Proof.
    intros.
    eapply pimpl_trans; [ | apply isolateN_bwd' ].
    2: eassumption.
    apply pimpl_refl.
  Qed.

  Theorem arrayN_isolate : forall (default : V) a i vs,
    i < length vs
    -> arrayN a vs <=p=>
       arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
       * arrayN (a + i + 1) (skipn (S i) vs).
  Proof.
    unfold piff; split.
    apply isolateN_fwd; auto.
    apply isolateN_bwd; auto.
  Qed.

  Theorem isolate_fwd_upd : forall (v : V) a i vs,
    i < length vs
    -> arrayN a (updN vs i v) <=p=>
       arrayN a (firstn i vs)
       * (a + i) |-?-> v
       * arrayN (a + i + 1) (skipn (S i) vs).
  Proof.
    intros.
    erewrite arrayN_isolate with (vs:=updN vs i v) (i:=i) (default:=v);
      autorewrite with lists; auto.
    unfold piff; split.
    cancel; autorewrite with lists; cancel.
    cancel; autorewrite with lists; cancel.
  Qed.

  Theorem isolateN_bwd_upd : forall (v : V) a i vs,
    i < length vs
    -> arrayN a (firstn i vs)
       * (a + i) |-?-> v
       * arrayN (a + i + 1) (skipn (S i) vs)
       =p=> arrayN a (updN vs i v).
  Proof.
    intros.
    erewrite <- isolateN_bwd with (vs:=updN vs i v) (i:=i) (default:=v).
    rewrite selN_updN_eq by auto.
    rewrite firstn_updN_oob by auto.
    rewrite skipN_updN' by auto.
    cancel.
    rewrite length_updN.
    auto.
  Qed.

  Theorem arrayN_app : forall (a b : list V) st,
    arrayN st (a ++ b) <=p=>
    arrayN st a * arrayN (st + length a) b.
  Proof.
    induction a; split; simpl; auto.
    rewrite Nat.add_0_r; cancel.
    rewrite Nat.add_0_r; cancel.
    rewrite IHa.
    replace (S st + length a0) with (st + S (length a0)) by omega.
    cancel.
    rewrite IHa.
    replace (S st + length a0) with (st + S (length a0)) by omega.
    cancel.
  Qed.

  Theorem arrayN_split : forall i (a : list V) st,
    arrayN st a <=p=>
    arrayN st (firstn i a) * arrayN (st + i) (skipn i a).
  Proof.
    intros.
    destruct (lt_dec i (length a)).
    erewrite arrayN_isolate; eauto.
    setoid_rewrite arrayN_isolate with (i := 0) at 4.
    rewrite skipn_skipn, skipn_selN.
    replace (st + i + 0) with (st+i) by omega.
    replace (1 + i) with (S i) by omega.
    replace (i + 0) with i by omega.
    split; cancel.
    rewrite skipn_length.
    omega.
    rewrite firstn_oob, skipn_oob by omega.
    split; cancel.
    Grab Existential Variables.
    destruct a.
    contradict l; simpl; omega.
    exact v.
  Qed.


  Lemma arrayN_ptsto_selN_0 : forall l (def : V) a,
    length l = 1 ->
    arrayN a l <=p=> (a |-?-> selN l 0 def)%pred.
  Proof.
    destruct l; simpl; intros; try congruence.
    assert (length l = 0) by omega.
    apply length_nil in H0; subst; simpl; split; cancel.
  Qed.

  Lemma arrayN_isolate_hd : forall l (def : V) a,
    length l >= 1 ->
    arrayN a l <=p=> (a |-?-> selN l 0 def * arrayN (a + 1) (skipn 1 l) )%pred.
  Proof.
    destruct l; simpl; intros; try omega.
    replace (a + 1) with (S a) by omega; auto.
  Qed.


End GenArray.

Section PtstoArray.

  Variable V : Type.
  Notation pts := (@ptsto addr addr_eq_dec V).

  Lemma arrayN_oob': forall (l : list V) a i m,
    i >= length l
    -> arrayN pts a l m
    -> m (a + i) = None.
  Proof.
    induction l; intros; auto; simpl in *.
    destruct (eq_nat_dec i 0); auto.
    subst; simpl in *; omega.

    unfold sep_star in H0; rewrite sep_star_is in H0; unfold sep_star_impl in H0.
    repeat deex.
    unfold mem_union.
    unfold ptsto in H2; destruct H2; rewrite H2.
    pose proof (IHl (S a0) (i - 1)).
    replace (S a0 + (i - 1)) with (a0 + i) in H3 by omega.
    apply H3; try omega.

    auto.
    omega.
  Qed.

  Lemma arrayN_oob: forall (l : list V) i m,
    i >= length l
    -> arrayN pts 0 l m
    -> m i = None.
  Proof.
    intros.
    replace i with (0 + i) by omega.
    eapply arrayN_oob'; eauto.
  Qed.

  Lemma arrayN_oob_lt: forall (l : list V) i a m,
    arrayN pts a l m ->
    i < a ->
    m i = None.
  Proof.
    induction l; intros; auto; simpl in *.
    unfold sep_star in H; rewrite sep_star_is in H; unfold sep_star_impl in H.
    repeat deex.
    unfold mem_union.
    unfold ptsto in H2; destruct H2; rewrite H2.
    eapply IHl; eauto.
    omega.
  Qed.

  Lemma arrayN_updN_memupd : forall F l a i (v : V) m,
    (F * arrayN pts a l)%pred m ->
    i < length l ->
    (F * arrayN pts a (updN l i v))%pred (Mem.upd m (a + i) v).
  Proof.
    intros.
    rewrite arrayN_isolate with (i := i).
    eapply pimpl_trans; [ apply pimpl_refl | | eapply ptsto_upd ].
    rewrite selN_updN_eq by auto.
    cancel.
    rewrite firstn_updN_oob by auto.
    rewrite skipn_updN by auto.
    pred_apply.
    rewrite arrayN_isolate by eauto.
    cancel.
    rewrite length_updN; auto.
    Grab Existential Variables. all: eauto.
  Qed.

  Lemma arrayN_app_memupd : forall l (v : V) m,
    arrayN pts 0 l m
    -> arrayN pts 0 (l ++ v :: nil) (Mem.upd m (length l) v).
  Proof.
    intros.

    eapply isolateN_bwd with (i := (length l)) (default := v).
    rewrite app_length; simpl; omega.

    rewrite firstn_app2; auto.
    rewrite selN_last; auto.
    rewrite skipn_oob; [ | rewrite app_length; simpl; omega ].
    unfold arrayN at 2; auto; apply emp_star_r.
    simpl.

    apply ptsto_upd_disjoint; auto.
    eapply arrayN_oob; eauto.
  Qed.


  Theorem arrayN_list_eq : forall (vs1 vs2 : list V) s m,
    arrayN pts s vs1 m -> arrayN pts s vs2 m -> vs1 = vs2.
  Proof.
    induction vs1; destruct vs2; simpl; intros; auto.
    apply ptsto_valid in H0; congruence.
    apply ptsto_valid in H; congruence.
    apply ptsto_valid in H as Hx.
    apply ptsto_valid in H0 as Hy.
    rewrite Hx in Hy; inversion Hy; subst; clear Hx Hy; f_equal.
    apply ptsto_mem_except in H.
    apply ptsto_mem_except in H0.
    eapply IHvs1; eauto.
  Qed.

  Theorem arrayN_strictly_exact : forall (vs : list V) base,
    strictly_exact (arrayN pts base vs).
  Proof.
    induction vs; simpl; intros.
    apply emp_strictly_exact.
    apply sep_star_strictly_exact.
    apply ptsto_strictly_exact.
    eauto.
  Qed.

  Lemma arrayN_selN : forall F a st l m (def : V),
    (F * arrayN pts st l)%pred m ->
    a >= st ->
    a < st + length l ->
    m a = Some (selN l (a - st) def).
  Proof.
    intros.
    eapply ptsto_valid; pred_apply.
    rewrite arrayN_isolate with (i := a - st) by omega.
    replace (st + (a - st)) with a by omega.
    clear H; cancel.
  Qed.

  Lemma arrayN_selN_exis : forall F a st (l : list V) m,
    (F * arrayN pts st l)%pred m ->
    a >= st ->
    a < st + length l ->
    exists v, m a = Some v.
  Proof.
    intros; destruct l.
    simpl in *; try omega.
    eexists; eapply arrayN_selN with (def := v); eauto; try omega.
  Qed.

  Lemma arrayN_unify' : forall a b s m (F1 F2 : pred), length a = length b ->
    (F1 * arrayN pts s a)%pred m -> (F2 * arrayN pts s b)%pred m -> a = b.
  Proof.
    induction a as [|x a']; intros.
    simpl in *.
    rewrite length_nil; auto.
    destruct b as [|y b']; simpl in *.
    inversion H.
    inversion H.
    erewrite IHa' with (s := S s); eauto.
    f_equal.
    assert (m s = Some x /\ m s = Some y); intuition.
    all : try match goal with
      | [ H : (_ * (pts ?s ?x * _))%pred ?m |- ?m ?s = Some ?x] =>
        eapply ptsto_valid;
        eapply pimpl_apply; [> | exact H]; cancel
      | [ H : (_ * (_ * arrayN _ _ ?a))%pred ?m |- (_ * arrayN _ _ ?a)%pred _] =>
        eapply pimpl_apply; [> | exact H]; cancel
    end.
    remember (m s) as r; clear Heqr; subst.
    match goal with [H: Some _ = Some _ |- _] => inversion H end; auto.
  Qed.

End PtstoArray.

Lemma arrayN_piff_replace: forall T V (l : list T) n (p q : _ -> _ -> @pred _ _ V),
  (forall i d x, i < length l -> selN l i d = x -> p (i + n) x <=p=> q (i + n) x) ->
  arrayN p n l <=p=> arrayN q n l.
Proof.
  induction l; cbn; intros; auto.
  rewrite H with (i := 0) by (auto; omega).
  rewrite IHl.
  split; cancel.
  intros.
  rewrite <- plus_Snm_nSm.
  rewrite H; (eauto; omega).
Qed.

Lemma arrayN_map: forall V T T' (l : list T) n (p : addr -> T' -> @pred _ _ V) (f : T -> T'),
  arrayN p n (map f l) <=p=> arrayN (fun i x => p i (f x)) n l.
Proof.
  induction l; cbn; intros; auto.
  rewrite IHl.
  auto.
Qed.
