  Proof.
    unfold lt; intros.
    apply wlt_lt in H; apply wlt_lt in H0.
    apply lt_wlt.
    omega.
  Qed.
  Proof.
    unfold lt, eq; intros.
    apply wlt_lt in H.
    intro He; subst; omega.
  Qed.
  Proof.
    unfold lt, eq.
    destruct (wlt_dec x y); [ apply LT; auto | ].
    destruct (weq x y); [ apply EQ; auto | ].
    apply GT. apply le_neq_lt; auto.
  Defined.
  Proof.
    rewrite valulen_is. simpl. firstorder. (* this could be much faster, say with reflection *)
  Qed.
  Proof.
    apply le_plus_minus_r; apply header_sz_ok.
  Qed.
  Proof.
    unfold valu_to_header, header_to_valu.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite <- plus_minus_header.
    do 2 rewrite <- eq_rect_eq_dec by (apply eq_nat_dec).
    unfold zext.
    rewrite split1_combine.
    apply Rec.of_to_id.
    simpl; destruct h; tauto.
  Qed.
  Proof.
    unfold descriptor_to_valu, valu_to_descriptor.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite Rec.to_of_id.
    rewrite <- descriptor_sz_ok.
    do 2 rewrite <- eq_rect_eq_dec by (apply eq_nat_dec).
    trivial.
  Defined.
  Proof.
    induction n; intros; simpl; auto.
    destruct l.
    reflexivity.
    simpl. rewrite IHn. reflexivity.
  Qed.
  Proof.
    (* intros; rename a into a'; remember (wordToNat a') as a. *)
    intros a ms m def HnotIn.
    destruct (MapFacts.elements_in_iff ms a) as [_ Hr].
    assert (not (exists e : valu, InA (Map.eq_key_elt (elt:=valu))
      (a, e) (Map.elements ms))) as HnotElem by auto; clear Hr HnotIn.
    remember (Map.eq_key_elt (elt:=valu)) as eq in *.
    unfold replay, replay'.
    remember (Map.elements ms) as elems in *.
    assert (forall x y, InA eq (x,y) elems -> x <> a) as Hneq. {
      intros x y Hin.
      destruct (addr_as_OT.eq_dec a x); [|intuition].
      destruct HnotElem; exists y; subst; auto.
    }
    clear Heqelems HnotElem.
    induction elems as [|p]; [reflexivity|].
    rewrite <- IHelems; clear IHelems; [|intros; eapply Hneq; right; eauto].
    destruct p as [x y]; simpl.
    assert (x <> a) as Hsep. {
      apply (Hneq x y); left; subst eq. 
      apply Equivalence.equiv_reflexive_obligation_1.
      apply MapProperties.eqke_equiv.
    }
    eapply (selN_updN_ne _ y);
      unfold not; intros; destruct Hsep; apply wordToNat_inj; trivial.
  Qed.
  Proof.
    intros until 0; intros HNoDup HIn Hbounds.

    induction l as [|p]; [inversion HIn|]; destruct p as [x y]; simpl.
    destruct HIn. {
      clear IHl.
      injection H; clear H;
        intro H; rewrite H in *; clear H;
        intro H; rewrite H in *; clear H.
      apply selN_updN_eq. rewrite <- replay'_length; assumption.
    } {
      assert (x <> a) as Hneq. {
        inversion HNoDup. 
        assert (InA eq (a,v) l). {
          apply In_InA; subst; eauto using MapProperties.eqk_equiv.
        }
      remember (Map.eq_key (elt:=V)) as eq_key in *.
      assert (forall a b, eq a b -> eq_key a b) as Heq_eqk by (
        intros; subst; apply MapProperties.eqk_equiv).
      assert (forall a l, InA eq a l -> InA eq_key a l) as HIn_eq_eqk by (
        intros until 0; intro HInAeq; induction HInAeq; [subst|right]; auto).
      assert (@Equivalence (Map.key*V) eq_key) as Eqeq by (
        subst eq_key; apply MapProperties.eqk_equiv).
      intro Hcontra; destruct
        (@InA_NotInA_neq (Map.key*V) eq_key Eqeq l (a,v) (x,y) (HIn_eq_eqk _ _ H4) H2).
      subst; unfold Map.eq_key; reflexivity.
      }
      unfold sel, upd in *.
      rewrite selN_updN_ne, IHl;
        try trivial;
        match goal with
          | [ H: KNoDup (?a::?l) |- KNoDup ?l ] => inversion H; assumption
          | [ Hneq: ?a<>?b |- wordToNat ?a <> wordToNat ?b] =>
            unfold not; intro Hcontra; destruct (Hneq (wordToNat_inj _  _ Hcontra))
        end.
    }
  Qed.
  Proof.
    intros.
    induction l.
    inversion H.
    inversion H.
    inversion H1.
    destruct a0; simpl in *; subst.
    left; trivial.
    simpl.
    right.
    apply IHl; auto.
  Qed.
  Proof.
    intros.
    apply Map.elements_1 in H.
    apply InA_eqke_In; auto.
  Qed.
  Proof.
    intros.
    apply mapsto_In in H.
    unfold replay.
    apply replay'_sel.
    apply Map.elements_3w.
    auto.
  Qed.
  Proof.
    intros; unfold goodSize in *.
    destruct (lt_dec a (length m)); [|
      repeat (rewrite selN_oob); unfold replay;
        try match goal with [H: _ |- length (replay' _ _) <= a]
            => rewrite <- replay'_length end;
        auto; omega].
    unfold replay, replay'.
    induction (Map.elements ms); [reflexivity|].
    rewrite <- IHl0; clear IHl0; simpl.
    unfold upd.
    rewrite selN_updN_ne.
  Qed.
  Proof.
    induction l.
    auto.
    intros.
    simpl.
    rewrite length_upd, IHl.
  Qed.
  Proof.
    intros.
    unfold replay.
    apply replay'_len.
  Qed.
  Proof.
    intros.
    (* Let's show that the lists are equal because [sel] at any index [pos] gives the same valu *)
    eapply list_selN_ext.
    rewrite length_upd.
    repeat rewrite replay_len.
    trivial.
    
    intros.
    destruct (lt_dec pos (pow2 addrlen)).
    - (* [pos] is a valid address *)
      replace pos with (wordToNat (natToWord addrlen (pos))) by word2nat_auto.
      destruct (weq ($ pos) a).
      + (* [pos] is [a], the address we're updating *)
        erewrite replay_sel_in.
        reflexivity.
        instantiate (default := $0).
        subst.
        unfold upd.
        rewrite selN_updN_eq.
        apply Map.add_1.
        trivial.
        rewrite replay_len in *.
        word2nat_auto.
    
      + (* [pos] is another address *)
        unfold upd.
        rewrite selN_updN_ne by word2nat_auto.

        case_eq (Map.find $ pos ms).

        (* [pos] is in the transaction *)
        intros w Hf.
        erewrite replay_sel_in.
        reflexivity.
        apply Map.find_2 in Hf.

        erewrite replay_sel_in.
        apply Map.add_2.
        unfold not in *; intros; solve [auto].
        eauto.
        eauto.
        
        (* [pos] is not in the transaction *)
        Ltac wneq H := intro HeqContra; symmetry in HeqContra; apply H; auto.
        intro Hf; 
          repeat (erewrite replay_sel_other);
          try trivial;
          intro HIn; destruct HIn as [x HIn];
          try apply Map.add_3 in HIn;
          try apply Map.find_1 in HIn;
          try wneq n;
          replace (Map.find $ (pos) ms) with (Some x) in Hf; inversion Hf.
    - (* [pos] is an invalid address *)
      rewrite replay_sel_invalid by auto.
      unfold upd.
      rewrite selN_updN_ne by (
        generalize (wordToNat_bound a); intro Hb;
        unfold addr_as_OT.WIDTH in *; omega).
      rewrite replay_sel_invalid by auto; trivial.
  Qed.
  Proof.
    unfold valid_entries in *.
    intros.
    destruct (weq a a0).
    subst; auto.
    eapply H.
    eapply Map.add_3; eauto.
  Qed.
Proof.
  unfold do_two_writes.
  hoare.
Qed.
Proof.
  hoare.
Qed.
Proof.
  hoare.
Qed.
Proof.
  hoare.
Qed.
Proof.
  hoare.
Qed.
  Proof.
    hoare.












