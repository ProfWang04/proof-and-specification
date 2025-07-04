Proof.
  unfold hash_list.
  step.
  rewrite app_nil_l; reflexivity.
  rewrite app_nil_l; eassumption.
  step; try apply HL_nil; auto.
  step.

  (* Loop invariant. *)
  - rewrite <- cons_nil_app. eauto.
  - rewrite rev_unit. cbn [app].
    econstructor; eauto using hash_list_rep_upd.
    eauto using hashmap_get_fwd_safe_eq.
  - repeat eexists.
    rewrite firstn_app_r, firstn_O.
    rewrite app_nil_r. eauto.
  (* Loop invariant implies post-condition. *)
  - step.
    rewrite app_nil_r. eauto.
  - repeat eexists.
    rewrite firstn_O. cbn. solve_hash_list_rep.
  Grab Existential Variables.
  all: eauto.
  all: try ( exact tt || exact 0 || exact False ).
Qed.