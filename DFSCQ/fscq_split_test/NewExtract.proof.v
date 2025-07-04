Proof.
*)

Axiom go_expr_is_apply1 : forall ArgType RetType
                                 (f : ArgType -> RetType) fg
                                 (a : ArgType) ag,
  go_expr_is f fg ->
  go_expr_is a ag ->
  go_expr_is (f a) (fg ++ ag).
Hint Resolve go_expr_is_apply1 : go_expr.

Proof.
  econstructor.
  eauto with go.
Defined.
Proof.
  econstructor.
  eapply go_expr_is_apply1.
  eauto with go.