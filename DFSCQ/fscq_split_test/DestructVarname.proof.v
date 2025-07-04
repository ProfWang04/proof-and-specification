Proof.
  intros.
  destruct H as [a H].
  destruct H as [b H].
  exists (a, b); auto.
Qed.
Proof.
  intros; destruct p; eauto.
Qed.
Proof.
  intros; do 2 destruct p; eauto.
Qed.
Proof.
  intros; repeat destruct_prod; repeat eexists.
Qed.
Proof.
  intros; repeat destruct_prod; repeat eexists.
Qed.
Proof.
  intros; repeat destruct_prod; repeat eexists.
Qed.
Proof.
  intros. repeat destruct_prod.
  repeat eexists.
Qed.
Proof. intros. repeat destruct_prod. repeat eexists. Qed.

Ltac destruct_varname4 :=
	match goal with
	| [ H : VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * ((VARNAME (_) * _) * _))) |- _ ] =>
		let Hx := fresh in
		pose proof (destruct_varname4 H) as Hx;
		match type of Hx with
		| exists (_ : VARNAME (vn1)) _ (_ : VARNAME (vn2)) _ (_ : VARNAME (vn3)) _ (_ : VARNAME (vn4)) _ _ , _ = _ =>
			destruct Hx as [? [?vn1 [? [?vn2 [? [?vn3 [? [?vn4 [? Hx] ] ] ] ] ] ] ] ]
		end
	end.

Proof. intros. repeat destruct_prod. repeat eexists. Qed.

Ltac destruct_varname6 :=
	match goal with
	| [ H : VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * ((VARNAME (_) * _) * _))))) |- _ ] =>
		let Hx := fresh in
		pose proof (destruct_varname6 H) as Hx;
		match type of Hx with
		| exists (_ : VARNAME (vn1)) _ (_ : VARNAME (vn2)) _ (_ : VARNAME (vn3)) _ (_ : VARNAME (vn4)) _ (_ : VARNAME (vn5)) _ (_ : VARNAME (vn6)) _ _ , _ = _ =>
			destruct Hx as [? [?vn1 [? [?vn2 [? [?vn3 [? [?vn4 [? [?vn5 [? [?vn6 [? Hx] ] ] ] ] ] ] ] ] ] ] ] ]
		end
	end.

Proof. intros. repeat destruct_prod. repeat eexists. Qed.

Ltac destruct_varname8 :=
	match goal with
	| [ H : VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * ((VARNAME (_) * _) * _))))))) |- _ ] =>
		let Hx := fresh in
		pose proof (destruct_varname8 H) as Hx;
		match type of Hx with
		| exists (_ : VARNAME (vn1)) _ (_ : VARNAME (vn2)) _ (_ : VARNAME (vn3)) _ (_ : VARNAME (vn4)) _ (_ : VARNAME (vn5)) _ (_ : VARNAME (vn6)) _ (_ : VARNAME (vn7)) _ (_ : VARNAME (vn8)) _ _ , _ = _ =>
			destruct Hx as [? [?vn1 [? [?vn2 [? [?vn3 [? [?vn4 [? [?vn5 [? [?vn6 [? [?vn7 [? [?vn8 [? Hx] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ]
		end
	end.

Proof. intros. repeat destruct_prod. repeat eexists. Qed.

Ltac destruct_varname10 :=
	match goal with
	| [ H : VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * ((VARNAME (_) * _) * _))))))))) |- _ ] =>
		let Hx := fresh in
		pose proof (destruct_varname10 H) as Hx;
		match type of Hx with
		| exists (_ : VARNAME (vn1)) _ (_ : VARNAME (vn2)) _ (_ : VARNAME (vn3)) _ (_ : VARNAME (vn4)) _ (_ : VARNAME (vn5)) _ (_ : VARNAME (vn6)) _ (_ : VARNAME (vn7)) _ (_ : VARNAME (vn8)) _ (_ : VARNAME (vn9)) _ (_ : VARNAME (vn10)) _ _ , _ = _ =>
			destruct Hx as [? [?vn1 [? [?vn2 [? [?vn3 [? [?vn4 [? [?vn5 [? [?vn6 [? [?vn7 [? [?vn8 [? [?vn9 [? [?vn10 [? Hx] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ]
		end
	end.

Proof. intros. repeat destruct_prod. repeat eexists. Qed.

Ltac destruct_varname12 :=
	match goal with
	| [ H : VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * ((VARNAME (_) * _) * _))))))))))) |- _ ] =>
		let Hx := fresh in
		pose proof (destruct_varname12 H) as Hx;
		match type of Hx with
		| exists (_ : VARNAME (vn1)) _ (_ : VARNAME (vn2)) _ (_ : VARNAME (vn3)) _ (_ : VARNAME (vn4)) _ (_ : VARNAME (vn5)) _ (_ : VARNAME (vn6)) _ (_ : VARNAME (vn7)) _ (_ : VARNAME (vn8)) _ (_ : VARNAME (vn9)) _ (_ : VARNAME (vn10)) _ (_ : VARNAME (vn11)) _ (_ : VARNAME (vn12)) _ _ , _ = _ =>
			destruct Hx as [? [?vn1 [? [?vn2 [? [?vn3 [? [?vn4 [? [?vn5 [? [?vn6 [? [?vn7 [? [?vn8 [? [?vn9 [? [?vn10 [? [?vn11 [? [?vn12 [? Hx] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ]
		end
	end.

Proof. intros. repeat destruct_prod. repeat eexists. Qed.

Ltac destruct_varname14 :=
	match goal with
	| [ H : VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * ((VARNAME (_) * _) * _))))))))))))) |- _ ] =>
		let Hx := fresh in
		pose proof (destruct_varname14 H) as Hx;
		match type of Hx with
		| exists (_ : VARNAME (vn1)) _ (_ : VARNAME (vn2)) _ (_ : VARNAME (vn3)) _ (_ : VARNAME (vn4)) _ (_ : VARNAME (vn5)) _ (_ : VARNAME (vn6)) _ (_ : VARNAME (vn7)) _ (_ : VARNAME (vn8)) _ (_ : VARNAME (vn9)) _ (_ : VARNAME (vn10)) _ (_ : VARNAME (vn11)) _ (_ : VARNAME (vn12)) _ (_ : VARNAME (vn13)) _ (_ : VARNAME (vn14)) _ _ , _ = _ =>
			destruct Hx as [? [?vn1 [? [?vn2 [? [?vn3 [? [?vn4 [? [?vn5 [? [?vn6 [? [?vn7 [? [?vn8 [? [?vn9 [? [?vn10 [? [?vn11 [? [?vn12 [? [?vn13 [? [?vn14 [? Hx] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ]
		end
	end.

Proof. intros. repeat destruct_prod. repeat eexists. Qed.

Ltac destruct_varname16 :=
	match goal with
	| [ H : VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * (VARNAME (_) * _ * ((VARNAME (_) * _) * _))))))))))))))) |- _ ] =>
		let Hx := fresh in
		pose proof (destruct_varname16 H) as Hx;
		match type of Hx with
		| exists (_ : VARNAME (vn1)) _ (_ : VARNAME (vn2)) _ (_ : VARNAME (vn3)) _ (_ : VARNAME (vn4)) _ (_ : VARNAME (vn5)) _ (_ : VARNAME (vn6)) _ (_ : VARNAME (vn7)) _ (_ : VARNAME (vn8)) _ (_ : VARNAME (vn9)) _ (_ : VARNAME (vn10)) _ (_ : VARNAME (vn11)) _ (_ : VARNAME (vn12)) _ (_ : VARNAME (vn13)) _ (_ : VARNAME (vn14)) _ (_ : VARNAME (vn15)) _ (_ : VARNAME (vn16)) _ _ , _ = _ =>
			destruct Hx as [? [?vn1 [? [?vn2 [? [?vn3 [? [?vn4 [? [?vn5 [? [?vn6 [? [?vn7 [? [?vn8 [? [?vn9 [? [?vn10 [? [?vn11 [? [?vn12 [? [?vn13 [? [?vn14 [? [?vn15 [? [?vn16 [? Hx] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ]
		end
	end.

Ltac destruct_varnames :=
	repeat (( destruct_varname16 || destruct_varname14 || destruct_varname12 || destruct_varname10 || destruct_varname8 || destruct_varname6 || destruct_varname4 || destruct_varname2 || destruct_varname1); subst).