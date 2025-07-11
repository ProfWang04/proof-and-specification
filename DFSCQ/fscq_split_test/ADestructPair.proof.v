Proof. intros; do 1 destruct p; repeat eexists. Qed.

Ltac destruct_pair2 :=
  match goal with
  | [ H : _ * _ |- _ ] => first [ clear H || let Hx := fresh in
      pose proof (destruct_pair2 H) as Hx;
      match type of Hx with
      | exists _ _, _ = _ =>
        let H1 := fresh H "_1" in let H2 := fresh H "_2" in
        destruct Hx as [H1 [H2 Hx] ]
      end ]
  end.

Proof. intros; do 3 destruct p; repeat eexists. Qed.

Ltac destruct_pair4 :=
	match goal with
	| [ H : _ * _ * _ * _|- _ ] => first [ clear H ||  let Hx := fresh in
		pose proof (destruct_pair4 H) as Hx;
		match type of Hx with
		| exists _ _ _ _ , _ = _ =>
		destruct Hx as [? [? [? [? Hx ] ] ] ]
		end ]
	end.

Proof. intros; do 5 destruct p; repeat eexists. Qed.

Ltac destruct_pair6 :=
	match goal with
	| [ H : _ * _ * _ * _ * _ * _|- _ ] => first [ clear H ||  let Hx := fresh in
		pose proof (destruct_pair6 H) as Hx;
		match type of Hx with
		| exists _ _ _ _ _ _ , _ = _ =>
		destruct Hx as [? [? [? [? [? [? Hx ] ] ] ] ] ]
		end ]
	end.

Proof. intros; do 7 destruct p; repeat eexists. Qed.

Ltac destruct_pair8 :=
	match goal with
	| [ H : _ * _ * _ * _ * _ * _ * _ * _|- _ ] => first [ clear H ||  let Hx := fresh in
		pose proof (destruct_pair8 H) as Hx;
		match type of Hx with
		| exists _ _ _ _ _ _ _ _ , _ = _ =>
		destruct Hx as [? [? [? [? [? [? [? [? Hx ] ] ] ] ] ] ] ]
		end ]
	end.

Proof. intros; do 9 destruct p; repeat eexists. Qed.

Ltac destruct_pair10 :=
	match goal with
	| [ H : _ * _ * _ * _ * _ * _ * _ * _ * _ * _|- _ ] => first [ clear H ||  let Hx := fresh in
		pose proof (destruct_pair10 H) as Hx;
		match type of Hx with
		| exists _ _ _ _ _ _ _ _ _ _ , _ = _ =>
		destruct Hx as [? [? [? [? [? [? [? [? [? [? Hx ] ] ] ] ] ] ] ] ] ]
		end ]
	end.

Proof. intros; do 11 destruct p; repeat eexists. Qed.

Ltac destruct_pair12 :=
	match goal with
	| [ H : _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _|- _ ] => first [ clear H ||  let Hx := fresh in
		pose proof (destruct_pair12 H) as Hx;
		match type of Hx with
		| exists _ _ _ _ _ _ _ _ _ _ _ _ , _ = _ =>
		destruct Hx as [? [? [? [? [? [? [? [? [? [? [? [? Hx ] ] ] ] ] ] ] ] ] ] ] ]
		end ]
	end.

Proof. intros; do 13 destruct p; repeat eexists. Qed.

Ltac destruct_pair14 :=
	match goal with
	| [ H : _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _|- _ ] => first [ clear H ||  let Hx := fresh in
		pose proof (destruct_pair14 H) as Hx;
		match type of Hx with
		| exists _ _ _ _ _ _ _ _ _ _ _ _ _ _ , _ = _ =>
		destruct Hx as [? [? [? [? [? [? [? [? [? [? [? [? [? [? Hx ] ] ] ] ] ] ] ] ] ] ] ] ] ]
		end ]
	end.

Proof. intros; do 15 destruct p; repeat eexists. Qed.

Ltac destruct_pair16 :=
	match goal with
	| [ H : _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _ * _|- _ ] => first [ clear H ||  let Hx := fresh in
		pose proof (destruct_pair16 H) as Hx;
		match type of Hx with
		| exists _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ , _ = _ =>
		destruct Hx as [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? Hx ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ]
		end ]
	end.

Ltac destruct_pair_once :=
	match goal with
	| [ v: valuset |- _ ] =>
	  let v0 := fresh v "_cur" in
	  let v1 := fresh v "_old" in
	  destruct v as [v0 v1]
	| _ => ( 
destruct_pair16 || destruct_pair14 || destruct_pair12 || destruct_pair10 || destruct_pair8 || destruct_pair6 || destruct_pair4 || destruct_pair2)
	end; subst.