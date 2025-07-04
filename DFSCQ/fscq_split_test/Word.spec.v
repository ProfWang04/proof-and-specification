
(** Fixed precision machine words *)

Require Import Arith Div2 NArith Bool Omega.
Require Import Nomega.
Require Import Wf_nat.
Require Import Eqdep_dec.
Require Import Program.Tactics.
Require Import Recdef.
Require Import Ring.
Require Import Ring_polynom.
Require Import ProofIrrelevance.
Require Import Psatz.

Set Implicit Arguments.


(** * Basic definitions and conversion to and from [nat] *)

Inductive word : nat -> Set :=
| WO : word O
| WS : bool -> forall n, word n -> word (S n).

Fixpoint wordToNat sz (w : word sz) : nat :=
  match w with
    | WO => O
    | WS false w' => (wordToNat w') * 2
    | WS true w' => S (wordToNat w' * 2)
  end.
Arguments wordToNat : simpl nomatch.

Fixpoint wordToNat' sz (w : word sz) : nat :=
  match w with
    | WO => O
    | WS false w' => 2 * wordToNat w'
    | WS true w' => S (2 * wordToNat w')
  end.

Theorem wordToNat_wordToNat' : forall sz (w : word sz),
  wordToNat w = wordToNat' w.

Fixpoint mod2 (n : nat) : bool :=
  match n with
    | 0 => false
    | 1 => true
    | S (S n') => mod2 n'
  end.

Fixpoint natToWord (sz n : nat) : word sz :=
  match sz with
    | O => WO
    | S sz' => WS (mod2 n) (natToWord sz' (div2 n))
  end.

Definition liftWord (sz : nat) (f : nat -> nat) (w: word sz) :=
  natToWord sz (f (wordToNat w)).

Fixpoint wordToN sz (w : word sz) : N :=
  match w with
    | WO => 0
    | WS false w' => 2 * wordToN w'
    | WS true w' => N.succ (2 * wordToN w')
  end%N.
Arguments wordToN : simpl nomatch.

Definition Nmod2 (n : N) : bool :=
  match n with
    | N0 => false
    | Npos (xO _) => false
    | _ => true
  end.

Definition wzero sz := natToWord sz 0.

Fixpoint wzero' (sz : nat) : word sz :=
  match sz with
    | O => WO
    | S sz' => WS false (wzero' sz')
  end.

Fixpoint posToWord (sz : nat) (p : positive) {struct p} : word sz :=
  match sz with
    | O => WO
    | S sz' =>
      match p with
        | xI p' => WS true (posToWord sz' p')
        | xO p' => WS false (posToWord sz' p')
        | xH => WS true (wzero' sz')
      end
  end.

Definition NToWord (sz : nat) (n : N) : word sz :=
  match n with
    | N0 => wzero' sz
    | Npos p => posToWord sz p
  end.

Fixpoint Npow2 (n : nat) : N :=
  match n with
    | O => 1
    | S n' => 2 * Npow2 n'
  end%N.


Ltac rethink :=
  match goal with
    | [ H : ?f ?n = _ |- ?f ?m = _ ] => replace m with n; simpl; auto
  end.

Theorem mod2_S_double : forall n, mod2 (S (2 * n)) = true.

Theorem mod2_double : forall n, mod2 (2 * n) = false.

Local Hint Resolve mod2_S_double mod2_double.

Theorem div2_double : forall n, div2 (2 * n) = n.

Theorem div2_S_double : forall n, div2 (S (2 * n)) = n.

Hint Rewrite div2_double div2_S_double : div2.

Theorem natToWord_wordToNat : forall sz w, natToWord sz (wordToNat w) = w.

Fixpoint pow2 (n : nat) : nat :=
  match n with
    | O => 1
    | S n' => 2 * pow2 n'
  end.

Lemma pow2_add_mul: forall a b,
  pow2 (a + b) = (pow2 a) * (pow2 b).

Lemma mult_pow2_bound: forall a b x y,
  x < pow2 a -> y < pow2 b -> x * y < pow2 (a + b).

Lemma mult_pow2_bound_ex: forall a c x y,
  x < pow2 a -> y < pow2 (c - a) -> c >= a -> x * y < pow2 c.

Lemma lt_mul_mono' : forall c a b,
  a < b -> a < b * (S c).

Lemma lt_mul_mono : forall a b c,
  c <> 0 -> a < b -> a < b * c.

Lemma zero_lt_pow2 : forall sz, 0 < pow2 sz.

Lemma one_lt_pow2:
  forall n,
    1 < pow2 (S n).

Lemma mul2_add : forall n, n * 2 = n + n.

Lemma pow2_le_S : forall sz, (pow2 sz) + 1 <= pow2 (sz + 1).

Lemma pow2_bound_mono: forall a b x,
  x < pow2 a -> a <= b -> x < pow2 b.


Lemma pow2_inc : forall n m,
  0 < n -> n < m ->
    pow2 n < pow2 m.

Theorem roundTrip_0 : forall sz, wordToNat (natToWord sz 0) = 0.

Hint Rewrite roundTrip_0 : wordToNat.

Local Hint Extern 1 (@eq nat _ _) => omega.

Theorem untimes2 : forall n, n + (n + 0) = 2 * n.

Section strong.
  Variable P : nat -> Prop.

  Hypothesis PH : forall n, (forall m, m < n -> P m) -> P n.

  Lemma strong' : forall n m, m <= n -> P m.

  Theorem strong : forall n, P n.
End strong.

Theorem div2_odd : forall n,
  mod2 n = true
  -> n = S (2 * div2 n).

Theorem div2_even : forall n,
  mod2 n = false
  -> n = 2 * div2 n.

Lemma wordToNat_natToWord' : forall sz w, exists k, wordToNat (natToWord sz w) + k * pow2 sz = w.

Theorem wordToNat_natToWord : forall sz w, exists k, wordToNat (natToWord sz w) = w - k * pow2 sz /\ k * pow2 sz <= w.

Definition wone sz := natToWord sz 1.

Fixpoint wones (sz : nat) : word sz :=
  match sz with
    | O => WO
    | S sz' => WS true (wones sz')
  end.


(** Comparisons *)

Fixpoint wmsb sz (w : word sz) (a : bool) : bool :=
  match w with
    | WO => a
    | WS b  x => wmsb x b
  end.

Definition whd sz (w : word (S sz)) : bool :=
  match w in word sz' return match sz' with
                               | O => unit
                               | S _ => bool
                             end with
    | WO => tt
    | WS b _ => b
  end.

Definition wtl sz (w : word (S sz)) : word sz :=
  match w in word sz' return match sz' with
                               | O => unit
                               | S sz'' => word sz''
                             end with
    | WO => tt
    | WS _ w' => w'
  end.

Theorem WS_neq : forall b1 b2 sz (w1 w2 : word sz),
  (b1 <> b2 \/ w1 <> w2)
  -> WS b1 w1 <> WS b2 w2.

Fixpoint rep_bit (n : nat) (b : word 1) : word n :=
  match n as n0 return (word n0) with
  | 0 => WO
  | S n0 => WS (whd b) (rep_bit n0 b)
  end.


(** Shattering **)

Lemma shatter_word : forall n (a : word n),
  match n return word n -> Prop with
    | O => fun a => a = WO
    | S _ => fun a => a = WS (whd a) (wtl a)
  end a.

Lemma shatter_word_S : forall n (a : word (S n)),
  exists b, exists c, a = WS b c.
Lemma shatter_word_0 : forall a : word 0,
  a = WO.

Hint Resolve shatter_word_0.

Theorem word0: forall (w : word 0), w = WO.

Definition weq : forall sz (x y : word sz), {x = y} + {x <> y}.
  refine (fix weq sz (x : word sz) : forall y : word sz, {x = y} + {x <> y} :=
    match x in word sz return forall y : word sz, {x = y} + {x <> y} with
      | WO => fun _ => left _ _
      | WS b x' => fun y => if bool_dec b (whd y)
        then if weq _ x' (wtl y) then left _ _ else right _ _
        else right _ _
    end); clear weq.

  abstract (symmetry; apply shatter_word_0).

  abstract (subst; symmetry; apply (shatter_word y)).

  abstract (rewrite (shatter_word y); simpl; intro; injection H; intros;
    apply n0; apply inj_pair2_eq_dec in H0; [ auto | apply eq_nat_dec ]).

  abstract (rewrite (shatter_word y); simpl; intro; apply n0; injection H; auto).

Fixpoint weqb sz (x : word sz) : word sz -> bool :=
  match x in word sz return word sz -> bool with
    | WO => fun _ => true
    | WS b x' => fun y => 
      if eqb b (whd y)
      then if @weqb _ x' (wtl y) then true else false
      else false
  end.

Theorem weqb_true_iff : forall sz x y,
  @weqb sz x y = true <-> x = y.

(** * Dependent type helpers *)

Theorem eq_rect_nat_double : forall T (a b c : nat) x ab bc,
  eq_rect b T (eq_rect a T x b ab) c bc = eq_rect a T x c (eq_trans ab bc).

Hint Rewrite eq_rect_nat_double.
Hint Rewrite <- (eq_rect_eq_dec eq_nat_dec).

Ltac generalize_proof :=
    match goal with
    | [ |- context[eq_rect _ _ _ _ ?H ] ] => generalize H
    end.

Ltac eq_rect_simpl :=
  unfold eq_rec_r, eq_rec;
  repeat rewrite eq_rect_nat_double;
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).

Lemma eq_rect_word_offset_helper : forall a b c,
  a = b -> c + a = c + b.

Theorem eq_rect_word_offset : forall n n' offset w Heq,
  eq_rect n (fun n => word (offset + n)) w n' Heq =
  eq_rect (offset + n) (fun n => word n) w (offset + n') (eq_rect_word_offset_helper _ Heq).

Lemma eq_rect_word_mult_helper : forall a b c,
  a = b -> a * c = b * c.

Theorem eq_rect_word_mult : forall n n' scale w Heq,
  eq_rect n (fun n => word (n * scale)) w n' Heq =
  eq_rect (n * scale) (fun n => word n) w (n' * scale) (eq_rect_word_mult_helper _ Heq).

Theorem eq_rect_word_match : forall n n' (w : word n) (H : n = n'),
  match H in (_ = N) return (word N) with
  | eq_refl => w
  end = eq_rect n (fun n => word n) w n' H.

Theorem whd_match : forall n n' (w : word (S n)) (Heq : S n = S n'),
  whd w = whd (match Heq in (_ = N) return (word N) with
               | eq_refl => w
               end).

Theorem wtl_match : forall n n' (w : word (S n)) (Heq : S n = S n') (Heq' : n = n'),
  (match Heq' in (_ = N) return (word N) with
   | eq_refl => wtl w
   end) = wtl (match Heq in (_ = N) return (word N) with
               | eq_refl => w
               end).

(** * Combining and splitting *)

Fixpoint combine (sz1 : nat) (w : word sz1) : forall sz2, word sz2 -> word (sz1 + sz2) :=
  match w in word sz1 return forall sz2, word sz2 -> word (sz1 + sz2) with
    | WO => fun _ w' => w'
    | WS b w' => fun _ w'' => WS b (combine w' w'')
  end.

Fixpoint split1 (sz1 sz2 : nat) : word (sz1 + sz2) -> word sz1 :=
  match sz1 with
    | O => fun _ => WO
    | S sz1' => fun w => WS (whd w) (split1 sz1' sz2 (wtl w))
  end.

Fixpoint split2 (sz1 sz2 : nat) : word (sz1 + sz2) -> word sz2 :=
  match sz1 with
    | O => fun w => w
    | S sz1' => fun w => split2 sz1' sz2 (wtl w)
  end.

Ltac shatterer := simpl; intuition;
  match goal with
    | [ w : _ |- _ ] => rewrite (shatter_word w); simpl
  end; f_equal; auto.

Theorem combine_split : forall sz1 sz2 (w : word (sz1 + sz2)),
  combine (split1 sz1 sz2 w) (split2 sz1 sz2 w) = w.

Theorem split1_combine : forall sz1 sz2 (w : word sz1) (z : word sz2),
  split1 sz1 sz2 (combine w z) = w.

Theorem split2_combine : forall sz1 sz2 (w : word sz1) (z : word sz2),
  split2 sz1 sz2 (combine w z) = z.

Hint Rewrite combine_split.
Hint Rewrite split1_combine.
Hint Rewrite split2_combine.

Theorem combine_assoc : forall n1 (w1 : word n1) n2 n3 (w2 : word n2) (w3 : word n3) Heq,
  combine (combine w1 w2) w3
  = match Heq in _ = N return word N with
      | refl_equal => combine w1 (combine w2 w3)
    end.

Theorem split1_iter : forall n1 n2 n3 Heq w,
  split1 n1 n2 (split1 (n1 + n2) n3 w)
  = split1 n1 (n2 + n3) (match Heq in _ = N return word N with
                           | refl_equal => w
                         end).

Theorem split2_iter : forall n1 n2 n3 Heq w,
  split2 n2 n3 (split2 n1 (n2 + n3) w)
  = split2 (n1 + n2) n3 (match Heq in _ = N return word N with
                           | refl_equal => w
                         end).

Theorem split1_split2 : forall n1 n2 n3 Heq w,
  split1 n2 n3 (split2 n1 (n2 + n3) w) =
  split2 n1 n2 (split1 (n1 + n2) n3 (match Heq in _ = N return word N with
                                     | refl_equal => w
                                     end)).

Theorem split2_split1 : forall n1 n2 n3 Heq w,
  split2 n1 n2 (split1 (n1+n2) n3 w) =
  split1 n2 n3 (split2 n1 (n2+n3) (match Heq in _ = N return word N with
                                     | refl_equal => w
                                     end)).

Theorem combine_0_n : forall sz2 (w: word 0) (v: word sz2),
  combine w v = v.

Lemma WS_eq_rect : forall b n (w: word n) n' H H',
  eq_rect _ word (@WS b n w) _ H = @WS b n' (eq_rect _ word w _ H').

Theorem combine_eq_rect2 : forall sz n n'
  (H: n = n') H'
  (a: word sz) (b: word n),
  combine a b =
    eq_rect _ word (combine a (eq_rect _ word b _ H)) _ H'.

Theorem combine_n_0 : forall sz1 (w : word sz1) (v : word 0),
  combine w v = eq_rect _ word w _ (plus_n_O sz1).

Lemma whd_eq_rect : forall n w Heq,
  whd (eq_rect (S n) word w (S (n + 0)) Heq) =
  whd w.

Lemma wtl_eq_rect : forall n w Heq Heq',
  wtl (eq_rect (S n) word w (S (n + 0)) Heq) =
  eq_rect n word (wtl w) (n + 0) Heq'.

Lemma whd_eq_rect_mul : forall n w Heq,
  whd (eq_rect (S n) word w (S (n * 1)) Heq) =
  whd w.

Lemma wtl_eq_rect_mul : forall n w b Heq Heq',
  wtl (eq_rect (S n) word (WS b w) (S (n * 1)) Heq) =
  eq_rect _ word w _ Heq'.

Theorem split1_0 : forall n w Heq,
  split1 n 0 (eq_rect _ word w _ Heq) = w.

Theorem split2_0 : forall n w Heq,
  split2 0 n (eq_rect _ word w _ Heq) = w.

Theorem combine_end : forall n1 n2 n3 Heq w,
  combine (split1 n2 n3 (split2 n1 (n2 + n3) w))
  (split2 (n1 + n2) n3 (match Heq in _ = N return word N with
                          | refl_equal => w
                        end))
  = split2 n1 (n2 + n3) w.

Theorem eq_rect_combine : forall n1 n2 n2' (w1 : word n1) (w2 : word n2') Heq,
  eq_rect (n1 + n2') (fun n => word n)
    (combine w1 w2) (n1 + n2) Heq =
  combine w1 (eq_rect n2' (fun n => word n) w2 n2 (plus_reg_l _ _ _ Heq)).


Lemma eq_rect_combine_assoc' : forall a b c H wa wb wc,
  eq_rect (a + (b + c)) word (combine wa (combine wb wc)) _ H = combine (combine wa wb) wc.

Lemma eq_rect_split2_helper : forall a b c,
  a = b -> c + a = c + b.

Theorem eq_rect_split2 : forall n1 n2 n2' (w : word (n1 + n2')) Heq,
  eq_rect n2' (fun n => word n)
    (split2 n1 n2' w) n2 Heq =
  split2 n1 n2 (eq_rect (n1+n2') (fun n => word n) w (n1+n2) (eq_rect_split2_helper _ Heq)).

Theorem eq_rect_split2_eq2 : forall n1 n2 n2' (w : word (n1 + n2)) Heq Heq2,
  eq_rect n2 (fun n => word n)
    (split2 n1 n2 w) n2' Heq =
  split2 n1 n2' (eq_rect (n1+n2) (fun n => word n) w (n1+n2') Heq2).

Theorem eq_rect_split2_eq1 : forall n1 n1' n2 (w: word (n1 + n2)) Heq,
     split2 n1 n2 w = split2 n1' n2
        (eq_rect (n1 + n2) (fun y : nat => word y) w
     (n1' + n2) Heq).

Theorem combine_split_eq_rect2 : forall n1 n2 n2' (w : word (n1 + n2)) Heq,
  combine (split1 n1 n2 w)
          (eq_rect n2 (fun n => word n) (split2 n1 n2 w)
                   n2' Heq) =
  eq_rect (n1 + n2) (fun n => word n) w
          (n1 + n2') (eq_rect_split2_helper _ Heq).

Lemma eq_rect_split1_helper : forall a b c,
  a = b -> a + c = b + c.

Lemma eq_rect_split1_eq2_helper : forall a b c,
  a = b -> c + a = c + b.

Theorem eq_rect_split1 : forall n1 n1' n2 (w : word (n1' + n2)) Heq,
  eq_rect n1' (fun n => word n)
    (split1 n1' n2 w) n1 Heq =
  split1 n1 n2 (eq_rect (n1'+n2) (fun n => word n) w (n1+n2) (eq_rect_split1_helper _ Heq)).

Theorem eq_rect_split1_eq1 : forall n1 n1' n2 (w : word (n1 + n2)) Heq Heq1,
  eq_rect n1 (fun n => word n)
    (split1 n1 n2 w) n1' Heq =
  split1 n1' n2 (eq_rect (n1+n2) (fun n => word n) w (n1'+n2) Heq1).

Lemma split1_eq_rect_eq1_helper : forall a b c, b = a -> a + c = b + c.
Theorem split1_eq_rect_eq1 : forall a a' b H w,
  split1 a b w = eq_rect _ word (split1 a' b
    (eq_rect _ word w _ (split1_eq_rect_eq1_helper b H))) _ H.

Theorem eq_rect_split1_eq2 : forall n1 n2 n2' (w: word (n1 + n2)) Heq,
     split1 n1 n2 w = split1 n1 n2'
        (eq_rect (n1 + n2) (fun y : nat => word y) w
     (n1 + n2') Heq).

Fact eq_rect_combine_dist_helper1 : forall a b c d, b * c = d -> (a + b) * c = a * c + d.
Theorem eq_rect_combine_dist : forall a b c d (w : word ((a + b) * c)) (H : b * c = d),
  b * c = d ->
  let H1 := (eq_rect_combine_dist_helper1 a b c H) in
  let H2 := (eq_rect_combine_dist_helper2 a b c H) in
  let w' := eq_rec ((a + b) * c) word w _ H1 in
  w = eq_rec _ word (combine (split1 (a * c) d w') (split2 (a * c) d w')) _ H2.

Lemma wzero_dist : forall a b c H,
  wzero ((a + b) * c) = eq_rect _ word (wzero (a * c + b * c)) _ H.

Lemma wzero_rev : forall (a b : nat) H,
   wzero (a + b) = eq_rect _ word (wzero (b + a)) _ H.
Lemma split1_zero : forall sz1 sz2, split1 sz1 sz2 (natToWord _ O) = natToWord _ O.

Lemma split2_zero : forall sz1 sz2, split2 sz1 sz2 (natToWord _ O) = natToWord _ O.

Theorem combine_inj : forall sz1 sz2 a b c d,
  @combine sz1 a sz2 b = @combine sz1 c sz2 d -> a = c /\ b = d.

Theorem combine_wzero : forall sz1 sz2, combine (wzero sz1) (wzero sz2) = wzero (sz1 + sz2).

Theorem combine_wones : forall sz1 sz2, combine (wones sz1) (wones sz2) = wones (sz1 + sz2).

(** * Extension operators *)

Definition sext (sz : nat) (w : word sz) (sz' : nat) : word (sz + sz') :=
  if wmsb w false then
    combine w (wones sz')
  else 
    combine w (wzero sz').

Definition zext (sz : nat) (w : word sz) (sz' : nat) : word (sz + sz') :=
  combine w (wzero sz').


(** * Arithmetic *)

Definition wneg sz (x : word sz) : word sz :=
  NToWord sz (Npow2 sz - wordToN x).

Definition wordBin (f : N -> N -> N) sz (x y : word sz) : word sz :=
  NToWord sz (f (wordToN x) (wordToN y)).

Definition wplus := wordBin Nplus.
Definition wmult := wordBin Nmult.
Definition wdiv := wordBin N.div.
Definition wmod := wordBin Nmod.
Definition wmult' sz (x y : word sz) : word sz := 
  split2 sz sz (NToWord (sz + sz) (Nmult (wordToN x) (wordToN y))).
Definition wminus sz (x y : word sz) : word sz := wplus x (wneg y).
Definition wnegN sz (x : word sz) : word sz :=
  natToWord sz (pow2 sz - wordToNat x).

Definition wordBinN (f : nat -> nat -> nat) sz (x y : word sz) : word sz :=
  natToWord sz (f (wordToNat x) (wordToNat y)).

Definition wplusN := wordBinN plus.

Definition wmultN := wordBinN mult.
Definition wmultN' sz (x y : word sz) : word sz := 
  split2 sz sz (natToWord (sz + sz) (mult (wordToNat x) (wordToNat y))).

Definition wminusN sz (x y : word sz) : word sz := wplusN x (wnegN y).

(** * Notations *)

Delimit Scope word_scope with word.
Bind Scope word_scope with word.

Notation "w ~ 1" := (WS true w)
 (at level 7, left associativity, format "w '~' '1'") : word_scope.
Notation "w ~ 0" := (WS false w)
 (at level 7, left associativity, format "w '~' '0'") : word_scope.

Notation "^~" := wneg.
Notation "l ^+ r" := (@wplus _ l%word r%word) (at level 50, left associativity).
Notation "l ^* r" := (@wmult _ l%word r%word) (at level 40, left associativity).
Notation "l ^- r" := (@wminus _ l%word r%word) (at level 50, left associativity).
Notation "l ^/ r" := (@wdiv _ l%word r%word) (at level 50, left associativity).
Notation "l ^% r" := (@wmod _ l%word r%word) (at level 50, left associativity).

Theorem wordToN_nat : forall sz (w : word sz), wordToN w = N_of_nat (wordToNat w).

Theorem mod2_S : forall n k,
  2 * k = S n
  -> mod2 n = true.

Theorem wzero'_def : forall sz, wzero' sz = wzero sz.

Theorem posToWord_nat : forall p sz, posToWord sz p = natToWord sz (nat_of_P p).

Theorem NToWord_nat : forall sz n, NToWord sz n = natToWord sz (nat_of_N n).

Theorem wplus_alt : forall sz (x y : word sz), wplus x y = wplusN x y.

Theorem wmult_alt : forall sz (x y : word sz), wmult x y = wmultN x y.

Theorem Npow2_nat : forall n, nat_of_N (Npow2 n) = pow2 n.

Theorem pow2_N : forall n, Npow2 n = N.of_nat (pow2 n).

Theorem wneg_alt : forall sz (x : word sz), wneg x = wnegN x.

Theorem wminus_Alt : forall sz (x y : word sz), wminus x y = wminusN x y.

Theorem wplus_unit : forall sz (x : word sz), natToWord sz 0 ^+ x = x.

Theorem wplus_comm : forall sz (x y : word sz), x ^+ y = y ^+ x.

Theorem drop_mod2 : forall n k,
  2 * k <= n
  -> mod2 (n - 2 * k) = mod2 n.

Theorem div2_minus_2 : forall n k,
  2 * k <= n
  -> div2 (n - 2 * k) = div2 n - k.

Theorem div2_bound : forall k n,
  2 * k <= n
  -> k <= div2 n.

Theorem drop_sub : forall sz n k,
  k * pow2 sz <= n
  -> natToWord sz (n - k * pow2 sz) = natToWord sz n.

Lemma mod2_S_S : forall n,
  mod2 (S (S n)) = mod2 n.

Lemma mod2_S_not : forall n,
  mod2 (S n) = if (mod2 n) then false else true.

Lemma mod2_S_eq : forall n k,
  mod2 n = mod2 k ->
  mod2 (S n) = mod2 (S k).

Theorem drop_mod2_add : forall n k,
  mod2 (n + 2 * k) = mod2 n.

Theorem div2_plus_2 : forall n k,
  div2 (n + 2 * k) = div2 n + k.

Theorem drop_add : forall sz n k,
  natToWord sz (n + k * pow2 sz) = natToWord sz n.


Local Hint Extern 1 (_ <= _) => omega.

Theorem wplus_assoc : forall sz (x y z : word sz), x ^+ (y ^+ z) = x ^+ y ^+ z.

Theorem roundTrip_1 : forall sz, wordToNat (natToWord (S sz) 1) = 1.

Theorem mod2_WS : forall sz (x : word sz) b, mod2 (wordToNat (WS b x)) = b.

Theorem div2_WS : forall sz (x : word sz) b, div2 (wordToNat (WS b x)) = wordToNat x.

Theorem wmult_unit_l : forall sz (x : word sz), natToWord sz 1 ^* x = x.

Theorem wmult_comm : forall sz (x y : word sz), x ^* y = y ^* x.

Theorem wmult_unit_r : forall sz (x : word sz), x ^* natToWord sz 1 = x.

Theorem wmult_assoc : forall sz (x y z : word sz), x ^* (y ^* z) = x ^* y ^* z.

Theorem wmult_plus_distr : forall sz (x y z : word sz), (x ^+ y) ^* z = (x ^* z) ^+ (y ^* z).

Theorem wminus_def : forall sz (x y : word sz), x ^- y = x ^+ ^~ y.

Theorem wordToNat_bound : forall sz (w : word sz), wordToNat w < pow2 sz.

Definition goodSize sz n := n < pow2 sz.
Arguments goodSize : simpl never.

Definition goodSizeEq sz n := n <= pow2 sz.
Arguments goodSizeEq : simpl never.

Theorem wordToNat_good : forall sz (w : word sz), goodSize sz (wordToNat w).

Theorem natToWord_goodSize:
  forall sz (w:word sz),
  goodSize sz (wordToNat w).

Theorem goodSize_trans: forall sz n1 n2,
  n1 <= n2 -> goodSize sz n2 -> goodSize sz n1.

Theorem goodSize_word_bound: forall n1 sz (bound: word sz),
  n1 <= wordToNat bound ->
  goodSize sz n1.


Theorem goodSize_bound: forall n1 sz bound,
  n1 <= wordToNat (natToWord sz bound) ->
  goodSize sz n1.

Lemma goodSize_sub : forall sz n a,
  goodSize sz n -> goodSize sz (n - a).


Lemma wordToNat_natToWord_idempotent'_iff : forall n sz,
  @wordToNat sz (natToWord sz n) = n -> goodSize sz n.

Lemma goodSize_add_l : forall sz a b,
  goodSize sz (a + b) -> goodSize sz a.

Lemma goodSize_add_r : forall sz a b,
  goodSize sz (a + b) -> goodSize sz b.


Theorem natToWord_pow2 : forall sz, natToWord sz (pow2 sz) = natToWord sz 0.

Theorem wminus_inv : forall sz (x : word sz), x ^+ ^~ x = wzero sz.

Definition wring (sz : nat) : ring_theory (wzero sz) (wone sz) (@wplus sz) (@wmult sz) (@wminus sz) (@wneg sz) (@eq _) :=
  mk_rt _ _ _ _ _ _ _
  (@wplus_unit _) (@wplus_comm _) (@wplus_assoc _)
  (@wmult_unit_l _) (@wmult_comm _) (@wmult_assoc _)
  (@wmult_plus_distr _) (@wminus_def _) (@wminus_inv _).

Theorem weqb_sound : forall sz (x y : word sz), weqb x y = true -> x = y.

Arguments weqb_sound : clear implicits.

Ltac is_nat_cst n :=
  match eval hnf in n with
    | O => constr:(true)
    | S ?n' => is_nat_cst n'
    | _ => constr:(false)
  end.

Ltac isWcst w :=
  match eval hnf in w with
    | WO => constr:(true)
    | WS ?b ?w' =>
      match eval hnf in b with
        | true => isWcst w'
        | false => isWcst w'
        | _ => constr:(false)
      end
    | natToWord _ ?n => is_nat_cst n
    | _ => constr:(false)
  end.

Ltac wcst w :=
  let b := isWcst w in
    match b with
      | true => w
      | _ => constr:(NotConstant)
    end.

(* Here's how you can add a ring for a specific bit-width.
   There doesn't seem to be a polymorphic method, so this code really does need to be copied. *)

(*
Definition wring8 := wring 8.
Add Ring wring8 : wring8 (decidable (weqb_sound 8), constants [wcst]).
*)

Ltac noptac x := idtac.

Ltac PackWring sz F :=
  let RNG := (fun proj => proj
    inv_morph_nothing inv_morph_nothing noptac noptac
    (word sz) (@eq (word sz)) (wzero sz) (wone sz)
    (@wplus sz) (@wmult sz) (@wminus sz) (@wneg sz)
    (BinNums.Z) (BinNums.N) (id_phi_N)
    (pow_N (wone sz) (@wmult sz))
    (ring_correct (@Eqsth (word sz))
                  (Eq_ext _ _ _)
                  (Rth_ARth (@Eqsth (word sz)) (Eq_ext _ _ _) (wring sz))
                  (gen_phiZ_morph (@Eqsth (word sz)) (Eq_ext _ _ _) (wring sz))
                  (pow_N_th _ _ (@Eqsth (word sz)))
                  (triv_div_th (@Eqsth (word sz))
                               (Eq_ext _ _ _)
                               (Rth_ARth (@Eqsth (word sz)) (Eq_ext _ _ _) (wring sz))
                               (gen_phiZ_morph (@Eqsth (word sz)) (Eq_ext _ _ _) (wring sz)))
    )
    tt) in
  F RNG (@nil (word sz)) (@nil (word sz)).

Ltac ring_sz sz := PackWring sz Ring_gen.


(** * Bitwise operators *)

Fixpoint wnot sz (w : word sz) : word sz :=
  match w with
    | WO => WO
    | WS b w' => WS (negb b) (wnot w')
  end.

Fixpoint bitwp (f : bool -> bool -> bool) sz (w1 : word sz) : word sz -> word sz :=
  match w1 with
    | WO => fun _ => WO
    | WS b w1' => fun w2 => WS (f b (whd w2)) (bitwp f w1' (wtl w2))
  end.

Fact bitwp_wtl : forall sz (w w' : word (S sz)) op, bitwp op (wtl w) (wtl w') = wtl (bitwp op w w').

Lemma split1_bitwp_dist : forall sz1 sz2 w w' op,
  split1 sz1 sz2 (bitwp op w w') = bitwp op (split1 sz1 sz2 w) (split1 sz1 sz2 w').

Lemma split2_bitwp_dist : forall sz1 sz2 w w' op,
  split2 sz1 sz2 (bitwp op w w') = bitwp op (split2 sz1 sz2 w) (split2 sz1 sz2 w').

Lemma combine_bitwp : forall sz1 sz2 (wa wa' : word sz1) (wb wb' : word sz2) op,
  combine (bitwp op wa wa') (bitwp op wb wb') = bitwp op (combine wa wb) (combine wa' wb').

Lemma eq_rect_bitwp : forall a b Heq f w1 w2,
  bitwp f w1 w2 = eq_rect a word (
    bitwp f (eq_rect b word w1 a Heq) (eq_rect b word w2 a Heq)) b (eq_sym Heq).

Fact eq_rect_bitwp' : forall a b Heq f w1 w2,
  eq_rect b word (bitwp f w1 w2) a Heq = bitwp f (eq_rect b word w1 a Heq) (eq_rect b word w2 a Heq).

Fact eq_rect_bitwp_1 : forall a b Heq f w1 w2,
  bitwp f (eq_rect a word w1 b Heq) w2 = eq_rect a word (bitwp f w1 (eq_rect b word w2 a (eq_sym Heq))) b Heq.

Definition wnot' sz := bitwp xorb (wones sz).

Theorem wnot_wnot'_equiv : forall sz (w : word sz), wnot w = wnot' w.

Theorem wnot_split1 : forall sz1 sz2 w, wnot (split1 sz1 sz2 w) = split1 sz1 sz2 (wnot w).

Theorem wnot_split2 : forall sz1 sz2 w, wnot (split2 sz1 sz2 w) = split2 sz1 sz2 (wnot w).

Theorem wnot_combine : forall sz1 sz2 (w1 : word sz1) (w2 : word sz2),
  wnot (combine w1 w2) = combine (wnot w1) (wnot w2).

Theorem wnot_zero: forall sz, wnot (wzero sz) = wones sz.

Theorem wnot_ones : forall sz, wnot (wones sz) = wzero sz.

Theorem wnot_eq_rect : forall a b H (w : word a), wnot (eq_rect a word w b H) = eq_rect a word (wnot w) b H.

Definition wor := bitwp orb.
Definition wand := bitwp andb.
Definition wxor := bitwp xorb.

Notation "l ^| r" := (@wor _ l%word r%word) (at level 50, left associativity).
Notation "l ^& r" := (@wand _ l%word r%word) (at level 40, left associativity).

Theorem wor_unit : forall sz (x : word sz), wzero sz ^| x = x.

Theorem wor_comm : forall sz (x y : word sz), x ^| y = y ^| x.

Theorem wor_assoc : forall sz (x y z : word sz), x ^| (y ^| z) = x ^| y ^| z.

Theorem wand_unit : forall sz (x : word sz), wones sz ^& x = x.

Theorem wand_kill : forall sz (x : word sz), wzero sz ^& x = wzero sz.

Theorem wand_comm : forall sz (x y : word sz), x ^& y = y ^& x.

Theorem wand_assoc : forall sz (x y z : word sz), x ^& (y ^& z) = x ^& y ^& z.

Theorem wand_or_distr : forall sz (x y z : word sz), (x ^| y) ^& z = (x ^& z) ^| (y ^& z).

Lemma wor_wones : forall sz w, wones sz ^| w = wones sz.

Lemma wor_wzero : forall sz w, wzero sz ^| w = w.

Lemma wand_wones : forall sz w, wones sz ^& w = w.

Lemma wand_wzero : forall sz w, wzero sz ^& w = wzero sz.

Lemma wxor_wones : forall sz w, wxor (wones sz) w = wnot w.

Lemma wxor_wzero : forall sz w, wxor (wzero sz) w = w.

Lemma wxor_comm : forall sz (w1 w2 : word sz), wxor w1 w2 = wxor w2 w1.

Lemma wxor_assoc : forall sz (w1 w2 w3 : word sz), wxor w1 (wxor w2 w3) = wxor (wxor w1 w2) w3.

Lemma wor_wone : forall sz (w : word sz) b,
  WS b w ^| wone _ = WS true w.

Lemma wand_wone : forall sz (w : word sz) b,
  WS b w ^& wone _ = WS b (wzero _).

Lemma wxor_wone : forall sz (w : word sz) b,
  wxor (WS b w) (wone _) = WS (negb b) w.

Definition wbring (sz : nat) : semi_ring_theory (wzero sz) (wones sz) (@wor sz) (@wand sz) (@eq _) :=
  mk_srt _ _ _ _ _
  (@wor_unit _) (@wor_comm _) (@wor_assoc _)
  (@wand_unit _) (@wand_kill _) (@wand_comm _) (@wand_assoc _)
  (@wand_or_distr _).


(** * Inequality proofs *)

Ltac word_simpl := unfold sext, zext, wzero in *; simpl in *.

Ltac word_eq := ring.

Ltac word_eq1 := match goal with
                   | _ => ring
                   | [ H : _ = _ |- _ ] => ring [H]
                 end.

Theorem word_neq : forall sz (w1 w2 : word sz),
  w1 ^- w2 <> wzero sz
  -> w1 <> w2.

Ltac word_neq := apply word_neq; let H := fresh "H" in intro H; simpl in H; ring_simplify in H; try discriminate.

Ltac word_contra := match goal with 
                      | [ H : _ <> _ |- False ] => apply H; ring
                    end. 

Ltac word_contra1 := match goal with 
                       | [ H : _ <> _ |- False ] => apply H;
                         match goal with
                           | _ => ring
                           | [ H' : _ = _ |- _ ] => ring [H']
                         end
                     end.

Open Scope word_scope.

(** * Signed Logic **)
Fixpoint wordToZ sz (w : word sz) : Z :=
  if wmsb w true then 
    (** Negative **)
    match wordToN (wneg w) with
      | N0 => 0%Z
      | Npos x => Zneg x
    end
  else 
    (** Positive **)
    match wordToN w with
      | N0 => 0%Z
      | Npos x => Zpos x
    end.

(** * Comparison Predicates and Deciders **)
Definition wlt sz (l r : word sz) : Prop :=
  N.lt (wordToN l) (wordToN r).
Definition wslt sz (l r : word sz) : Prop :=
  Z.lt (wordToZ l) (wordToZ r).

Notation "w1 > w2" := (@wlt _ w2%word w1%word) : word_scope.
Notation "w1 >= w2" := (~(@wlt _ w1%word w2%word)) : word_scope.
Notation "w1 < w2" := (@wlt _ w1%word w2%word) : word_scope.
Notation "w1 <= w2" := (~(@wlt _ w2%word w1%word)) : word_scope.

Notation "w1 '>s' w2" := (@wslt _ w2%word w1%word) (at level 70, w2 at next level) : word_scope.
Notation "w1 '>s=' w2" := (~(@wslt _ w1%word w2%word)) (at level 70, w2 at next level) : word_scope.
Notation "w1 '<s' w2" := (@wslt _ w1%word w2%word) (at level 70, w2 at next level) : word_scope.
Notation "w1 '<s=' w2" := (~(@wslt _ w2%word w1%word)) (at level 70, w2 at next level) : word_scope.

Definition wlt_dec : forall sz (l r : word sz), {l < r} + {l >= r}.
  refine (fun sz l r => 
    match N.compare (wordToN l) (wordToN r) as k return N.compare (wordToN l) (wordToN r) = k -> _ with
      | Lt => fun pf => left _ _
      | _ => fun pf => right _ _
    end (refl_equal _));
  abstract congruence.

Definition wslt_dec : forall sz (l r : word sz), {l <s r} + {l >s= r}.
  refine (fun sz l r => 
    match Z.compare (wordToZ l) (wordToZ r) as c return Z.compare (wordToZ l) (wordToZ r) = c -> _ with
      | Lt => fun pf => left _ _
      | _ => fun pf => right _ _
    end (refl_equal _));
  abstract congruence.

Lemma not_wlt_ge : forall sz (l r : word sz),
  ((l < r) -> False) -> (r <= l).

Lemma not_wle_gt : forall sz (l r : word sz),
  ((l <= r) -> False) -> (r < l).

(* Ordering Lemmas **)
Lemma lt_le : forall sz (a b : word sz),
  a < b -> a <= b.
Lemma eq_le : forall sz (a b : word sz),
  a = b -> a <= b.
Lemma wordToN_inj : forall sz (a b : word sz),
  wordToN a = wordToN b -> a = b.
Lemma wordToNat_inj : forall sz (a b : word sz),
  wordToNat a = wordToNat b -> a = b.
Lemma unique_inverse : forall sz (a b1 b2 : word sz),
  a ^+ b1 = wzero _ ->
  a ^+ b2 = wzero _ ->
  b1 = b2.
Lemma sub_0_eq : forall sz (a b : word sz),
  a ^- b = wzero _ -> a = b.

Lemma le_neq_lt : forall sz (a b : word sz),
  b <= a -> a <> b -> b < a.


Hint Resolve word_neq lt_le eq_le sub_0_eq le_neq_lt : worder.

Ltac shatter_word x :=
  match type of x with
    | word 0 => try rewrite (shatter_word_0 x) in *
    | word (S ?N) => 
      let x' := fresh in 
      let H := fresh in
      destruct (@shatter_word_S N x) as [ ? [ x' H ] ];
      rewrite H in *; clear H; shatter_word x'
  end.


(** Uniqueness of equality proofs **)
Lemma rewrite_weq : forall sz (a b : word sz)
  (pf : a = b),  
  weq a b = left _ pf.


(** * Some more useful derived facts *)

Lemma natToWord_plus : forall sz n m, natToWord sz (n + m) = natToWord _ n ^+ natToWord _ m.

Lemma natToWord_S : forall sz n, natToWord sz (S n) = natToWord _ 1 ^+ natToWord _ n.

Theorem natToWord_inj : forall sz n m, natToWord sz n = natToWord sz m
  -> goodSize sz n
  -> goodSize sz m
  -> n = m.

Lemma wordToNat_natToWord_idempotent : forall sz n,
  (N.of_nat n < Npow2 sz)%N
  -> wordToNat (natToWord sz n) = n.

Lemma wplus_cancel : forall sz (a b c : word sz),
  a ^+ c = b ^+ c
  -> a = b.


(* Some additional useful facts added in the fscq version of Word.v *)

Lemma natToWord_mult : forall sz n m, natToWord sz (n * m) = natToWord _ n ^* natToWord _ m.

Lemma wlt_lt: forall sz (a b : word sz), a < b ->
  (wordToNat a < wordToNat b)%nat.

Lemma wle_le: forall sz (a b : word sz), (a <= b)%word ->
  (wordToNat a <= wordToNat b)%nat.

Lemma wlt_lt': forall sz a b, goodSize sz a
  -> natToWord sz a < b
  -> (wordToNat (natToWord sz a) < wordToNat b)%nat.

Lemma lt_word_lt_nat : forall (sz:nat) (n:word sz) (m:nat),
  (n < (natToWord sz m))%word ->
  (wordToNat n < m)%nat.

Lemma le_word_le_nat : forall (sz:nat) (n:word sz) (m:nat),
  (n <= (natToWord sz m))%word ->
  (wordToNat n <= m)%nat.

(* Chain [lt_word_lt_nat] and [Nat.lt_le_incl]
    Avoids using [Hint Resolve Nat.lt_le_incl] for this specific lemma,
    though this may be a premature optimization. *)
Lemma lt_word_le_nat : forall (sz:nat) (n:word sz) (m:nat),
  (n < (natToWord sz m))%word ->
  (wordToNat n <= m)%nat.

Hint Resolve lt_word_le_nat.

Lemma wordToNat_natToWord_idempotent' : forall sz n,
  goodSize sz n
  -> wordToNat (natToWord sz n) = n.

Lemma le_word_le_nat': forall (sz:nat) n m,
  goodSize sz n ->
  (natToWord sz n <= m)%word ->
  (n <= wordToNat m)%nat.

Lemma wordToNat_natToWord_bound : forall sz n (bound : word sz),
  (n <= wordToNat bound)%nat
  -> wordToNat (natToWord sz n) = n.

Lemma wordToNat_natToWord_le : forall sz n,
  (wordToNat (natToWord sz n) <= n)%nat.

Lemma wordToNat_natToWord_lt : forall sz n b,
  (n < b -> wordToNat (natToWord sz n) < b)%nat.

Lemma wordToNat_eq_natToWord : forall sz (w : word sz) n,
  wordToNat w = n
  -> w = natToWord sz n.

Lemma wlt_lt_bound: forall sz (a : word sz) (b bound : nat),
  (a < natToWord sz b)%word
  -> (b <= wordToNat (natToWord sz bound))%nat
  -> (wordToNat a < b)%nat.

Lemma natplus1_wordplus1_eq:
  forall sz (a bound : word sz),
    (0 < sz)%nat ->
    (a < bound)%word ->
    (wordToNat a) + 1 = wordToNat (a ^+ (natToWord sz 1)).

Lemma lt_wlt: forall sz (n : word sz) m, (wordToNat n < wordToNat m)%nat ->
  n < m.

Lemma le_wle: forall sz (n : word sz) m, (wordToNat n <= wordToNat m)%nat ->
  n <= m.

Lemma wlt_wle_incl : forall sz (a b : word sz),
  (a < b)%word -> (a <= b)%word.

Lemma wminus_Alt2: forall sz x y, y <= x ->
  @wminusN sz x y = wordBinN minus x y.

Theorem wlt_wf:
  forall sz, well_founded (@wlt sz).

Ltac wlt_ind :=
  match goal with
  | [ |- forall (n: word ?len), ?P ] =>
    refine (well_founded_ind (@wlt_wf len) (fun n => P) _)
  end.

Theorem wordToNat_plusone: forall sz w w', w < w' ->
  wordToNat (w ^+ natToWord sz 1) = S (wordToNat w).


Theorem wordToNat_minus_one': forall sz n, n <> natToWord sz 0 ->
  S (wordToNat (n ^- natToWord sz 1)) = wordToNat n.

Theorem wordToNat_minus_one: forall sz n, n <> natToWord sz 0 ->
  wordToNat (n ^- natToWord sz 1) = wordToNat n - 1.

Lemma lt_minus : forall a b c,
  (b <= a -> b < c -> a < c -> a - b < c)%nat.

Lemma wminus_minus : forall sz (a b : word sz),
  b <= a
  -> wordToNat (a ^- b) = wordToNat a - wordToNat b.

Lemma wordToNat_neq_inj: forall sz (a b : word sz),
  a <> b <-> wordToNat a <> wordToNat b.

Lemma natToWord_discriminate: forall sz, (sz > 0)%nat -> natToWord sz 0 <> natToWord sz 1.

Notation "$ n" := (natToWord _ n) (at level 0).
Notation "# n" := (wordToNat n) (at level 0).

Definition bit_dec : forall (a : word 1), {a = $0} + {a = $1}.
  intro.
  rewrite (shatter_word a).
  replace (wtl a) with WO by auto.
  destruct (whd a).
  right; apply eq_refl.
  left; apply eq_refl.

Lemma neq0_wneq0: forall sz (n : word sz),
  wordToNat n <> 0  <-> n <> $0.

Lemma gt0_wneq0: forall sz (n : word sz),
  (wordToNat n > 0)%nat <-> n <> $0.

Lemma weq_minus1_wlt: forall sz (a b : word sz),
  (a <> $0 -> a ^- $1 = b -> a > b)%word.

Lemma wordnat_minus1_eq : forall sz n (w : word sz),
  (n > 0)%nat
  -> n = wordToNat w
  -> n - 1 = wordToNat (w ^- $1).

(* Bit shifting *)

Lemma sz_minus_nshift : forall sz nshift, (nshift < sz)%nat -> sz = sz - nshift + nshift.

Lemma nshift_plus_nkeep : forall sz nshift, (nshift < sz)%nat -> nshift + (sz - nshift) = sz.

Definition wlshift (sz : nat) (w : word sz) (n : nat) : word sz.
  refine (split1 sz n _).
  rewrite plus_comm.
  exact (combine (wzero n) w).

Definition wrshift (sz : nat) (w : word sz) (n : nat) : word sz.
  refine (split2 n sz _).
  rewrite plus_comm.
  exact (combine w (wzero n)).

Notation "l ^<< r" := (@wlshift _ _ l%word r%word) (at level 35).
Notation "l ^>> r" := (@wrshift _ _ l%word r%word) (at level 35).

Theorem wlshift_0 : forall sz (w : word sz), @wlshift sz w 0 = w.

Theorem wrshift_0 : forall sz (w : word sz), @wrshift sz w 0 = w.

Theorem wlshift_gt : forall sz n (w : word sz), (n > sz)%nat ->
  wlshift w n = wzero sz.

Theorem wrshift_gt : forall sz n (w : word sz), (n > sz)%nat ->
  wrshift w n = wzero sz.

Theorem wlshift_bitwp : forall sz (w1 w2 : word sz) f n,
  wlshift (bitwp f w1 w2) n = split1 sz n (
    eq_rec _ word (combine (wzero n) (bitwp f w1 w2)) _ (eq_sym (Nat.add_comm sz n))).

Theorem wrshift_bitwp : forall sz (w1 w2 : word sz) f n,
  wrshift (bitwp f w1 w2) n = split2 n sz (
    eq_rect _ word (combine (bitwp f w1 w2) (wzero n)) _ (eq_sym (Nat.add_comm n sz))).

Theorem wnot_wlshift : forall sz (w : word sz) n,
  wnot (wlshift w n) = split1 sz n (eq_rect _ word (combine (wones n) (wnot w)) _ (eq_sym (Nat.add_comm sz n))).

Theorem wnot_wrshift : forall sz (w : word sz) n,
  wnot (wrshift w n) = split2 n sz (eq_rect _ word (combine (wnot w) (wones n)) _ (eq_sym (Nat.add_comm n sz))).

(* Setting an individual bit *)

Definition wbit sz sz' (n : word sz') := natToWord sz (pow2 (wordToNat n)).

Theorem div2_pow2_twice: forall n,
  Nat.div2 (pow2 n + (pow2 n + 0)) = pow2 n.

Theorem zero_or_wordToNat_S: forall sz (n : word sz),
  n = $0 \/
  exists nn, wordToNat n = S nn /\ wordToNat (n ^- $1) = nn.

Theorem wbit_or_same : forall sz sz' (n : word sz'), (wordToNat n < sz)%nat
  -> (wbit sz n) ^| (wbit sz n) <> wzero sz.

Theorem mod2_pow2_twice: forall n,
  mod2 (pow2 n + (pow2 n + 0)) = false.

Theorem wbit_or_other : forall sz sz' (n1 n2 : word sz'), (wordToNat n1 < sz)%nat
  -> (wordToNat n2 < sz)%nat
  -> (n1 <> n2)
  -> (wbit sz n1) ^& (wbit sz n2) = wzero sz.

Theorem wbit_and_not: forall sz sz' (n : word sz'), (wordToNat n < sz)%nat
  -> (wbit sz n) ^& wnot (wbit sz n) = wzero sz.

Theorem wbit_and_not_other: forall sz sz' (n1 n2 : word sz'), (wordToNat n1 < sz)%nat
  -> (wordToNat n2 < sz)%nat
  -> n1 <> n2
  -> (wbit sz n1) ^& wnot (wbit sz n2) = wbit sz n1.

(* Coq trunk seems to inherit open scopes across imports? *)
Close Scope word_scope.

(* Don't allow simpl to expand out these functions *)
Arguments natToWord : simpl never.
Arguments weq : simpl never.

(* Making wlt_dec opaque is necessary to prevent the [exact H] in the
 * example below from blowing up..
 *)
Global Opaque wlt_dec.
Definition test_wlt_f (a : nat) (b : nat) : nat :=
  if wlt_dec (natToWord 64 a) $0 then 0 else 0.
Theorem test_wlt_f_example: forall x y z, test_wlt_f x y = 0 -> test_wlt_f x z = 0.