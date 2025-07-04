Require Import Arith Omega.
Require Import Word.
Require Import WordAuto.
Require Import Psatz.

(* TODO: move byte-specific lemmas *)
Require Import AsyncDisk.
Import Valulen.

(** The divup and roundup functions and associated theorems.
    divup n sz performs n / sz, rounding up rather than down.
    roundup n sz rounds n to the smallest multiple of sz >= n;
     it is similar to the customary n / sz * sz, but uses divup instead of /.
*)

Definition divup (n unitsz : nat) : nat := (n + unitsz - 1) / unitsz.
Definition roundup (n unitsz:nat) : nat := (divup n unitsz) * unitsz.

  Lemma div_le_mul : forall n a b,
    b > 0 -> a > 0 -> n / a <= n * b.

  Lemma mul_div : forall a b,
    a mod b = 0 ->
    b > 0 ->
    a / b * b = a.

  Lemma mod_le_r : forall a b, a mod b <= b.

  Lemma lt_add_lt_sub : forall a b c,
    b <= a -> a < b + c -> a - b < c.

  Lemma lt_div_mul_add_le : forall a b c,
    b > 0 -> a < c / b -> b + a * b <= c.

  Lemma lt_div_mul_lt : forall a b c,
    b > 0 -> a < c / b -> a * b < c.

  Lemma div_lt_mul_lt : forall a b c,
    b > 0 -> a / b < c -> a < c * b.

  Lemma sub_round_eq_mod : forall a b, b <> 0 -> a - a / b * b = a mod b.

  Lemma mult_neq_0 : forall m n, m <> 0 -> n <> 0 -> m * n <> 0.

  Lemma mul_ge_l : forall m n,
    0 < m -> n <= n * m.

  Lemma mul_ge_r : forall m n,
    0 < m -> n <= m * n.

  Lemma div_mul_le : forall a b : addr, a / b * b <= a.

  Lemma sub_sub_assoc : forall a b,
    a >= b -> a - (a - b) = b.

  Lemma sub_mod_eq_round : forall a b, b <> 0 -> a - (a mod b) = a / b * b.

  Lemma roundup_ge: forall x sz,
      sz > 0 ->
      roundup x sz >= x.

  Lemma roundup_ge_divisor : forall x sz, 0 < x -> roundup x sz >= sz.

  Lemma divup_ok:
    forall x,
      divup x valubytes * valubytes >= x.

  Lemma divup_0:
    forall x,
    divup 0 x = 0.

  Lemma roundup_0:
    forall x,
    roundup 0 x = 0.

  Lemma divup_1: forall x,
    divup x 1 = x.

  Lemma divup_divup_eq:
    forall x,
      (divup ((divup x valubytes)*valubytes) valubytes) * valubytes =
      (divup x valubytes) * valubytes.

  Lemma divup_lt_arg: forall x sz,
    divup x sz <= x.
  
  Lemma divup_ge : forall a b c,
    b > 0 -> 
    c >= divup a b -> c * b >= a.

  Lemma divup_mono: forall m n sz,
    m <= n -> divup m sz <= divup n sz.

  Lemma roundup_mono : forall m n sz,
    m <= n -> roundup m sz <= roundup n sz.

  Definition divup' x m :=
  match (x mod m) with
  | O => x / m
  | S _ => x / m + 1
  end.

  Theorem divup_eq_divup'_m_nonzero : forall x m,
    m <> 0 ->
    divup x m = divup' x m.

  Theorem divup_eq_divup' : forall x m,
    divup x m = divup' x m.

  Ltac divup_cases :=
    rewrite divup_eq_divup';
    match goal with
    | [ |- context[divup' ?x ?m] ] =>
      unfold divup';
      case_eq (x mod m); intros
    end.

  Lemma divup_mul : forall x m,
    m <> 0 ->
    divup (x*m) m = x.

  Lemma divup_eq_div : forall a b, a mod b = 0 -> divup a b = a / b.

  Lemma div_le_divup : forall n sz,
    n / sz <= divup n sz.

  Lemma div_lt_divup : forall m n sz,
    sz <> 0 ->
    m < n ->
    m / sz < divup n sz.

  Lemma le_divup:
    forall m n,
      m <= n ->
      divup m valubytes <= divup n valubytes.

  Lemma le_roundup:
    forall m n,
      m <= n ->
      roundup m valubytes <= roundup n valubytes.

  (* slightly different from the one in Word.v *)
  Lemma lt_minus':
    forall a b c,
      a < c -> a - b < c.

  Lemma divup_goodSize:
    forall (a: waddr),
      goodSize addrlen (divup #a valubytes).

  Lemma divup_sub_1 : forall n sz,
    n >= sz -> sz <> 0 ->
    divup (n - sz) sz = divup n sz - 1.

  Lemma divup_sub : forall i n sz,
    n >= i * sz -> sz <> 0 ->
    divup (n - i * sz) sz = divup n sz - i.

  Lemma sub_mod_add_mod : forall a b,
    b <> 0 -> b - a mod b + a mod b = b.

  Lemma divup_mul_l : forall b c,
    divup (c * b) b <= c.

  Lemma divup_mul_r : forall b c,
    divup (b * c) b <= c.

  Lemma divup_le : forall a b c,
    a <= b * c -> divup a b <= c.

  Lemma divup_le_1 : forall a b,
    a <= b -> divup a b <= 1.

  Lemma divup_ge_1 : forall a b,
   b <> 0 -> a >= b -> divup a b >= 1.

  Lemma divup_small : forall c n, 0 < c <= n -> divup c n = 1.

  Lemma divup_mul_ge : forall a b c,
    b <> 0 -> a >= b * c -> divup a b >= c.

  Lemma divup_gt_0 : forall a b, 0 < a -> 0 < b -> divup a b > 0.

  Lemma mod_div_0 : forall a b,
    (a mod b) / b = 0.

  Lemma div_add_distr_le : forall a b c,
    a / c + b / c <= (a + b) / c.


  Lemma divup_add' : forall i n sz,
    sz <> 0 -> n <> 0 ->
    divup (n + sz * i) sz = divup n sz + i.
  
  Lemma divup_add : forall i n sz,
    sz <> 0 -> divup (n + sz * i) sz = divup n sz + i.

  Lemma divup_n_mul_n_le : forall a n, n <> 0 -> a <= (divup a n) * n.

  Lemma add_lt_upper_bound : forall a b c d,
    a <= b -> c + b < d -> c + a < d.

  Lemma helper_sub_add_cancel : forall a b c,
    a >= b -> b >= c ->
    a - b + (b - c) = a - c.

  Lemma helper_add_sub_lt : forall a b c,
    b > 0 -> a < c -> a + b - c < b.

  Lemma div_mul_lt : forall a b,
    b <> 0 -> a mod b <> 0 -> a / b * b < a.

  Theorem roundup_mult_mono : forall n a b, b <> 0 ->
    Nat.divide a b -> roundup n a <= roundup n b.

  Lemma min_roundup : forall a b z, roundup (min a b) z = min (roundup a z) (roundup b z).

  Lemma roundup_mult : forall a b, roundup (a * b) a = a * b.

  Lemma roundup_sub_lt : forall n sz,
    sz > 0 -> roundup n sz - n < sz.

  Lemma roundup_subt_divide : forall a b c, a < roundup b c -> Nat.divide c a ->
    roundup (b - a) c = roundup b c - a.

  Lemma divup_add_small : forall m n k,
    k > 0 -> n <= roundup m k - m ->
    divup (m + n) k = divup m k.

  Lemma divup_divup: forall x sz,
      sz > 0 ->
      divup ((divup x sz) * sz) sz = divup x sz.

  Lemma roundup_roundup : forall n sz,
    sz > 0 ->
    roundup (roundup n sz) sz = roundup n sz.

  Lemma roundup_roundup_add : forall x n sz,
    sz > 0 ->
    roundup (roundup n sz + x) sz = roundup n sz + roundup x sz.

  Lemma divup_same : forall x,
    x <> 0 -> divup x x = 1.

  Lemma divup_gt : forall a b sz,
    sz > 0 -> divup a sz > b -> a > b * sz.

  Definition divup_S x sz :=
    match (x mod sz) with
    | O => divup x sz + 1
    | S _ => divup x sz
    end.

  Theorem divup_eq_divup_S : forall x sz,
    sz <> 0 ->
    divup (S x) sz = divup_S x sz.


  Lemma divup_add_gt : forall a b n sz,
    sz > 0 -> a + divup b sz > n ->
    a * sz + b > n * sz.

  Lemma roundup_le' : forall a b sz,
    sz > 0 ->
    a <= b * sz -> roundup a sz <= b * sz.

  Lemma roundup_le : forall a b sz,
    a <= b * sz -> roundup a sz <= b * sz.

  Lemma roundup_min_r : forall a b,
    b > 0 -> Nat.min ((divup a b) * b ) a = a.

  Lemma divup_eq_div_plus_1 : forall a b, a mod b <> 0 -> divup a b = a / b + 1.

  Lemma roundup_gt : forall a b, b <> 0 -> a mod b <> 0 -> a < roundup a b.

  Lemma roundup_eq : forall a n, n <> 0 -> a mod n <> 0 -> roundup a n = a + (n - a mod n).