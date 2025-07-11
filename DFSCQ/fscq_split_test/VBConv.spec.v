Require Import Arith.
Require Import Word.
Require Import Omega.
Require Import List ListUtils.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import AsyncDisk.
Require Import Bytes.
Require Import DiskSet.
Require Import Pred.
Import EqNotations.

Set Implicit Arguments.

Notation "'byteset'" := (byte * list byte)%type.


Definition list2byteset {A} def (l: list A) : (A * list A) :=
  match l with
  | nil => (def, nil)
  | h::t => (h,t)
  end.

Definition byteset2list {A} (nel: A * list A) : list A := (fst nel)::(snd nel).


Definition byteset0 := (byte0, nil: list byte).
Definition valu0 := bytes2valu  (natToWord (valubytes*8) 0).
Definition valuset0 := (valu0, nil: list valu).

Definition bytes_eq: forall sz, sz <= valubytes -> sz + (valubytes - sz) = valubytes.
Definition bytes2valubytes sz (b: bytes sz): bytes valubytes:=
    let c:= le_dec sz valubytes in
    match c with
    | left l => eq_rect (sz + (valubytes - sz)) bytes 
                  (bcombine b (word2bytes (valubytes-sz) eq_refl $0)) valubytes (bytes_eq l)
    | right _ => $0
    end.

Definition byte2valu b : valu :=  bytes2valu (bytes2valubytes (byte2bytes b)).

Definition list2valu l: valu :=  bytes2valu (bytes2valubytes (bcombine_list l)).

Definition valu2list v : list byte :=  bsplit_list (valu2bytes v).

Definition selN' {A: Type} i def (l: list A): A := selN l i def.
  
Definition cons' {A} (a: list A) b:= cons b a.

Definition get_sublist {A:Type}(l: list A) (off len: nat) : list A := firstn len (skipn off l).


Fixpoint valuset2bytesets_rec (vs: list (list byte)) i : list (list byte):=
match i with
| O => nil
| S i' => match vs with
    | nil => nil
    | _ =>  (map (selN' 0 byte0) vs)::(valuset2bytesets_rec (map (skipn 1) vs) i')
    end
end.

Definition valuset2bytesets (vs: valuset): list byteset:=
  map (list2byteset byte0) (valuset2bytesets_rec (map valu2list (byteset2list vs)) valubytes).

Fixpoint bytesets2valuset_rec (bs: list (list byte)) i : list (list  byte):=
match i with
| O => nil
| S i' => match bs with
          | nil => nil
          | _ =>  (map (selN' 0 byte0) bs)::(bytesets2valuset_rec (map (skipn 1) bs) i')
          end
end.

Definition bytesets2valuset (bs: list byteset) : valuset :=
	list2byteset valu0 (map (list2valu) (bytesets2valuset_rec (map (@byteset2list byte) bs)
                             (length(byteset2list(selN bs 0 byteset0))))).


Fixpoint merge_bs (lb: list byte) (lbs: list byteset): list byteset :=
match lb with
| nil => nil
| hb :: tb => match lbs with
              | nil => (hb, nil)::(merge_bs tb nil)
              | hbs::tbs => (hb, (fst hbs)::(snd hbs)):: (merge_bs tb tbs)
              end
end. 

Definition updN_list (l: list byteset) off (l1: list byte): list byteset :=
(firstn off l)++ (merge_bs l1 (get_sublist l off (length l1))) ++(skipn (off + length l1) l).

Definition ds2llb (ds: diskset) : nelist (list (list byteset)):= 
d_map (map valuset2bytesets) ds.

Definition llb2ds (llb : nelist (list (list byteset))) : diskset :=
d_map (map bytesets2valuset) llb.

Definition dsbupd (ds : diskset) (a : addr) (b : byteset): diskset :=
  llb2ds (d_map (map (fun x : list byteset => x ⟦ a := b ⟧)) (ds2llb ds)).

Fixpoint dsblistupd (ds : diskset) (a : addr) (lb : list byteset): diskset :=
  match lb with
  | nil => ds
  | h::t => dsblistupd (dsbupd ds a h) (a+1) t
  end. 
  
  
Definition mem_except_range AEQ V (m: @Mem.mem _ AEQ V) a n :=
(fun a' =>
    if (le_dec a a')
      then if (lt_dec a' (a + n))
            then None 
           else m a'
    else m a').
    
Fixpoint list_split_chunk A k cs (l: list A): list (list A) :=
match k with
  | O => nil
  | S k' => (firstn cs l)::(list_split_chunk k' cs (skipn cs l))
end.


Fixpoint list_zero_pad l a :=
match a with
| O => l
| S a' => list_zero_pad (l ++ (byte0 :: nil)) a'
end.

Definition mod_minus_curb a b: nat:=
match a mod b with
| O => 0
| _ => (b - a mod b)
end.
	
Fixpoint valu0_pad n: list valu :=
match n with
| O => nil
| S n' => valu0::(valu0_pad n')
end.

(* Lemmas *)

Lemma byteset2list2byteset: forall A (l: A * list A) def, 
  list2byteset def (byteset2list l) = l.

Lemma list2byteset2list: forall A (l: list A) def, 
  l<>nil -> byteset2list (list2byteset def l) = l.

Lemma valu2list_len : forall v,
 length(valu2list v) = valubytes.

Lemma valuset2bytesets_rec_expand: forall i a l,
   i > 0 ->
  valuset2bytesets_rec (a::l) i = 
	(map (selN' 0 byte0) (a::l)):: (valuset2bytesets_rec (map (skipn 1) (a::l)) (i-1)).

Lemma valuset2bytesets_rec_len: forall i l,  
  l <> nil -> length(valuset2bytesets_rec l i) = i.

Lemma valuset2bytesets_len: forall vs, 
  length(valuset2bytesets vs) = valubytes.

(* XXX: START Arithmetic Lemmas. *)
Lemma le_trans: forall n m k, n <= m -> m <= k -> n <= k.
Lemma le_weaken_l: forall n m k, n + m <= k -> n <= k.
Lemma le_weaken_r: forall n m k, n + m <= k -> m <= k.
Lemma lt_weaken_l: forall n m k, n + m < k -> n < k.
Lemma lt_weaken_r: forall n m k, n + m < k -> m < k.
Lemma le2lt_l: forall n m k, n + m <= k -> m > 0 -> n < k.
Lemma le2lt_r: forall n m k, n + m <= k -> n > 0 -> m < k.
Lemma mult_ne_O_l: forall n m p, p * n < p * m -> p > 0.

Lemma mult_ne_O_r: forall n m p, n * p < m * p -> p > 0.

Lemma plus_lt_compat_rev: forall n m p, p + n < p + m -> n < m.
Lemma lt_mult_weaken: forall p n m, n * p < m * p  -> n < m.

Lemma le_le_weaken: forall n m p k,
n + m <= p -> k <= m -> n + k <= p.

Lemma le_lt_weaken: forall n m p k,
n + m <= p -> k < m -> n + k < p.

Lemma div_eq: forall m n k, k < m -> (n * m + k)/m = n.

(* XXX: END Arithmetic Lemmas. *)

Lemma some_eq: forall A (x y: A), Some x = Some y <-> x = y.

 
Lemma concat_hom_selN: forall A (lists: list(list A)) i n k def, 
  Forall (fun sublist => length sublist = k) lists ->
  i < k ->
  selN (concat lists) (n * k + i) def = selN (selN lists n nil) i def.


 
Lemma fst_list2byteset: forall A (l:list A) def, fst(list2byteset def l) =  selN l 0 def.
Lemma flat_map_len: forall vs, length(flat_map valuset2bytesets vs) = length(vs) * valubytes.

Lemma valuset2bytesets_rec_nil: forall i, valuset2bytesets_rec nil i = nil.
Lemma firstn1 : forall A (l:list(list A)), concat(firstn 1 l) = selN l 0 nil.

  Lemma cons_eq_destruct: forall A (l1 l2: list A) b1 b2,
  b1 = b2 -> l1 = l2 -> b1::l1 = b2::l2.
Lemma concat_hom_O: forall A (l: list(list A)) i k,
  Forall (fun sublist : list A => length sublist = k) l ->
  i<= k -> 
  firstn i (concat l) = firstn i (selN l 0 nil).





Lemma mapfst_maplist2byteset: forall A (l: list (list A)) def,
  map fst (map (list2byteset def) l) = map (selN' 0 def) l.

Lemma bcombine_list_contr: forall a l, 
  bcombine (byte2bytes a) (bcombine_list l) = bcombine_list (a::l).
Lemma word2bytes_preserve: forall sz (b: bytes sz),
  word2bytes sz eq_refl $ (# b) = b.

Lemma bytes_eq_to_word_eq : forall n m,
    n = m ->
    n * 8 = m * 8.

Lemma eq_rect_bytes_to_word : forall sz sz' (H: sz = sz') b,
    rew [fun n => word (n * 8)] H in b = rew [fun n => word n] (bytes_eq_to_word_eq H) in b.

Theorem bcombine_0 : forall sz (b: bytes sz) (b': bytes 0) H,
    eq_rect _ bytes (bcombine b b') _ H = b.

Lemma list2valu2list: forall l, length l = valubytes -> valu2list (list2valu l) = l.

Lemma valu2list2valu: forall v, list2valu (valu2list v) = v.

Lemma cons_simpl: forall A a (l l': list A), l = l' -> (a::l) = (a::l').
Lemma v2b_rec_nil: forall l i,
  i = length l  ->
  valuset2bytesets_rec (l::nil) i = map (cons' nil) l.

Lemma length_skip1: forall l i, 
  length l = S i -> 
  length ((fun l : list byte => match l with
                               | nil => nil
                               | _ :: l0 => l0
                               end) l) = i.

Lemma mapfst_valuset2bytesets_single: forall w,
map fst (valuset2bytesets (w,nil)) = valu2list w.


Lemma mapfst_valuset2bytesets_rec: forall i a l,
length a = i ->
  Forall (fun sublist => length sublist = i) l ->
  map fst (map (list2byteset byte0)
     (valuset2bytesets_rec (a::l) i)) = a.

Lemma mapfst_valuset2bytesets: forall vs,
map fst (valuset2bytesets vs) = valu2list (fst vs).


Lemma bsplit1_bsplit_list: forall sz (b: bytes (1 + (sz - 1))),
  (bsplit1 1 (sz - 1) b :: bsplit_list (bsplit2 1 (sz - 1) b)) = bsplit_list b.

Lemma merge_bs_nil: forall l,
merge_bs l nil = map (fun x => (x, nil)) l.

Lemma l2b_cons_x_nil: forall l,
map (list2byteset byte0) (map (cons' nil) l)
		= map (fun x => (x, nil)) l.
	
Lemma valuset2bytesets_rec_cons_merge_bs: forall k a l,
  Forall (fun sublist => length sublist = k) (a::l) ->
 map (list2byteset byte0) (valuset2bytesets_rec (a::l) k) 
 		= merge_bs a (map (list2byteset byte0) (valuset2bytesets_rec l k)).


(* alterantive definitions that are easier to induct over *)
Definition valuset2byteset (vs : list (list byte)) :=
  map (fun i => selN_each vs i byte0) (seq 0 valubytes).

Definition valuset2bytesets' (vs: valuset): list byteset :=
  combine (valu2list (fst vs)) (valuset2byteset (map valu2list (snd vs))).

Definition bytesets2valuset' (l : list byteset) i :=
  let sets := split l in
  (list2valu (fst sets), map (fun i => list2valu (selN_each (snd sets) i byte0)) (seq 0 i)).

Lemma valuset2bytesets_rec_eq_valuset2bytesets: forall vs,
  length vs > 0 ->
  valuset2bytesets_rec vs valubytes = valuset2byteset vs.

Lemma valuset2bytesets_eq_valuset2bytesets': forall vs,
  valuset2bytesets vs = valuset2bytesets' vs.

Lemma bytesets2valuset_rec_eq_map: forall n bs,
  length bs > 0 ->
  bytesets2valuset_rec bs n = map (fun i => selN_each bs i byte0) (seq 0 n).

Lemma selN_each_fst_list2byteset: forall T (l : list (T * _)) def,
  selN_each (map byteset2list l) 0 def = fst (split l).

Lemma selN_each_snd_list2byteset: forall T (l : list (T * _)) a def,
  selN_each (map byteset2list l) (S a) def = selN_each (snd (split l)) a def.


Lemma bytesets2valuset_eq_bytesets2valuset': forall bs n,
  Forall (fun b => length (snd b) = n) bs ->
  length bs = valubytes ->
  bytesets2valuset bs = bytesets2valuset' bs n.

Lemma valuset2bytesets2valuset: forall vs,
  bytesets2valuset (valuset2bytesets vs) = vs.

Fact updN_list_nil: forall l2 l1 a,
  l1 <> nil -> updN_list l1 a l2 = nil -> l2 = nil.

Fact skipn_not_nil: forall A (l: list A) n,
  n < length l -> skipn n l <> nil.

Fact b2v_rec_nil: forall i bn,
  bytesets2valuset_rec bn i = nil -> i = 0 \/ bn = nil.

Fact d_map_d_map: forall A B C (a: A) (l: list A) (f: A -> B) (g: B -> C),
d_map g (d_map f (a,l)) = d_map (fun x => g(f x)) (a, l).

Lemma mod_Sn_n_1: forall a, a >1 -> (a + 1) mod a = 1.


Lemma le_mult_weaken: forall p n m, p > 0 -> n * p <= m * p  -> n <= m.



Fact vs2bs_selN_O: forall l,
selN (valuset2bytesets l) 0 byteset0 = (list2byteset byte0 (map (selN' 0 byte0) (map valu2list (byteset2list l)))).

Lemma updN_eq: forall A v v' a (l: list A), v = v' -> updN l a v  = updN l a v'.
Lemma skipn_concat_skipn: forall A j i k (l: list (list A)) def,
i <= k -> j < length l -> Forall (fun sublist : list A => length sublist = k) l ->
skipn i (concat (skipn j l)) = skipn i (selN l j def) ++ concat (skipn (S j) l).

Fact map_1to1_eq: forall A B (f: A -> B) (l l': list A), 
  (forall x y, f x = f y -> x = y) -> 
  map f l = map f l' ->
  l = l'.
  

Fact map_eq: forall A B (f: A -> B) (l l': list A), 
  l = l' ->
  map f l = map f l'.

Fact valubytes_ne_O: valubytes <> 0.

Fact le_minus_divmult: forall n m k, m <> 0 ->
    n - (m - k mod m) - (n - (m - k mod m)) / m * m <= m.

Fact grouping_minus: forall n m k a, n - (m - k + a) = n - (m - k) - a.
Lemma mod_dem_neq_dem: forall a b, a <> 0 -> b <> 0 -> b <> a mod b.


Lemma get_sublist_length: forall A (l: list A) a b,
a + b <= length l ->
length (get_sublist l a b) = b.

Lemma bsplit_list_b2vb: forall b,
  exists l, (bsplit_list (bytes2valubytes (byte2bytes b))) = b::l.


Lemma app_length_eq: forall A (l l': list A) len a,
length l = len -> a + length l' <= len ->
length (firstn a l ++ l' ++ skipn (a + length l') l) = len.
	
Lemma off_mod_v_l_data_le_v: forall length_data off,
	length_data <= valubytes - off mod valubytes ->
	off mod valubytes + length_data <= valubytes.
	
	
Lemma v_off_mod_v_le_length_data: forall length_data off,
~ length_data <= valubytes - off mod valubytes ->
valubytes - off mod valubytes <= length_data.
Lemma three_reorder: forall a b c,
a + b + c = c + b + a.
Lemma last_two_reorder: forall a b c,
a + b + c = a + c + b.
Lemma pm_1_3_cancel: forall a b,
a + b - a = b.
Lemma n_le_n_p_1: forall n,
n <= n + 1.
Lemma ppmp_2_4_cancel: forall a b c d,
a + b + c - b + d = a + c + d.
Lemma mm_dist: forall a b c,
b <= a ->
c <= b ->
a - (b - c) = a - b + c.
Lemma le_2: forall a b c,
b <= a + b + c.
Lemma app_assoc_middle_2: forall A (l1 l2 l3 l4 l5: list A),
l1++l2++l3++l4++l5 = l1++l2++(l3++l4)++l5.
Lemma ppmp_3_4_cancel: forall a b c d,
a + b + c - c + d = a + b + d.
Lemma mm_1_3_cancel: forall a b,
a - b - a = 0.
Lemma list_split_chunk_length: forall A n m (l: list A),
m > 0 ->
length l = n * m -> 
length (list_split_chunk n m l) = min n (length l / m).

Lemma firstn_valuset2bytesets_byte2valu: forall b,
firstn 1 (valuset2bytesets (byte2valu b, nil)) = (b, nil)::nil.

Lemma list_split_chunk_app_1: forall A a b (l l': list A) ,
length l = a * b ->
length l' = b ->
list_split_chunk (a+1) b (l ++ l') =  list_split_chunk a b l ++ l'::nil.

Lemma list_split_chunk_map_comm: forall A B a b (l: list A) (f:A -> B),
map (fun x => map f x) (list_split_chunk a b l) = list_split_chunk a b (map f l).

Lemma get_sublist_map_comm: forall A B a b (f: A -> B) (l: list A),
map f (get_sublist l a b) = get_sublist (map f l) a b.

Lemma firstn_1_selN: forall A (l: list A) def,
l <> nil -> firstn 1 l = (selN l 0 def)::nil.

Lemma concat_list_split_chunk_id: forall A a b (l: list A),
a * b = length l -> concat (list_split_chunk a b l) = l.

Lemma list_split_chunk_cons: forall A m1 (l: list A),
length l = m1 * valubytes + valubytes -> 
list_split_chunk (m1 + 1) valubytes l  = firstn valubytes l :: list_split_chunk m1 valubytes (skipn valubytes l).

Lemma list_split_chunk_nonnil: forall A a b (l: list A),
b > 0 ->
length l = a * b ->
forall x, In x (list_split_chunk a b l) -> x <> nil.


Lemma le_minus_weaken: forall a b c,
a <= b -> a-c <= b - c.
Lemma le_minus_dist: forall a b c,
a >= b ->
b >= c ->
a - (b - c) = a - b + c.
Lemma plus_minus_arrange: forall a b c d,
a >= b ->
a - b + c >= d ->
a - b + c - d + b = a + c - d + b - b.
Lemma le_minus_weaken_r: forall a b c,
a <= b - c -> a <= b.

Fact updN_list_length: forall l a ln,
a + length ln <= length l ->
length (updN_list l a ln) = length l.

Fact updN_list2firstn_skipn: forall ln a l,
a + length ln <= length l ->
updN_list l a ln = firstn a l ++ (updN_list (get_sublist l a (length ln)) 0 ln) 
                      ++ skipn (a + (length ln)) l.

Lemma app_tail_eq: forall A (l l' l'':list A),
  l = l' -> l ++ l'' = l' ++ l''.
Lemma app_head_eq: forall A (l l' l'':list A),
  l = l' -> l'' ++ l = l'' ++ l'.
Lemma valubytes_ge_O: valubytes > 0.
Lemma old_data_m1_ge_0: forall l_old_data m1 l_old_blocks,
m1 < l_old_blocks ->
l_old_data = l_old_blocks * valubytes ->
l_old_data - m1 * valubytes > 0.
Lemma length_data_ge_m1: forall l_data l_old_data m1 l_old_blocks,
l_data = l_old_data ->
m1 < l_old_blocks ->
l_old_data = l_old_blocks * valubytes ->
m1 * valubytes <= l_data.
Lemma get_sublist_div_length: forall A (data: list A) l_old_data m1 l_old_blocks,
length data = l_old_data ->
m1 < l_old_blocks ->
l_old_data = l_old_blocks * valubytes ->
m1 <= length (get_sublist data 0 (m1 * valubytes)) / valubytes.

Lemma length_old_data_ge_O: forall l_data l_old_data m1 l_old_blocks,
l_data = l_old_data ->
m1 < l_old_blocks ->
l_old_data = l_old_blocks * valubytes ->
l_old_data > 0.
Lemma old_data_ne_nil: forall A (old_data: list A) m1 l_old_blocks,
old_data = nil ->
m1 < l_old_blocks ->
length old_data = l_old_blocks * valubytes ->
False.
Lemma length_bytefile_ge_minus: forall l_fy block_off l_old_data m1 l_old_blocks,
block_off * valubytes + l_old_data <= l_fy ->
m1 < l_old_blocks ->
l_old_data = l_old_blocks * valubytes ->
valubytes <= l_fy - (block_off + m1) * valubytes.
Lemma length_data_ge_m1_v: forall l_data l_old_data m1 l_old_blocks,
l_data = l_old_data ->
m1 < l_old_blocks ->
l_old_data = l_old_blocks * valubytes ->
m1 * valubytes + valubytes <= l_data.
Lemma nonnil_exists: forall A (l: list A),
l <> nil -> exists a l', l = a::l'.

Lemma map_same: forall A B (l1 l2: list A) (f: A -> B),
l1 = l2 -> map f l1 = map f l2.
Lemma pmm_1_3_cancel: forall a b c,
a + b - a -c = b - c.
Lemma le_div_mult_add: forall a b,
b <> 0 -> a <= a/b * b + b.

Lemma le_minus_middle_cancel: forall a b c d e,
a - c <= d - e -> a - b - c <= d - b - e.
Lemma mppp_two_five_cancel: forall a b c d,
a >= b ->
a - b + c + d + b = a + c + d.
Lemma le_minus_lt: forall a b c,
b > 0 -> c > 0 -> a <= b - c -> a < b.
Lemma modulo_eq: forall b a,
  b <> 0 -> a >= b -> (a - b) mod b = a mod b.

Lemma minus_middle: forall a b c,
b <> 0 -> a>= b -> b >= c -> (a - (b - c))/ b = (a + c) / b - 1.
  
	Lemma mod_minus_eq: forall c a b,
	b <> 0 ->
	a >= c * b ->
	(a - c * b) mod b = a mod b.
	
		Lemma lt_minus_r: forall a b c,
	b > c -> a > c -> a - c > a -b.

Lemma n2w_id: forall a b sz,
a = b -> natToWord sz a = natToWord sz b.
Lemma mod_minus: forall a b,
b <> 0 ->
a - a mod b = (a / b) * b.
 
Lemma mod_minus_mod: forall a b,
b <> 0 ->
(a - a mod b) mod b = 0.
 
 	
Lemma lt_mp: forall a b c,
a > b -> 
c < b ->
a - b + c < a.
Lemma between_lt_upper: forall a b c,
b <> 0 ->
a > (c - 1) * b ->
a <= c * b ->
a mod b > 0 ->
a < c * b.

Lemma list_zero_pad_length: forall a l,
length (list_zero_pad l a) = length l + a.

Lemma list_zero_pad_selN_l: forall a l i def,
i < length l ->
selN (list_zero_pad l a) i def = selN l i def.

Lemma list_zero_pad_selN_pad: forall a l i,
i >= length l ->
selN (list_zero_pad l a) i byte0 = byte0.

Lemma between_mod_ne_0: forall c a b,
b <> 0 ->
a > (c - 1) * b ->
a < c * b ->
a mod b <> 0.

Lemma merge_bs_firstn_comm: forall l l' a,
firstn a (merge_bs l l') = merge_bs (firstn a l) (firstn a l').

Lemma list_zero_pad_expand: forall a l,
list_zero_pad l a = l ++ list_zero_pad nil a.
  
Lemma list_zero_pad_nil_iff: forall a l,
list_zero_pad l a = nil <-> l = nil /\ a = 0.

Lemma pmp_1_4_cancel: forall a b c,
a + b - a + c = b + c.
Lemma lt_minus_S: forall a b,
a > b ->
exists n, a - b = S n.

Lemma mod_upper_bound_le: forall a b,
a mod b < b ->
a mod b + 1 <= b.
Lemma list_zero_pad_nil_firstn: forall a b,
firstn a (list_zero_pad nil b) = list_zero_pad nil (min a b).

		
		Lemma lt_0_S: forall a,
	a > 0 -> exists n, a = S n.
	
	Lemma mod_minus_lt_0: forall a b,
	b <> 0 ->
	b - a mod b > 0.
	
	Lemma mp_2_3_cancel: forall a b,
	a >= b -> a - b + b = a.
	
	Lemma mod_ne_0: forall a b,
b <> 0 -> a mod b > 0 ->
a > 0.

Lemma minus_le_0_eq: forall a b,
a >= b -> a - b = 0 -> a = b.
Lemma plus_minus_eq_le: forall a b c,
  a >=  b -> a - b = c -> a = b + c.
Lemma between_exists: forall b a c,
    a >= (b-1) * c -> a < b*c -> c<>0 -> a = (b-1) * c + a mod c.

Lemma mod_between_upper: forall a b c,
	b <> 0 ->
	a > (c - 1) * b ->
	c * b >= a ->
	a mod b = 0 ->
	a = c * b.