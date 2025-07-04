Require Import Mem.
Require Import Prog.
Require Import List.
Require Import Array.
Require Import Pred.
Require Import FunctionalExtensionality.
Require Import Word.
Require Import WordAuto.
Require Import Omega.
Require Import Ring.
Require Import SepAuto.
Require Import ListUtils.
Require Import ListPred.

Set Implicit Arguments.

(**
 * This module is meant to generalize separation logic to arbitrary functions
 * from some address-like thing to some value-like thing.  The motivating use
 * case is in files: we want to think of the disk as a mapping from inode numbers
 * to file objects, where each file object includes metadata and the entire file
 * contents.  Current separation logic is not quite good enough, because we want
 * to have values that are bigger than a 512-byte block.
 *)

(**
 * list2nmem is meant to convert a list representation of files into a memory-like
 * object that maps inode numbers (list positions) into files (or None, if the
 * inode number is too big).  [list2nmem] always uses [nat] as the index.
 *)
Definition list2nmem (A: Type) (l: list A) : (@mem nat eq_nat_dec A) :=
  fun a => selN (map (@Some A) l) a None.

Notation "[[[ NS ':::' P ]]]" := [[ (P)%pred (list2nmem NS) ]]%pred : pred_scope.
Notation "【 NS '‣‣' P 】" := [[ (P)%pred (list2nmem NS) ]]%pred : pred_scope.

Theorem list2nmem_oob : forall A (l : list A) i,
  i >= length l
  -> (list2nmem l) i = None.


Theorem list2nmem_inbound: forall A F (l : list A) i x,
  (F * i |-> x)%pred (list2nmem l)
  -> i < length l.


Theorem list2nmem_sel: forall A F (l: list A) i x def,
  (F * i |-> x)%pred (list2nmem l)
  -> x = selN l i def.


Lemma listupd_memupd: forall A l i (v : A),
  i < length l
  -> list2nmem (updN l i v) = Mem.upd (list2nmem l) i v.

Theorem list2nmem_updN: forall A F (l: list A) i x y,
  (F * i |-> x)%pred (list2nmem l)
  -> (F * i |-> y)%pred (list2nmem (updN l i y)).

Lemma list2nmem_updN_selN : forall A F (l : list A) a v1 def,
  (F * a |-> v1)%pred (list2nmem (updN l a v1)) ->
  (F * a |-> selN l a def)%pred (list2nmem l).


Theorem listapp_memupd: forall A l (a : A),
  list2nmem (l ++ a :: nil) = Mem.upd (list2nmem l) (length l) a.

Theorem listapp_meminsert: forall A l (a : A),
  list2nmem (l ++ a :: nil) = Mem.insert (list2nmem l) (length l) a.


Theorem list2nmem_app: forall A (F : @pred _ _ A) l a,
  F (list2nmem l)
  -> (F * (length l) |-> a)%pred (list2nmem (l ++ a :: nil)).

Theorem list2nmem_arrayN_app: forall A (F : @pred _ _ A) l l',
  F (list2nmem l) ->
  (F * arrayN (@ptsto _ eq_nat_dec A) (length l) l') %pred (list2nmem (l ++ l')).

Theorem list2nmem_removelast_is : forall A l (def : A),
  l <> nil
  -> list2nmem (removelast l) =
     fun i => if (lt_dec i (length l - 1)) then Some (selN l i def) else None.


Theorem list2nmem_removelast_list2nmem : forall A (l : list A) (def : A),
  l <> nil
  -> list2nmem (removelast l) =
     fun i => if (eq_nat_dec i (length l - 1)) then None else (list2nmem l) i.


Lemma mem_disjoint_either: forall AT AEQ V (m1 m2 : @mem AT AEQ V) a v,
  mem_disjoint m1 m2
  -> m1 a = Some v -> m2 a = None.


Theorem list2nmem_removelast: forall A F (l : list A) v,
  l <> nil
  -> (F * (length l - 1) |-> v)%pred (list2nmem l)
  -> F (list2nmem (removelast l)).

Lemma list2nmem_except_last : forall T (l : list T) x,
  mem_except (list2nmem (l ++ x::nil)) (length l) = list2nmem l.

Theorem list2nmem_array: forall  A (l : list A),
  arrayN (@ptsto _ eq_nat_dec A) 0 l (list2nmem l).

Theorem list2nmem_array': forall  A (l l' : list A),
  l = l' ->
  arrayN (@ptsto _ eq_nat_dec A) 0 l' (list2nmem l).

Theorem list2nmem_arrayN_firstn_skipn: forall A (l:list A) n,
  (arrayN (@ptsto _ eq_nat_dec A) 0 (firstn n l) *
   arrayN (@ptsto _ eq_nat_dec A) n (skipn n l))%pred (list2nmem l).

Lemma listpred_ptsto_list2nmem: forall T t (l : list T),
  listpred (fun a => a |->?)%pred t (list2nmem l) ->
  Permutation.Permutation t (seq 0 (length l)).


Lemma arrayN_ptsto_linked: forall S V t l,
  arrayN (ptsto (V:=S)) 0 l =p=> listpred (fun a => exists v, a |-> v) t ->
  @listpred _ _ Nat.eq_dec V (fun a => a |->?) (seq 0 (length l)) =p=> listpred (fun a => a |->?) t.

(* Alternative variants of [list2nmem] that are more induction-friendly *)
Definition list2nmem_off (A: Type) (start : nat) (l: list A) : (nat -> option A) :=
  fun a => if lt_dec a start then None
                             else selN (map (@Some A) l) (a - start) None.

Theorem list2nmem_off_eq : forall A (l : list A), list2nmem l = list2nmem_off 0 l.

Fixpoint list2nmem_fix (A : Type) (start : nat) (l : list A) : (nat -> option A) :=
  match l with
  | nil => fun a => None
  | h :: l' => fun a => if eq_nat_dec a start then Some h else list2nmem_fix (S start) l' a
  end.

Lemma list2nmem_fix_below : forall (A : Type) (l : list A) start a,
  a < start -> list2nmem_fix start l a = None.

Theorem list2nmem_fix_off_eq : forall A (l : list A) n,
  list2nmem_off n l = list2nmem_fix n l.

Theorem list2nmem_fix_eq : forall A (l : list A),
  list2nmem l = list2nmem_fix 0 l.

Theorem list2nmem_off_app_union : forall A (a b : list A) start,
  list2nmem_off start (a ++ b) = @mem_union _ eq_nat_dec A (list2nmem_off start a)
                                                           (list2nmem_off (start + length a) b).

Theorem list2nmem_off_disjoint : forall A (a b : list A) sa sb,
  (sb >= sa + length a \/ sa >= sb + length b) ->
  @mem_disjoint _ eq_nat_dec A (list2nmem_off sa a) (list2nmem_off sb b).

Lemma list2nmem_nil_array : forall A (l : list A) start,
  arrayN (@ptsto _ eq_nat_dec A) start l (list2nmem nil) -> l = nil.

Lemma list2nmem_array_nil : forall A (l : list A) start,
  arrayN (@ptsto _ eq_nat_dec A) start nil (list2nmem_fix start l) -> l = nil.

Theorem list2nmem_array_eq': forall A (l' l : list A) start,
  arrayN (@ptsto _ eq_nat_dec A) start l (list2nmem_fix start l')
  -> l' = l.

Theorem list2nmem_array_eq: forall A (l' l : list A),
  arrayN (@ptsto _ eq_nat_dec A) 0 l (list2nmem l')
  -> l' = l.

Theorem list2nmem_array_mem_eq : forall V (l : list V) m,
  arrayN (@ptsto _ eq_nat_dec V) 0 l m ->
  m = list2nmem l.

Theorem list2nmem_array_app_eq: forall A (l l' : list A) a,
  (arrayN (@ptsto _ eq_nat_dec A) 0 l * (length l) |-> a)%pred (list2nmem l')
  -> l' = (l ++ a :: nil).


Lemma list2nmem_some_bound' : forall A (m : list A) start off a,
  list2nmem_fix start m off = Some a
  -> off + 1 <= start + length m.

Lemma list2nmem_some_bound : forall A (m : list A) off a,
  list2nmem m off = Some a
  -> off + 1 <= length m.

Theorem list2nmem_arrayN_bound : forall A (l m : list A) off F,
  (F * arrayN (@ptsto _ eq_nat_dec A) off l)%pred (list2nmem m)
  -> l = nil \/ off + length l <= length m.

Theorem list2nmem_arrayN_length : forall A (l m : list A) F,
  (F * arrayN (@ptsto _ eq_nat_dec A) 0 l)%pred (list2nmem m)
  -> length l <= length m.

Theorem list2nmem_ptsto_bound : forall A (l : list A) off v F,
  (F * off |-> v)%pred (list2nmem l)
  -> off < length l.


Definition arrayN_ex A VP pts (vs : list A) i : @pred _ _ VP :=
  (arrayN pts 0 (firstn i vs) *
   arrayN pts (i + 1) (skipn (S i) vs))%pred.

Lemma arrayN_ex_one: forall V VP (pts : _ -> _ -> @pred _ _ VP) (l : list V),
    List.length l = 1 ->
    arrayN_ex pts l 0 <=p=> emp.

Theorem arrayN_except : forall T V (vs : list T) (def : T) i (pts: _ -> _ -> @pred _ _ V),
  i < length vs
  -> arrayN pts 0 vs <=p=>
    (arrayN_ex pts vs i) * (pts i (selN vs i def)).

Theorem arrayN_except_upd : forall V T vs (v : T) i (pts : nat -> T -> @pred _ _ V),
  i < length vs
  -> arrayN pts 0 (updN vs i v) <=p=>
    (arrayN_ex pts vs i) * (pts i v).

Theorem arrayN_ex_updN_eq : forall T A l i (v : A) (pts : _ -> _ -> @pred _ _ T),
  arrayN_ex pts (updN l i v) i <=p=>
  arrayN_ex pts l i.

Theorem arrayN_mem_upd_none : forall V vs i m (v d : V) (p : nat -> V -> pred),
  m i = None ->
  i < length vs ->
  arrayN_ex p vs i m ->
  p i (selN vs i d) (fun a => if eq_nat_dec a i then Some v else None) ->
  arrayN p 0 vs (Mem.upd m i v).


Theorem list2nmem_array_pick : forall V l (def : V) i,
  i < length l
  -> (arrayN_ex (@ptsto _ eq_nat_dec V) l i * i |-> selN l i def)%pred (list2nmem l).

Theorem list2nmem_array_updN : forall V ol nl (v : V) i,
  (arrayN_ex (@ptsto _ eq_nat_dec V) ol i * i |-> v)%pred (list2nmem nl)
  -> i < length ol
  -> nl = updN ol i v.

Theorem list2nmem_array_removelast_eq : forall V (nl ol : list V),
  (arrayN_ex (@ptsto _ eq_nat_dec V) ol (length ol - 1))%pred (list2nmem nl)
  -> length ol > 0
  -> nl = removelast ol.


Theorem list2nmem_array_exis : forall V l (def : V) i,
  (arrayN_ex (@ptsto _ eq_nat_dec V) l i * i |-> selN l i def)%pred (list2nmem l)
  -> (arrayN_ex (@ptsto _ eq_nat_dec V) l i * i |->?)%pred (list2nmem l).


Lemma list2nmem_ptsto_cancel : forall V i (def : V) l, i < length l ->
  (arrayN_ex (@ptsto _ eq_nat_dec V) l i * i |-> selN l i def)%pred (list2nmem l).

Lemma list2nmem_ptsto_cancel_pair : forall A B i (def : A * B) l,
  i < length l ->
  (arrayN_ex (@ptsto _ eq_nat_dec (A * B)) l i * 
    i |-> (fst (selN l i def), snd (selN l i def)))%pred (list2nmem l).

Lemma list2nmem_sel_for_eauto : forall V A i (v v' : V) l def,
  (A * i |-> v)%pred (list2nmem l)
  -> v' = selN l i def
  -> v' = v.

Lemma arrayN_combine' : forall A VP (pts : _ -> _ -> @pred _ _ VP) (a b : list A) start,
  arrayN pts start a * arrayN pts (start + length a) b <=p=> arrayN pts start (a ++ b).

Lemma arrayN_combine : forall A VP (pts : _ -> _ -> @pred _ _ VP) (a b : list A) start off,
  off = start + length a ->
  arrayN pts start a * arrayN pts off b <=p=> arrayN pts start (a ++ b).


Lemma arrayN_list2nmem : forall A (def : A) (a b : list A) F off,
  (F * arrayN (@ptsto _ eq_nat_dec A) off a)%pred (list2nmem b) ->
  a = firstn (length a) (skipn off b).

Theorem list2nmem_ptsto_end_eq : forall A (F : @pred _ _ A) l a a',
  (F * (length l) |-> a)%pred (list2nmem (l ++ a' :: nil)) ->
  a = a'.

Theorem list2nmem_arrayN_end_eq : forall A (F : @pred _ _ A) l l' l'' (def:A),
  length l' = length l'' ->
  (F * arrayN (@ptsto _ eq_nat_dec A) (length l) l')%pred (list2nmem (l ++ l'')) ->
  l' = l''.

Theorem list2nmem_off_arrayN: forall A (l : list A) off,
  arrayN (@ptsto _ eq_nat_dec A) off l (list2nmem_off off l).

Theorem list2nmem_arrayN_app_iff : forall A (F : @pred _ _ A) l l',
  (F * arrayN (@ptsto _ eq_nat_dec A) (length l) l')%pred (list2nmem (l ++ l')) ->
  F (list2nmem l).


Lemma mem_except_list2nmem_oob : forall A (l : list A) a,
  a >= length l ->
  mem_except (list2nmem l) a = list2nmem l.

Lemma list2nmem_sel_inb : forall A (l : list A) a def,
  a < length l ->
  list2nmem l a = Some (selN l a def).


Lemma sep_star_reorder_helper1 : forall AT AEQ V (a b c d : @pred AT AEQ V),
  (a * ((b * c) * d)) <=p=> (a * b * d) * c.

Lemma list2nmem_arrayN_updN : forall V F a vl l i (v : V),
  (F * arrayN (@ptsto _ eq_nat_dec V) a vl)%pred (list2nmem l) ->
  i < length vl ->
  (F * arrayN (@ptsto _ eq_nat_dec V) a (updN vl i v))%pred (list2nmem (updN l (a + i) v)).


Lemma listmatch_ptsto_list2nmem_inbound : forall VT al vl (F : @pred _ _ VT) m ,
  (F * listmatch (fun a v => a |-> v) al vl)%pred (list2nmem m) ->
  Forall (fun a => a < length m) al.


Lemma list2nmem_inj' : forall A (a b : list A) n,
  list2nmem_off n a = list2nmem_off n b ->
  a = b.


Lemma list2nmem_inj : forall A (a b : list A),
  list2nmem a = list2nmem b ->  a = b.


(* crashes *)

Require Import PredCrash AsyncDisk.
Import ListNotations.

Lemma list2nmem_crash_xform : forall vl vsl (F : rawpred),
  possible_crash_list vsl vl ->
  F (list2nmem vsl) ->
  crash_xform F (list2nmem (synced_list vl)).


Lemma crash_xform_list2nmem_possible_crash_list : forall vl (F : rawpred),
  crash_xform F (list2nmem vl) ->
  exists vsl, F (list2nmem vsl) /\ possible_crash_list vsl (map fst vl).


Lemma crash_xform_list2nmem_synced : forall vl (F : rawpred),
  crash_xform F (list2nmem vl) ->
  map snd vl = repeat (@nil valu) (length vl).


Lemma crash_xform_list2nmem_list_eq : forall F vsl vl,
  crash_xform F (list2nmem vsl) ->
  possible_crash_list vsl vl ->
  vsl = synced_list vl.

Lemma possible_crash_list2nmem_cons : forall l l' x y,
  possible_crash (list2nmem (x :: l)) (list2nmem (y :: l'))
  -> possible_crash (list2nmem l) (list2nmem l').

Lemma possible_crash_list2nmem_length : forall l l',
  possible_crash (list2nmem l) (list2nmem l')
  -> length l = length l'.


Lemma possible_crash_list2nmem_vssync : forall a d m,
  possible_crash (list2nmem (vssync d a)) m ->
  possible_crash (list2nmem d) m.

Lemma possible_crash_list2nmem_vssync_vecs : forall al d m,
  possible_crash (list2nmem (vssync_vecs d al)) m ->
  possible_crash (list2nmem d) m.

Lemma crash_xform_diskIs_vssync_vecs : forall al d,
  crash_xform (diskIs (list2nmem (vssync_vecs d al))) =p=>
  crash_xform (diskIs (list2nmem d)).

Lemma setlen_singleton : forall T l (v : T),
  setlen l 1 v = [ selN (setlen l 1 v) 0 v ].

Lemma setlen_singleton_ptsto : forall (l : list valuset),
  let l' := setlen l 1 ($0, nil) in
  (0 |-> selN l' 0 ($0, nil))%pred (list2nmem l').

Lemma ptsto_0_list2nmem_mem_eq : forall V v (d : list V),
  (0 |-> v)%pred (list2nmem d) -> d = [v].

Lemma ptsto_a_list2nmem_a0 : forall V v (d : list V) a,
  (a |-> v)%pred (list2nmem d) -> a = 0.

Lemma ptsto_a_list2nmem_mem_eq : forall V v (d : list V) a,
  (a |-> v)%pred (list2nmem d) -> d = [v].

Theorem arrayN_pimpl : forall V m (F : @pred addr addr_eq_dec V) l,
  F m ->
  arrayN (@ptsto _ _ _) 0 l m ->
  arrayN (@ptsto _ _ _) 0 l =p=> F.

Lemma pred_except_ptsto_pimpl : forall V (l : list V) off v F,
  (F * off |-> v)%pred (list2nmem l) ->
  pred_except (arrayN (@ptsto _ _ _) 0 l) off v =p=> F.

Lemma arrayN_notindomain_before : forall V (l : list V) start off,
  off < start ->
  arrayN (@ptsto _ _ V) start l =p=> notindomain off.

Lemma arrayN_notindomain_after : forall V (l : list V) start off,
  start + length l <= off ->
  arrayN (@ptsto _ _ V) start l =p=> notindomain off.

Lemma arrayN_ex_notindomain : forall V (l : list V) off,
  arrayN_ex (@ptsto _ _ V) l off ⇨⇨ notindomain off.

Theorem arrayN_ex_pred_except : forall V (l : list V) off def,
  off < length l ->
  arrayN_ex (@ptsto _ _ _) l off =p=>
  pred_except (arrayN (@ptsto _ _ _) 0 l) off (selN l off def).

Lemma arrayN_ex_frame_pimpl : forall V (l : list V) off v F,
  (F * off |-> v)%pred (list2nmem l) ->
  arrayN_ex (@ptsto _ _ _) l off =p=> F.