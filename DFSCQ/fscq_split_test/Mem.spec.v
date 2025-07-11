Require Import FunctionalExtensionality.

Set Implicit Arguments.

Definition EqDec (T : Type) := forall (a b : T), {a = b} + {a <> b}.

(* generalized memory of any address / value type *)

Definition mem {A : Type} {AEQ : EqDec A} {V : Type} := A -> option V.
Definition empty_mem {A : Type} {AEQ : EqDec A} {V : Type} : @mem A AEQ V := fun a => None.

Section GenMem.
  Variable A : Type.
  Variable V : Type.
  Variable AEQ : EqDec A.

  Definition upd (m : @mem A AEQ V) (a : A) (v : V) : @mem A AEQ V :=
    fun a' => if AEQ a' a then Some v else m a'.

  Definition updSome (m : @mem A AEQ V) (a : A) (v : V) : @mem A AEQ V :=
    fun a' => if AEQ a' a then
      match m a with
      | None => None
      | Some _ => Some v
      end else m a'.

  Definition delete (m : @mem A AEQ V) (a : A) : @mem A AEQ V :=
    fun a' => if AEQ a' a then None else m a'.

  Definition insert (m : @mem A AEQ V) (a : A) (v : V) : @mem A AEQ V :=
    fun a' => if AEQ a' a then
      match m a with
      | None => Some v
      | Some _ => m a'
      end else m a'.

  Theorem upd_eq : forall m (a : A) (v : V) a',
    a' = a -> upd m a v a' = Some v.

  Theorem updSome_eq : forall m (a : A) (v v' : V) a',
    m a = Some v' -> a' = a -> updSome m a v a' = Some v.

  Theorem insert_eq : forall m (a : A) (v v' : V) a',
    m a = None -> a' = a -> insert m a v a' = Some v.

  Theorem upd_ne : forall m (a : A) (v : V) a',
    a' <> a -> upd m a v a' = m a'.

  Theorem updSome_ne : forall m (a : A) (v : V) a',
    a' <> a -> updSome m a v a' = m a'.

  Theorem insert_ne : forall m (a : A) (v : V) a',
    a' <> a -> insert m a v a' = m a'.

  Theorem upd_repeat: forall m (a : A) (v v':V),
    upd (upd m a v') a v = upd m a v.

  Theorem updSome_repeat: forall m (a : A) (v v':V),
    updSome (updSome m a v') a v = updSome m a v.

  Theorem insert_repeat: forall m (a : A) (v v':V),
    insert (insert m a v) a v' = insert m a v.

  Theorem upd_nop: forall m (a : A) (v : V),
    m a = Some v ->
    upd m a v = m.

  Theorem updSome_nop: forall m (a : A) (v : V),
    m a = Some v ->
    updSome m a v = m.

  Theorem updSome_none : forall m (a : A) (v : V),
    m a = None ->
    updSome m a v = m.

  Theorem upd_comm: forall m (a0 : A) (v0 : V) a1 v1, a0 <> a1
    -> upd (upd m a0 v0) a1 v1 = upd (upd m a1 v1) a0 v0.

  Theorem updSome_comm: forall m (a0 : A) (v0 : V) a1 v1, a0 <> a1
    -> updSome (updSome m a0 v0) a1 v1 = updSome (updSome m a1 v1) a0 v0.

  Theorem updSome_insert_comm: forall m (a0 : A) (v0 : V) a1 v1, a0 <> a1
    -> updSome (insert m a0 v0) a1 v1 = insert (updSome m a1 v1) a0 v0.

  Theorem updSome_delete_comm: forall m (a0 : A) a1 (v1 : V), a0 <> a1
    -> updSome (delete m a0) a1 v1 = delete (updSome m a1 v1) a0.

  Theorem insert_comm: forall m (a0 : A) (v0 : V) a1 v1, a0 <> a1
    -> insert (insert m a0 v0) a1 v1 = insert (insert m a1 v1) a0 v0.

  Theorem insert_delete_comm: forall m (a0 : A) a1 (v1 : V), a0 <> a1
    -> insert (delete m a0) a1 v1 = delete (insert m a1 v1) a0.

  Theorem delete_comm: forall m (a0 : A) a1, a0 <> a1
    -> delete (delete m a0) a1 = delete (delete m a1) a0.

End GenMem.

Hint Rewrite upd_eq using (solve [ auto ]) : upd.
Hint Rewrite upd_ne using (solve [ auto ]) : upd.