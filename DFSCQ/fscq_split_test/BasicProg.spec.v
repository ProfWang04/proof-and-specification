Require Import Prog ProgMonad.
Require Import Pred.
Require Import PredCrash.
Require Import Hoare.
Require Import Omega.
Require Import SepAuto.
Require Import Word.
Require Import Nomega.
Require Import NArith.
Require Import FunctionalExtensionality.
Require Import List.
Require Import AsyncDisk.
Require Import Hashmap.
Require Import ListUtils.
Require Import ProofIrrelevance.

Set Implicit Arguments.

(** * Some helpful [prog] combinators and proofs *)

Lemma sync_invariant_possible_sync : forall (F: rawpred) (m: rawdisk),
    F m ->
    sync_invariant F ->
    possible_sync m =p=> F.

Hint Resolve sync_invariant_possible_sync.

Theorem read_ok:
  forall (a:addr),
  {< v,
  PRE:hm         a |+> v
  POST:hm' RET:r a |+> v * [[ r = (fst v) ]]
  CRASH:hm'      a |+> v
  >} Read a.

Hint Extern 1 ({{_}} Bind (Read _) _) => apply read_ok : prog.

Theorem write_ok:
  forall (a:addr) (v:valu),
  {< v0,
  PRE:hm         a |+> v0
  POST:hm' RET:r a |+> (v, vsmerge v0)
  CRASH:hm'      a |+> v0
  >} Write a v.

Hint Extern 1 ({{_}} Bind (Write _ _) _) => apply write_ok : prog.

Theorem possible_sync_from_sync : forall A AEQ (m m': @Mem.mem A AEQ _),
    possible_sync (sync_mem m) m' ->
    m' = sync_mem m.

Theorem sync_ok:
  {!< F,
  PRE:vm,hm          F * [[ sync_invariant F ]]
  POST:vm',hm' RET:r sync_xform F * [[ vm' = vm ]]
  CRASH:hm'          F
  >!} Sync.

Hint Extern 1 ({{_}} Bind Sync _) => apply sync_ok : prog.
Hint Extern 1 ({{_}} Bind (@Sync _) _) => apply sync_ok : prog.

Theorem trim_ok:
  forall (a:addr),
  {< v0,
  PRE:hm         a |+> v0
  POST:hm' RET:r a |+>?
  CRASH:hm'      a |+>?
  >} Trim a.

Hint Extern 1 ({{_}} Bind (Trim _) _) => apply trim_ok : prog.

Theorem hash_ok:
  forall sz (buf : word sz),
  {< (_: unit),
  PRE:hm    emp
  POST:hm'
    RET:h     emp *
              [[ hash_safe hm h buf ]] *
              [[ h = hash_fwd buf ]] *
              [[ hm' = upd_hashmap' hm h buf ]]
  CRASH:hm' emp * [[ hm' = hm ]]
  >} Hash buf.

Hint Extern 1 ({{_}} Bind (Hash _) _) => apply hash_ok : prog.

Theorem hash2_ok:
  forall sz1 sz2 (buf1 : word sz1) (buf2 : word sz2),
  {< (_: unit),
  PRE:hm    emp
  POST:hm'
    RET:h     emp *
              [[ hash_safe hm h (Word.combine buf1 buf2) ]] *
              [[ h = hash_fwd (Word.combine buf1 buf2) ]] *
              [[ hm' = upd_hashmap' hm h (Word.combine buf1 buf2) ]]
  CRASH:hm' emp * [[ hm' = hm ]]
  >} Hash2 buf1 buf2.

Hint Extern 1 ({{_}} Bind (Hash2 _ _) _) => apply hash2_ok : prog.

Theorem rdtsc_ok:
  {< (_: unit),
  PRE:hm    emp
  POST:hm'
    RET:t   emp * [[ hm' = hm ]]
  CRASH:hm' emp * [[ False ]]
  >} Rdtsc.

Hint Extern 1 ({{_}} Bind (Rdtsc) _) => apply rdtsc_ok : prog.


(** program equivalence and monad laws *)

Definition If_ T P Q (b : {P} + {Q}) (p1 p2 : prog T) :=
  if b then p1 else p2.

Theorem if_ok:
  forall T T' P Q (b : {P}+{Q}) (p1 p2 : prog T) (p': T -> prog T'),
  {{ fun vm hm done crash => exists pre, pre
   * [[ {{ fun vm' hm' done' crash' => pre * [[P]] * [[ hm = hm' ]] * [[ vm = vm' ]] * [[ done' = done ]] * [[ crash' = crash ]] }} Bind p1 p' ]]
   * [[ {{ fun vm' hm' done' crash' => pre * [[Q]] * [[ hm = hm' ]] * [[ vm = vm' ]] * [[ done' = done ]] * [[ crash' = crash ]] }} Bind p2 p' ]]
  }} Bind (If_ b p1 p2) p'.

(* helper to use If with an option *)
Definition is_some A (a: option A) : {a <> None} + {a = None}.

Hint Extern 1 ({{_}} Bind (If_ _ _ _) _) => apply if_ok : prog.
Notation "'If' b { p1 } 'else' { p2 }" := (If_ b p1 p2) (at level 9, b at level 0).

Record For_args (L : Type) := {
  For_args_i : waddr;
  For_args_n : waddr;
  For_args_l : L
}.

Theorem for_args_wf: forall L,
  well_founded (fun a b => wlt a.(@For_args_n L) b.(@For_args_n L)).

Lemma word_minus_1 : forall sz (w: word sz),
    w <> $ 0 ->
    (w ^- $1 < w)%word.

Definition For_ (L : Type) (G : Type) (f : waddr -> L -> prog L)
                (i n : waddr)
                (nocrash : G -> waddr -> L -> varmem -> hashmap -> rawpred)
                (crashed : G -> hashmap -> rawpred)
                (l : L) : prog L.

Lemma For_step: forall L G (f: waddr -> L -> prog L) i n l nocrash crashed,
  @For_ L G f i n nocrash crashed l =
    if weq n $0
    then Ret l
    else l' <- (f i l);
         @For_ L G f
             (i ^+ $1)
             (n ^- $1)
             nocrash crashed l'.

Theorem for_ok':
  forall T (n i : waddr)
         (L : Type) (G : Type)
         (f: waddr -> L -> prog L) (rx: L -> prog T)
         (nocrash : G -> waddr -> L -> varmem -> hashmap -> rawpred)
         (crashed : G -> hashmap -> rawpred)
         (li : L),
  {{ fun vm hm done crash => exists F (g:G) hm', F * nocrash g i li vm hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall m lm rxm,
      (i <= m)%word ->
      (m < n ^+ i)%word ->
      (forall lSm,
       {{ fun vm'' hm'' done' crash' => F * nocrash g (m ^+ $1) lSm vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun vm'' hm'' done' crash' => F * nocrash g m lm vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f m lm) rxm]]
   * [[forall lfinal,
       {{ fun vm'' hm'' done' crash' => F * nocrash g (n ^+ i) lfinal vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[wordToNat i + wordToNat n = wordToNat (i ^+ n)]]
   * [[forall hm'',
        F * crashed g hm'' * [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} Bind (For_ f i n nocrash crashed li) rx.

Theorem for_ok:
  forall T (n : waddr)
         (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> waddr -> L -> varmem -> hashmap -> rawpred)
         (crashed : G -> hashmap -> rawpred)
         (li : L),
  {{ fun vm hm done crash => exists F (g:G) hm', F * nocrash g $0 li vm hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall m lm rxm,
      (m < n)%word ->
      (forall lSm,
       {{ fun vm'' hm'' done' crash' => F * nocrash g (m ^+ $1) lSm vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun vm'' hm'' done' crash' => F * nocrash g m lm vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f m lm) rxm]]
   * [[forall lfinal,
       {{ fun vm'' hm'' done' crash' => F * nocrash g n lfinal vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall hm'',
        F * crashed g hm'' * [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} Bind (For_ f $0 n nocrash crashed li) rx.

Hint Extern 1 ({{_}} Bind (For_ _ _ _ _ _ _) _) => apply for_ok : prog.

Notation "'For' i < n 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (For_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        $0 n
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun vm hm => ([[ vm = vm0 ]] * nocrash)%pred)) ..))
        )) .. ))))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'For' i < n 'Hashmap' hm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (For_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        $0 n
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun vm hm => ([[ vm = vm0 ]] * nocrash)%pred)) ..))
        )) .. ))))
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Fixpoint ForN_  (L : Type) (G : Type) (f : nat -> L -> prog L)
                (i n : nat)
                (nocrash : G -> nat -> L -> varmem -> hashmap -> rawpred)
                (crashed : G -> hashmap -> rawpred)
                (l : L) : prog L :=
  match n with
  | 0 =>   Ret l
  | S m => l' <- f i l;  ForN_ f (S i) m nocrash crashed l'
  end.


Theorem forN_ok':
  forall T (n i : nat)
         (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> nat -> L -> varmem -> hashmap -> pred)
         (crashed : G -> hashmap -> pred)
         (li : L),
  {{ fun vm hm done crash => exists F (g:G) hm', F * nocrash g i li vm hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall m lm rxm,
      i <= m ->
      m < n + i ->
      (forall lSm,
       {{ fun vm'' hm'' done' crash' => F * nocrash g (S m) lSm vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun vm'' hm'' done' crash' => F * nocrash g m lm vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f m lm) rxm]]
   * [[forall lfinal,
       {{ fun vm'' hm'' done' crash' => F * nocrash g (n + i) lfinal vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall hm'',
        F * crashed g hm'' *
        [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} Bind (ForN_ f i n nocrash crashed li) rx.

Theorem forN_ok:
  forall (n : nat)
         T (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> nat -> L -> varmem -> hashmap -> pred)
         (crashed : G -> hashmap -> pred)
         (li : L),
  {{ fun vm hm done crash => exists F (g:G) hm', F * nocrash g 0 li vm hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall m lm rxm,
      m < n ->
      (forall lSm,
       {{ fun vm'' hm'' done' crash' => F * nocrash g (S m) lSm vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun vm'' hm'' done' crash' => F * nocrash g m lm vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f m lm) rxm]]
   * [[forall lfinal,
       {{ fun vm'' hm'' done' crash' => F * nocrash g n lfinal vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall hm'',
        F * crashed g hm'' *
        [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} Bind (ForN_ f 0 n nocrash crashed li) rx.

Hint Extern 1 ({{_}} Bind (ForN_ _ _ _ _ _ _) _) => apply forN_ok : prog.

Notation "'ForN' i < n 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForN_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        0 n
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun vm hm => ([[ vm = vm0 ]] * nocrash)%pred)) ..))
        )) .. ))))
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'ForN' i < n 'Hashmap' hm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForN_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        0 n
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun vm hm => ([[ vm = vm0 ]] * nocrash)%pred)) ..))
        )) .. ))))
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))))
  (at level 9, i at level 0, n at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'ForN' x <= i < n 'Hashmap' hm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForN_ (fun i =>
          (pair_args_helper (fun l1 => ..
            (pair_args_helper (fun l2 (_:unit) => body))
          ..)))
        x (n - x)
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun i =>
          (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
           fun vm hm => ([[ vm = vm0 ]] * nocrash)%pred)) ..))
        )) .. ))))
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))))
  (at level 9, i at level 0, n at level 0, x at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Fixpoint ForEach_ (ITEM : Type)
                (L : Type) (G : Type) (f : ITEM -> L -> prog L)
                (lst : list ITEM)
                (nocrash : G -> list ITEM -> L -> varmem -> hashmap -> rawpred)
                (crashed : G -> hashmap -> rawpred)
                (l : L) : prog L :=
  match lst with
  | nil => Ret l
  | elem :: lst' =>
    l' <- f elem l;
    ForEach_ f lst' nocrash crashed l'
  end.

Theorem foreach_ok:
  forall T ITEM (lst : list ITEM)
         (L : Type) (G : Type)
         f (rx: _ -> prog T)
         (nocrash : G -> list ITEM -> L -> varmem -> hashmap -> pred)
         (crashed : G -> hashmap -> pred)
         (li : L),
  {{ fun vm hm done crash => exists F (g:G) hm', F * nocrash g lst li vm hm
   * [[ exists l, hashmap_subset l hm' hm ]]
   * [[forall elem lst' lm rxm,
      (forall lSm,
       {{ fun vm'' hm'' done' crash' => F * nocrash g lst' lSm vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]]  * [[ crash' = crash ]]
       }} rxm lSm) ->
      {{ fun vm'' hm'' done' crash' => F * nocrash g (elem :: lst') lm vm'' hm'' *
         [[ exists l, hashmap_subset l hm' hm'' ]] *
         [[ exists prefix, prefix ++ elem :: lst' = lst ]] *
         [[ done' = done ]] * [[ crash' = crash ]]
      }} Bind (f elem lm) rxm]]
   * [[forall lfinal,
       {{ fun vm'' hm'' done' crash' => F * nocrash g nil lfinal vm'' hm'' *
          [[ exists l, hashmap_subset l hm' hm'' ]] *
          [[ done' = done ]] * [[ crash' = crash ]]
       }} rx lfinal]]
   * [[forall hm'',
        F * crashed g hm'' * [[ exists l, hashmap_subset l hm' hm'' ]] =p=> crash hm'' ]]
  }} Bind (ForEach_ f lst nocrash crashed li) rx.

Hint Extern 1 ({{_}} Bind (ForEach_ _ _ _ _ _) _) => apply foreach_ok : prog.

Notation "'ForEach' elem rest lst 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForEach_ (fun elem => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) => body)) ..)))
        lst
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun rest => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
         fun vm hm => ([[ vm = vm0 ]] * nocrash)%pred)) ..))  )) .. ))))
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))))
  (at level 9, elem at level 0, rest at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

Notation "'ForEach' elem rest lst 'Hashmap' hm 'Ghost' [ g1 .. g2 ] 'Loopvar' [ l1 .. l2 ] 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (ForEach_ (fun elem => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) => body)) ..)))
        lst
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun rest => (pair_args_helper (fun l1 => .. (pair_args_helper (fun l2 (_:unit) =>
         fun vm hm => ([[ vm = vm0 ]] * nocrash)%pred)) ..))  )) .. ))))
        (pair_args_helper (fun vm0 =>
        (pair_args_helper (fun g1 => .. (pair_args_helper (fun g2 (_:unit) =>
         fun hm => crashed%pred)) .. )))))
  (at level 9, elem at level 0, rest at level 0,
   g1 closed binder, g2 closed binder,
   l1 closed binder, l2 closed binder,
   body at level 9).

(* TODO: need a good spec for this. Probably want a predicate
describing early breaks, so that we can guarantee something if the
function terminates without breaking (otherwise the spec would equally
apply to a loop that didn't do anything) *)
Fixpoint ForNBreak_  (L : Type) (G : Type) (f : nat -> L -> prog (L+L))
                (i n : nat)
                (nocrash : G -> nat -> L -> varmem -> hashmap -> rawpred)
                (crashed : G -> hashmap -> rawpred)
                (l : L) : prog L :=
  match n with
  | 0 =>   Ret l
  | S m => l' <- f i l;
            match l' with
            | inl l' => ForNBreak_ f (S i) m nocrash crashed l'
            | inr l' => Ret l'
            end
  end.

Definition Continue L (l:L) : L + L := inl l.
Definition Break L (l:L) : L + L := inr l.


Theorem var_get_ok:
  forall (Tv : Type) (i : vartype),
  {< (x : Tv) Fv,
  PRE::vm,hm          emp * [[ (Fv * i |-> Any x)%pred vm ]]
  POST::vm',hm' RET:r emp * [[ r = x ]] * [[ vm' = vm ]]
  CRASH:hm'           [[ False ]]
  >} VarGet i.

Hint Extern 1 ({{_}} Bind (VarGet _) _) => apply var_get_ok : prog.

Theorem var_set_ok:
  forall (T : Type) (i : vartype) (v : T),
  {< v0 Fv,
  PRE::vm,hm          emp * [[ (Fv * i |-> v0)%pred vm ]]
  POST::vm',hm' RET:_ emp * [[ (Fv * i |-> Any v)%pred vm' ]]
  CRASH:hm'           [[ False ]]
  >} VarSet i v.

Hint Extern 1 ({{_}} Bind (VarSet _ _) _) => apply var_set_ok : prog.

Theorem var_alloc_ok:
  forall (T : Type) (v : T),
  {< Fv,
  PRE::vm,hm          emp * [[ Fv vm ]]
  POST::vm',hm' RET:r emp * [[ (Fv * r |-> Any v)%pred vm' ]]
  CRASH:hm'           [[ False ]]
  >} VarAlloc v.

Hint Extern 1 ({{_}} Bind (VarAlloc _) _) => apply var_alloc_ok : prog.

Theorem var_delete_ok:
  forall (i : vartype),
  {< v Fv,
  PRE::vm,hm          emp * [[ (Fv * i |-> v)%pred vm ]]
  POST::vm',hm' RET:_ emp * [[ Fv vm' ]]
  CRASH:hm'           [[ False ]]
  >} VarDelete i.

Hint Extern 1 ({{_}} Bind (VarDelete _) _) => apply var_delete_ok : prog.