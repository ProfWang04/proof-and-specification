Definition vsupd (vs : list valuset) (i : addr) (v : valu) : list valuset :=
  updN vs i (v, vsmerge (selN vs i ($0, nil))).

Definition vssync (vs : list valuset) (i : addr) : list valuset :=
  updN vs i (fst (selN vs i ($0, nil)), nil).

Definition vsupd_range (vsl : list valuset) (vl : list valu) :=
  let n := length vl in
  (List.combine vl (map vsmerge (firstn n vsl))) ++ skipn n vsl.

Definition vs_synced a (vl : list valuset) :=
  snd (selN vl a ($0, nil)) = nil.

Definition vssync_range (vsl : list valuset) n :=
  (List.combine (map fst (firstn n vsl)) (repeat nil n)) ++ skipn n vsl.
    
(** update vsl according to (addr, valu) pairs in l. *)
Definition vsupd_vecs (vsl : list valuset) (l : list (addr * valu)) : list valuset :=
  fold_left (fun vs e => (vsupd vs (fst e) (snd e))) l vsl.

(** sync vsl for all addresses in l. *)
Definition vssync_vecs (vsl : list valuset) (l : list addr) : list valuset :=
  fold_left vssync l vsl.

Definition vssync_vecs_rev (vsl : list valuset) (l : list addr) : list valuset :=
  fold_right (fun a m => vssync m a) vsl (rev l).

