Set Implicit Arguments.

Theorem destruct_two : forall A B (p : A * B),
  exists a b, p = (a, b).

Theorem destruct_four : forall A B C D (p : A * B * C * D),
  exists a b c d, p = (a, b, c, d).

Theorem destruct_eight : forall A B C D E F G H (p : A * B * C * D * E * F * G * H),
  exists a b c d e f g h, p = (a, b, c, d, e, f, g, h).

Theorem x : forall (x : unit * bool * nat * list nat * option nat * nat * unit * bool * bool * nat * unit * bool),
  x = x.