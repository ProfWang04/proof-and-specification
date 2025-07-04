Require Import AsyncDisk.

Set Implicit Arguments.

Theorem destruct_pair2 : forall X1 X2 (p : X1 * X2),
	exists x1 x2 , p = (x1, x2).
Theorem destruct_pair4 : forall X1 X2 X3 X4 (p : X1 * X2 * X3 * X4),
	exists x1 x2 x3 x4 , p = (x1, x2, x3, x4).
Theorem destruct_pair6 : forall X1 X2 X3 X4 X5 X6 (p : X1 * X2 * X3 * X4 * X5 * X6),
	exists x1 x2 x3 x4 x5 x6 , p = (x1, x2, x3, x4, x5, x6).
Theorem destruct_pair8 : forall X1 X2 X3 X4 X5 X6 X7 X8 (p : X1 * X2 * X3 * X4 * X5 * X6 * X7 * X8),
	exists x1 x2 x3 x4 x5 x6 x7 x8 , p = (x1, x2, x3, x4, x5, x6, x7, x8).
Theorem destruct_pair10 : forall X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 (p : X1 * X2 * X3 * X4 * X5 * X6 * X7 * X8 * X9 * X10),
	exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 , p = (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10).
Theorem destruct_pair12 : forall X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 (p : X1 * X2 * X3 * X4 * X5 * X6 * X7 * X8 * X9 * X10 * X11 * X12),
	exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 , p = (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12).
Theorem destruct_pair14 : forall X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 (p : X1 * X2 * X3 * X4 * X5 * X6 * X7 * X8 * X9 * X10 * X11 * X12 * X13 * X14),
	exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 , p = (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14).
Theorem destruct_pair16 : forall X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 (p : X1 * X2 * X3 * X4 * X5 * X6 * X7 * X8 * X9 * X10 * X11 * X12 * X13 * X14 * X15 * X16),
	exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 , p = (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16).