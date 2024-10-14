Require Import Setoid.
Declare ML Module "coqtwee.plugin".


Parameter G : Set.

Parameter f : G -> G -> G.
Infix "+" := f (at level 50, left associativity).

Parameter e : G.

Parameter i : G -> G.

Axiom ax0 : forall X Y, X + Y = Y + X.
Axiom ax1 : forall X, e + X = X.
Axiom ax2 : forall X Y Z, (X + Y) + Z = X + (Y + Z).


Theorem check: forall X Y Z, X + (Y + Z) = Z + (X + Y).
Proof.
  twee ax0 ax1 ax2.
Qed.
