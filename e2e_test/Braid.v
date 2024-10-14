Require Import Setoid.
Declare ML Module "coqtwee.plugin".


Parameter G : Set.
Parameter f : G -> G -> G.
Infix "*" := f (at level 40, left associativity).

Parameter e : G.
Parameter c1 : G.
Parameter c2 : G.

Axiom a0 : forall X : G, e * X = X.
Axiom a1 : forall X : G, X * e = X.
Axiom a2 : forall X Y Z : G, (X * Y) * Z = X * (Y * Z).
Axiom a3 : c1 * (c2 * c1) = c2 * (c1 * c2).
Axiom a4 : e = c1 * c1.
Axiom a5 : c2 * c2 = e.

Theorem check1: c1 * c2 * c1 = c2 * c1 * c2.
Proof.
  twee a0 a1 a2 a3 a4 a5.
Qed.
