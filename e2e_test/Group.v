Require Import Setoid.
Declare ML Module "coqtwee.plugin".

Parameter G : Set.
Parameter e : G.
Parameter i : G -> G.
Parameter f : G -> G -> G.

Axiom left_identity : forall X, f e X = X.
Axiom left_inverse : forall X, f (i X) X = e.
Axiom associativity : forall X Y Z, f X (f Y Z) = f (f X Y) Z.

Goal forall X, f X e = X.
Proof.
  twee left_identity left_inverse associativity.
Qed.
