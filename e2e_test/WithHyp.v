Require Import Setoid.
Declare ML Module "coqtwee.plugin".

Parameter G : Set.
Parameter e : G.
Parameter i : G -> G.
Parameter f : G -> G -> G.

Axiom plus_zero : forall X, f e X = X.
Axiom minus_left : forall X, f (i X) X = e.
Axiom associativity : forall X Y Z, f X (f Y Z) = f (f X Y) Z.

Goal forall a b, f a b = a -> b = e.
Proof.
  intros a b h.
  twee plus_zero minus_left associativity h.
Qed.
