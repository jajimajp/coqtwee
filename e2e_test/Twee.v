Declare ML Module "coqtwee.plugin".

Parameter G : Set.
Parameter O : G.
Parameter i : G -> G.
Parameter f : G -> G -> G.

Axiom plus_zero : forall X, f O X = X.
Axiom minus_left : forall X, f (i X) X = O.
Axiom associativity : forall X Y Z, f X (f Y Z) = f (f X Y) Z.

Goal forall a b, f a b = a -> b = O.
Proof.
  intros.
  twee plus_zero minus_left associativity H.
Qed.

