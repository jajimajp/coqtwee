Require Import Setoid.
Declare ML Module "coqtwee.plugin".

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter identity : G.
Parameter multiply : G -> G -> G.
Axiom a_times_b_is_c : (multiply a b) = c.
Axiom squareness : forall X : G, (multiply X X) = identity.
Axiom left_identity : forall X : G, (multiply identity X) = X.
Axiom associativity : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).


(* Goal *)
Theorem check : (multiply b a) = c.
Proof.
  twee a_times_b_is_c squareness left_identity associativity.
Qed.

Check check.
