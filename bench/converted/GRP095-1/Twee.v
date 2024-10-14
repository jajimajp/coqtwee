(* Generated by tptp2coqp *)
Require Import Setoid.
From CoqTwee Require Import Twee.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter a2 : G.
Parameter a3 : G.
Parameter a4 : G.
Parameter b1 : G.
Parameter b2 : G.
Parameter b3 : G.
Parameter b4 : G.
Parameter c3 : G.
Parameter divide : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_identity : forall X : G, identity = (divide X X).
Axiom ax_inverse : forall X : G, (inverse X) = (divide identity X).
Axiom ax_multiply : forall X Y : G, (multiply X Y) = (divide X (divide identity Y)).
Axiom ax_single_axiom : forall X Y Z : G, (divide (divide identity X) (divide (divide (divide Y X) Z) Y)) = Z.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  twee ax_identity ax_inverse ax_multiply ax_single_axiom.
Qed.

Check check.

