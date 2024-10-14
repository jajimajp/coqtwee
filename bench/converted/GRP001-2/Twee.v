(* Generated by tptp2coqp *)
Require Import Setoid.
From CoqTwee Require Import Twee.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_a_times_b_is_c : (multiply a b) = c.
Axiom ax_squareness : forall X : G, (multiply X X) = identity.
Axiom ax_right_inverse : forall X : G, (multiply X (inverse X)) = identity.
Axiom ax_right_identity : forall X : G, (multiply X identity) = X.
Axiom ax_associativity : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom ax_left_inverse : forall X : G, (multiply (inverse X) X) = identity.
Axiom ax_left_identity : forall X : G, (multiply identity X) = X.


(* Goal *)
Theorem check : (multiply b a) = c.
Proof.
  twee ax_a_times_b_is_c ax_squareness ax_right_inverse ax_right_identity ax_associativity ax_left_inverse ax_left_identity.
Qed.

Check check.

