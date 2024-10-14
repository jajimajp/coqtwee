(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter identity : G.
Parameter multiply : G -> G -> G.
Axiom ax_a_times_b_is_c : (multiply a b) = c.
Axiom ax_squareness : forall X : G, (multiply X X) = identity.
Axiom ax_left_identity : forall X : G, (multiply identity X) = X.
Axiom ax_associativity : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).


(* Goal *)
Theorem check : (multiply b a) = c.
Proof.
  hammer.
Qed.

Check check.

