(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter commutator : G -> G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_associativity_of_commutator : forall A B C : G, (commutator (commutator A B) C) = (commutator A (commutator B C)).
Axiom ax_commutator : forall A B : G, (multiply A B) = (multiply B (multiply A (commutator A B))).
Axiom ax_left_cancellation : forall A B C : G, (multiply A B) = (multiply A C).
Axiom ax_right_cancellation : forall A B C : G, (multiply A B) = (multiply C B).
Axiom ax_associativity_of_multiply : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).


(* Goal *)
Theorem check : (commutator (multiply a b) c) = (multiply (commutator a c) (commutator b c)).
Proof.
  hammer.
Qed.

Check check.

