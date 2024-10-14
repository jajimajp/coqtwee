(* Generated by tptp2coqp *)
Require Import Setoid.
Declare ML Module "coqtwee.plugin".

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter equalish : G -> G -> G.
Parameter identity : G.
Parameter ifeq : G -> G -> G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Parameter product : G -> G -> G -> G.
Parameter true : G.
Axiom ax_a_equals_b : (equalish a b) = true.
Axiom ax_product_substitution3 : forall W X Y Z : G, (ifeq (equalish X Y) true (ifeq (product W Z X) true (product W Z Y) true) true) = true.
Axiom ax_associativity2 : forall U V W X Y Z : G, (ifeq (product Y Z V) true (ifeq (product X V W) true (ifeq (product X Y U) true (product U Z W) true) true) true) = true.
Axiom ax_associativity1 : forall U V W X Y Z : G, (ifeq (product U Z W) true (ifeq (product Y Z V) true (ifeq (product X Y U) true (product X V W) true) true) true) = true.
Axiom ax_total_function2 : forall W X Y Z : G, (ifeq (product X Y W) true (ifeq (product X Y Z) true (equalish Z W) true) true) = true.
Axiom ax_total_function1 : forall X Y : G, (product X Y (multiply X Y)) = true.
Axiom ax_left_inverse : forall X : G, (product (inverse X) X identity) = true.
Axiom ax_left_identity : forall X : G, (product identity X X) = true.
Axiom ax_ifeq_axiom : forall A B C : G, (ifeq A A B C) = B.


(* Goal *)
Theorem check : (equalish (inverse a) (inverse b)) = true.
Proof.
  twee ax_a_equals_b ax_product_substitution3 ax_associativity2 ax_associativity1 ax_total_function2 ax_total_function1 ax_left_inverse ax_left_identity ax_ifeq_axiom.
Qed.

Check check.

