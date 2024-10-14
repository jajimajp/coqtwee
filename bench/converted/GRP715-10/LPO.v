(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter minus : G -> G.
Parameter mult : G -> G -> G.
Parameter op_0 : G.
Parameter op_a : G.
Parameter op_b : G.
Parameter plus : G -> G -> G.
Parameter unit : G.
Parameter x0 : G.
(* HACK: for coq-completion *)
Hint Resolve op_0 : hint_hack_compl.
Axiom ax_f11 : (mult op_b op_a) = unit.
Axiom ax_f10 : (mult op_a op_b) = unit.
Axiom ax_f09 : forall A : G, (mult unit A) = A.
Axiom ax_f08 : forall A : G, (mult A unit) = A.
Axiom ax_f07 : forall A B : G, (mult A (mult B B)) = (mult (mult A B) B).
Axiom ax_f06 : forall A B C : G, (mult (mult (mult A B) C) B) = (mult A (mult (mult B C) B)).
Axiom ax_f05 : forall A B C : G, (mult A (plus B C)) = (plus (mult A B) (mult A C)).
Axiom ax_f04 : forall A : G, (plus A (minus A)) = op_0.
Axiom ax_f03 : forall A : G, (plus A op_0) = A.
Axiom ax_f02 : forall A B : G, (plus A B) = (plus B A).
Axiom ax_f01 : forall A B C : G, (plus (plus A B) C) = (plus A (plus B C)).

Complete ax_f11 ax_f10 ax_f09 ax_f08 ax_f07 ax_f06 ax_f05 ax_f04 ax_f03 ax_f02 ax_f01 : minus mult op_0 op_a op_b plus unit x0 : hint
  for ((mult (mult x0 op_a) op_b) = x0).

(* Goal *)
Theorem check : (mult (mult x0 op_a) op_b) = x0.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

