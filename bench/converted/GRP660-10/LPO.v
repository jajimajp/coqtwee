(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter tuple : G -> G -> G.
Parameter x1 : G -> G.
Parameter x1_2 : G -> G.
Axiom ax_f05 : forall A B C : G, (mult (mult (mult A B) C) A) = (mult A (mult B (mult C A))).
Axiom ax_f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom ax_f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom ax_f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom ax_f01 : forall A B : G, (mult A (ld A B)) = B.

Complete ax_f05 ax_f04 ax_f03 ax_f02 ax_f01 : ld mult rd tuple x1 x1_2 : hint
  for (forall X0 : G, (tuple (mult X0 (x1 X0)) (mult (x1_2 X0) X0)) = (tuple (x1 X0) (x1_2 X0))).

(* Goal *)
Theorem check : forall X0 : G, (tuple (mult X0 (x1 X0)) (mult (x1_2 X0) X0)) = (tuple (x1 X0) (x1_2 X0)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

