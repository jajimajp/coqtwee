(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter op_c : G.
Parameter op_d : G.
Parameter op_e : G.
Parameter op_f : G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Parameter x4 : G.
Parameter x5 : G.
Axiom ax_f13 : forall A B : G, op_f = (mult A (mult B (ld (mult A B) op_c))).
Axiom ax_f12 : forall A B : G, op_e = (mult (mult (rd op_c (mult A B)) B) A).
Axiom ax_f11 : forall A : G, op_d = (ld A (mult op_c A)).
Axiom ax_f10 : forall A B : G, (mult A (mult op_c B)) = (mult (mult A op_c) B).
Axiom ax_f09 : forall A B : G, (mult A (mult B op_c)) = (mult (mult A B) op_c).
Axiom ax_f08 : forall A B : G, (mult op_c (mult A B)) = (mult (mult op_c A) B).
Axiom ax_f07 : forall A B C : G, (mult A (mult B (mult B C))) = (mult (mult (mult A B) B) C).
Axiom ax_f06 : forall A : G, (mult unit A) = A.
Axiom ax_f05 : forall A : G, (mult A unit) = A.
Axiom ax_f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom ax_f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom ax_f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom ax_f01 : forall A B : G, (mult A (ld A B)) = B.


(* Goal *)
Theorem check : (mult x4 (mult x5 op_f)) = (mult (mult x4 x5) op_f).
Proof.
  hammer.
Qed.

Check check.

