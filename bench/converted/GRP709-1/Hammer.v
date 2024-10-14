(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter op_c : G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Axiom ax_c09 : forall A B : G, (mult A (mult B op_c)) = (mult (mult A B) op_c).
Axiom ax_c08 : forall A : G, (mult op_c A) = (mult A op_c).
Axiom ax_c07 : forall A B C : G, (mult A (mult B (mult A C))) = (mult (mult A (mult B A)) C).
Axiom ax_c06 : forall A : G, (mult unit A) = A.
Axiom ax_c05 : forall A : G, (mult A unit) = A.
Axiom ax_c04 : forall A B : G, (rd (mult A B) B) = A.
Axiom ax_c03 : forall A B : G, (mult (rd A B) B) = A.
Axiom ax_c02 : forall A B : G, (ld A (mult A B)) = B.
Axiom ax_c01 : forall A B : G, (mult A (ld A B)) = B.


(* Goal *)
Theorem check : (mult (mult op_c op_c) (mult a b)) = (mult (mult (mult op_c op_c) a) b).
Proof.
  hammer.
Qed.

Check check.

