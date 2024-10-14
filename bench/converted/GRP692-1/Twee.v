(* Generated by tptp2coqp *)
Require Import Setoid.
From CoqTwee Require Import Twee.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter i : G -> G.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter op_c : G.
Parameter op_d : G.
Parameter op_e : G.
Parameter op_f : G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Axiom ax_c13 : (mult op_e op_e) = op_f.
Axiom ax_c12 : (mult op_d op_d) = op_e.
Axiom ax_c11 : (mult op_c (mult op_c op_c)) = op_d.
Axiom ax_c10 : forall A : G, (mult A (i A)) = unit.
Axiom ax_c09 : forall A : G, (mult (i A) A) = unit.
Axiom ax_c08 : forall A B C : G, (mult (mult A B) C) = (mult (mult A C) (ld C (mult B C))).
Axiom ax_c07 : forall A B C : G, (mult A (mult B C)) = (mult (rd (mult A B) A) (mult A C)).
Axiom ax_c06 : forall A : G, (mult unit A) = A.
Axiom ax_c05 : forall A : G, (mult A unit) = A.
Axiom ax_c04 : forall A B : G, (rd (mult A B) B) = A.
Axiom ax_c03 : forall A B : G, (mult (rd A B) B) = A.
Axiom ax_c02 : forall A B : G, (ld A (mult A B)) = B.
Axiom ax_c01 : forall A B : G, (mult A (ld A B)) = B.


(* Goal *)
Theorem check : (mult op_e (mult a (mult b op_e))) = (mult (mult (mult op_e a) b) op_e).
Proof.
  twee ax_c13 ax_c12 ax_c11 ax_c10 ax_c09 ax_c08 ax_c07 ax_c06 ax_c05 ax_c04 ax_c03 ax_c02 ax_c01.
Qed.

Check check.

