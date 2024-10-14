(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter asoc : G -> G -> G -> G.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter op_t : G.
Parameter op_x : G.
Parameter op_y : G.
Parameter op_z : G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Axiom ax_f09 : (mult (asoc op_x op_y op_z) (asoc op_x op_y op_t)) = (asoc op_x op_y (mult op_z op_t)).
Axiom ax_f08 : forall A B C : G, (asoc A B C) = (ld (mult A (mult B C)) (mult (mult A B) C)).
Axiom ax_f07 : forall A B C : G, (mult A (mult B (mult C A))) = (mult (mult (mult A B) C) A).
Axiom ax_f06 : forall A : G, (mult unit A) = A.
Axiom ax_f05 : forall A : G, (mult A unit) = A.
Axiom ax_f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom ax_f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom ax_f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom ax_f01 : forall A B : G, (mult A (ld A B)) = B.


(* Goal *)
Theorem check : (mult op_z (asoc op_x op_y op_t)) = (mult (asoc op_x op_y op_t) op_z).
Proof.
  hammer.
Qed.

Check check.

