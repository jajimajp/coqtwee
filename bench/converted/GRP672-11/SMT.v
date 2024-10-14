(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable asoc : Z -> Z -> Z -> Z.
Variable ld : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable op_t : Z.
Variable op_x : Z.
Variable op_y : Z.
Variable op_z : Z.
Variable rd : Z -> Z -> Z.
Variable unit : Z.
Axiom ax_f09 : (mult op_z (asoc op_x op_y op_t)) =? (mult (asoc op_x op_y op_t) op_z).
Axiom ax_f08 : forall A B C : Z, (asoc A B C) =? (ld (mult A (mult B C)) (mult (mult A B) C)).
Axiom ax_f07 : forall A B C : Z, (mult A (mult B (mult C A))) =? (mult (mult (mult A B) C) A).
Axiom ax_f06 : forall A : Z, (mult unit A) =? A.
Axiom ax_f05 : forall A : Z, (mult A unit) =? A.
Axiom ax_f04 : forall A B : Z, (rd (mult A B) B) =? A.
Axiom ax_f03 : forall A B : Z, (mult (rd A B) B) =? A.
Axiom ax_f02 : forall A B : Z, (ld A (mult A B)) =? B.
Axiom ax_f01 : forall A B : Z, (mult A (ld A B)) =? B.

Add_lemmas ax_f09 ax_f08 ax_f07 ax_f06 ax_f05 ax_f04 ax_f03 ax_f02 ax_f01.

(* Goal *)
Theorem check : (mult (asoc op_x op_y op_z) (asoc op_x op_y op_t)) =? (asoc op_x op_y (mult op_z op_t)).
Proof.
  smt.
Qed.

Check check.

