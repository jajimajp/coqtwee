(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable asoc : Z -> Z -> Z -> Z.
Variable b : Z.
Variable c : Z.
Variable d : Z.
Variable i : Z -> Z.
Variable mult : Z -> Z -> Z.
Variable op_k : Z -> Z -> Z.
Variable op_l : Z -> Z -> Z -> Z.
Variable op_r : Z -> Z -> Z -> Z.
Variable op_t : Z -> Z -> Z.
Variable rd : Z -> Z -> Z.
Variable unit : Z.
Axiom ax_c22 : forall A B C D E : Z, (asoc A B (asoc C D E)) =? unit.
Axiom ax_c21 : forall A B C D E : Z, (asoc (asoc A B C) D E) =? unit.
Axiom ax_c20 : forall A B C : Z, (op_t (op_t A B) C) =? (op_t (op_t A C) B).
Axiom ax_c19 : forall A B C D : Z, (op_t (op_l A B C) D) =? (op_l (op_t A D) B C).
Axiom ax_c18 : forall A B C D : Z, (op_t (op_r A B C) D) =? (op_r (op_t A D) B C).
Axiom ax_c17 : forall A B C D E : Z, (op_l (op_l A B C) D E) =? (op_l (op_l A D E) B C).
Axiom ax_c16 : forall A B C D E : Z, (op_l (op_r A B C) D E) =? (op_r (op_l A D E) B C).
Axiom ax_c15 : forall A B C D E : Z, (op_r (op_r A B C) D E) =? (op_r (op_r A D E) B C).
Axiom ax_c14 : forall A B : Z, (op_t A B) =? (mult (i B) (mult A B)).
Axiom ax_c13 : forall A B C : Z, (op_r A B C) =? (rd (mult (mult A B) C) (mult B C)).
Axiom ax_c12 : forall A B C : Z, (op_l A B C) =? (mult (i (mult C B)) (mult C (mult B A))).
Axiom ax_c11 : forall A B : Z, (mult A B) =? (mult (mult B A) (op_k A B)).
Axiom ax_c10 : forall A B C : Z, (mult (mult A B) C) =? (mult (mult A (mult B C)) (asoc A B C)).
Axiom ax_c09 : forall A B C : Z, (mult (mult A (mult B A)) C) =? (mult A (mult B (mult A C))).
Axiom ax_c08 : forall A B : Z, (mult (rd A B) B) =? A.
Axiom ax_c07 : forall A B : Z, (rd (mult A B) B) =? A.
Axiom ax_c06 : forall A B : Z, (mult (i A) (mult A B)) =? B.
Axiom ax_c05 : forall A B : Z, (i (mult A B)) =? (mult (i A) (i B)).
Axiom ax_c04 : forall A : Z, (mult (i A) A) =? unit.
Axiom ax_c03 : forall A : Z, (mult A (i A)) =? unit.
Axiom ax_c02 : forall A : Z, (mult A unit) =? A.
Axiom ax_c01 : forall A : Z, (mult unit A) =? A.

Add_lemmas ax_c22 ax_c21 ax_c20 ax_c19 ax_c18 ax_c17 ax_c16 ax_c15 ax_c14 ax_c13 ax_c12 ax_c11 ax_c10 ax_c09 ax_c08 ax_c07 ax_c06 ax_c05 ax_c04 ax_c03 ax_c02 ax_c01.

(* Goal *)
Theorem check : (asoc a b (op_k c d)) =? unit.
Proof.
  smt.
Qed.

Check check.

