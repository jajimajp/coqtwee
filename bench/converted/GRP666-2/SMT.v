(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable b : Z.
Variable c : Z.
Variable i : Z -> Z.
Variable ld : Z -> Z -> Z.
Variable mult : Z -> Z -> Z.
Variable rd : Z -> Z -> Z.
Variable unit : Z.
Axiom ax_c11 : forall A B : Z, (mult (mult A B) (i B)) =? A.
Axiom ax_c10 : forall A B : Z, (mult (i A) (mult A B)) =? B.
Axiom ax_c09 : forall A B C : Z, (ld A (mult (mult B C) A)) =? (mult (ld A (mult B A)) (ld A (mult C A))).
Axiom ax_c08 : forall A B C D : Z, (rd (mult (mult (mult A B) C) D) (mult C D)) =? (mult (rd (mult (mult A C) D) (mult C D)) (rd (mult (mult B C) D) (mult C D))).
Axiom ax_c07 : forall A B C D : Z, (ld (mult A B) (mult A (mult B (mult C D)))) =? (mult (ld (mult A B) (mult A (mult B C))) (ld (mult A B) (mult A (mult B D)))).
Axiom ax_c06 : forall A : Z, (mult unit A) =? A.
Axiom ax_c05 : forall A : Z, (mult A unit) =? A.
Axiom ax_c04 : forall A B : Z, (rd (mult A B) B) =? A.
Axiom ax_c03 : forall A B : Z, (mult (rd A B) B) =? A.
Axiom ax_c02 : forall A B : Z, (ld A (mult A B)) =? B.
Axiom ax_c01 : forall A B : Z, (mult A (ld A B)) =? B.

Add_lemmas ax_c11 ax_c10 ax_c09 ax_c08 ax_c07 ax_c06 ax_c05 ax_c04 ax_c03 ax_c02 ax_c01.

(* Goal *)
Theorem check : (mult a (mult b (mult a c))) =? (mult (mult (mult a b) a) c).
Proof.
  smt.
Qed.

Check check.

