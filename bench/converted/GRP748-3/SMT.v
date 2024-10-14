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
Axiom ax_f11 : forall A B : Z, (mult A B) =? (mult B A).
Axiom ax_f10 : forall A : Z, (mult (i A) A) =? unit.
Axiom ax_f09 : forall A : Z, (mult A (i A)) =? unit.
Axiom ax_f08 : forall A B : Z, (mult (mult A B) (i B)) =? A.
Axiom ax_f07 : forall A B C : Z, (mult (mult (mult A B) C) B) =? (mult A (mult (mult B C) B)).
Axiom ax_f06 : forall A : Z, (mult unit A) =? A.
Axiom ax_f05 : forall A : Z, (mult A unit) =? A.
Axiom ax_f04 : forall A B : Z, (rd (mult A B) B) =? A.
Axiom ax_f03 : forall A B : Z, (mult (rd A B) B) =? A.
Axiom ax_f02 : forall A B : Z, (ld A (mult A B)) =? B.
Axiom ax_f01 : forall A B : Z, (mult A (ld A B)) =? B.

Add_lemmas ax_f11 ax_f10 ax_f09 ax_f08 ax_f07 ax_f06 ax_f05 ax_f04 ax_f03 ax_f02 ax_f01.

(* Goal *)
Theorem check : (mult a (mult b (mult c b))) =? (mult (mult (mult a b) c) b).
Proof.
  smt.
Qed.

Check check.

