(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable a0 : Z.
Variable b : Z.
Variable b0 : Z.
Variable c : Z.
Variable c0 : Z.
Variable d : Z.
Variable d0 : Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_prove_quotient3 : (multiply b d0) =? (multiply a c0).
Axiom ax_prove_quotient2 : (multiply d b0) =? (multiply c a0).
Axiom ax_prove_quotient1 : (multiply b b0) =? (multiply a a0).
Axiom ax_nilpotency : forall X Y Z : Z, (multiply X (multiply Y (multiply Z (multiply Y X)))) =? (multiply Y (multiply X (multiply Z (multiply X Y)))).
Axiom ax_left_cancellation : forall A B C : Z, (multiply A B) =? (multiply A C).
Axiom ax_right_cancellation : forall A B C : Z, (multiply A B) =? (multiply C B).
Axiom ax_associativity_of_multiply : forall X Y Z : Z, (multiply (multiply X Y) Z) =? (multiply X (multiply Y Z)).

Add_lemmas ax_prove_quotient3 ax_prove_quotient2 ax_prove_quotient1 ax_nilpotency ax_left_cancellation ax_right_cancellation ax_associativity_of_multiply.

(* Goal *)
Theorem check : (multiply d d0) =? (multiply c c0).
Proof.
  smt.
Qed.

Check check.

