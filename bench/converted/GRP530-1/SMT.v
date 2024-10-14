(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a2 : Z.
Variable b2 : Z.
Variable divide : Z -> Z -> Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_inverse : forall A B : Z, (inverse A) =? (divide (divide B B) A).
Axiom ax_multiply : forall A B C : Z, (multiply A B) =? (divide A (divide (divide C C) B)).
Axiom ax_single_axiom : forall A B C : Z, (divide (divide A (divide B C)) (divide A B)) =? C.

Add_lemmas ax_inverse ax_multiply ax_single_axiom.

(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) =? a2.
Proof.
  smt.
Qed.

Check check.

