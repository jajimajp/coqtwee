(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable b : Z.
Variable double_divide : Z -> Z -> Z.
Variable identity : Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_identity : forall A : Z, identity =? (double_divide A (inverse A)).
Axiom ax_inverse : forall A : Z, (inverse A) =? (double_divide A identity).
Axiom ax_multiply : forall A B : Z, (multiply A B) =? (double_divide (double_divide B A) identity).
Axiom ax_single_axiom : forall A B C : Z, (double_divide (double_divide A (double_divide (double_divide B (double_divide C A)) (double_divide C identity))) (double_divide identity identity)) =? B.

Add_lemmas ax_identity ax_inverse ax_multiply ax_single_axiom.

(* Goal *)
Theorem check : (multiply a b) =? (multiply b a).
Proof.
  smt.
Qed.

Check check.

