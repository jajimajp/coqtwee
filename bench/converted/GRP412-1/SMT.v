(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a1 : Z.
Variable b1 : Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_single_axiom : forall A B C : Z, (multiply A (inverse (multiply (multiply (multiply (inverse B) B) (inverse (multiply (inverse (multiply A (inverse B))) C))) B))) =? C.

Add_lemmas ax_single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) =? (multiply (inverse b1) b1).
Proof.
  smt.
Qed.

Check check.

