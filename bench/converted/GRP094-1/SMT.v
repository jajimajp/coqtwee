(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a1 : Z.
Variable a2 : Z.
Variable a3 : Z.
Variable a4 : Z.
Variable b1 : Z.
Variable b2 : Z.
Variable b3 : Z.
Variable b4 : Z.
Variable c3 : Z.
Variable divide : Z -> Z -> Z.
Variable identity : Z.
Variable inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Axiom ax_identity : forall X : Z, identity =? (divide X X).
Axiom ax_inverse : forall X : Z, (inverse X) =? (divide identity X).
Axiom ax_multiply : forall X Y : Z, (multiply X Y) =? (divide X (divide identity Y)).
Axiom ax_single_axiom : forall X Y Z : Z, (divide (divide identity (divide X Y)) (divide (divide Y Z) X)) =? Z.

Add_lemmas ax_identity ax_inverse ax_multiply ax_single_axiom.

(* Goal *)
Theorem check : (multiply (inverse a1) a1) =? (multiply (inverse b1) b1).
Proof.
  smt.
Qed.

Check check.

