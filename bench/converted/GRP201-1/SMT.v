(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable b : Z.
Variable c : Z.
Variable identity : Z.
Variable left_division : Z -> Z -> Z.
Variable left_inverse : Z -> Z.
Variable multiply : Z -> Z -> Z.
Variable right_division : Z -> Z -> Z.
Variable right_inverse : Z -> Z.
Axiom ax_moufang2 : forall X Y Z : Z, (multiply (multiply (multiply X Y) Z) Y) =? (multiply X (multiply Y (multiply Z Y))).
Axiom ax_left_inverse : forall X : Z, (multiply (left_inverse X) X) =? identity.
Axiom ax_right_inverse : forall X : Z, (multiply X (right_inverse X)) =? identity.
Axiom ax_right_division_multiply : forall X Y : Z, (right_division (multiply X Y) Y) =? X.
Axiom ax_multiply_right_division : forall X Y : Z, (multiply (right_division X Y) Y) =? X.
Axiom ax_left_division_multiply : forall X Y : Z, (left_division X (multiply X Y)) =? Y.
Axiom ax_multiply_left_division : forall X Y : Z, (multiply X (left_division X Y)) =? Y.
Axiom ax_right_identity : forall X : Z, (multiply X identity) =? X.
Axiom ax_left_identity : forall X : Z, (multiply identity X) =? X.

Add_lemmas ax_moufang2 ax_left_inverse ax_right_inverse ax_right_division_multiply ax_multiply_right_division ax_left_division_multiply ax_multiply_left_division ax_right_identity ax_left_identity.

(* Goal *)
Theorem check : (multiply (multiply (multiply a b) a) c) =? (multiply a (multiply b (multiply a c))).
Proof.
  smt.
Qed.

Check check.

