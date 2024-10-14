(* Generated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable b : Z.
Variable c : Z.
Variable d : Z.
Variable h : Z.
Variable identity : Z.
Variable ifeq : Z -> Z -> Z -> Z -> Z.
Variable ifeq2 : Z -> Z -> Z -> Z -> Z.
Variable inverse : Z -> Z.
Variable j : Z.
Variable k : Z.
Variable multiply : Z -> Z -> Z.
Variable product : Z -> Z -> Z -> Z.
Variable true : Z.
Axiom ax_j_times_inverse_h_is_k : (product j (inverse h) k) =? true.
Axiom ax_h_times_b_is_j : (product h b j) =? true.
Axiom ax_d_times_inverse_b_is_h : (product d (inverse b) h) =? true.
Axiom ax_c_times_inverse_a_is_d : (product c (inverse a) d) =? true.
Axiom ax_a_times_b_is_c : (product a b c) =? true.
Axiom ax_x_cubed_is_identity_2 : forall X Y : Z, (ifeq (product X X Y) true (product Y X identity) true) =? true.
Axiom ax_x_cubed_is_identity_1 : forall X Y : Z, (ifeq (product X X Y) true (product X Y identity) true) =? true.
Axiom ax_associativity2 : forall U V W X Y Z : Z, (ifeq (product Y Z V) true (ifeq (product X V W) true (ifeq (product X Y U) true (product U Z W) true) true) true) =? true.
Axiom ax_associativity1 : forall U V W X Y Z : Z, (ifeq (product U Z W) true (ifeq (product Y Z V) true (ifeq (product X Y U) true (product X V W) true) true) true) =? true.
Axiom ax_total_function2 : forall W X Y Z : Z, (ifeq2 (product X Y W) true (ifeq2 (product X Y Z) true Z W) W) =? W.
Axiom ax_total_function1 : forall X Y : Z, (product X Y (multiply X Y)) =? true.
Axiom ax_right_inverse : forall X : Z, (product X (inverse X) identity) =? true.
Axiom ax_left_inverse : forall X : Z, (product (inverse X) X identity) =? true.
Axiom ax_right_identity : forall X : Z, (product X identity X) =? true.
Axiom ax_left_identity : forall X : Z, (product identity X X) =? true.
Axiom ax_ifeq_axiom_001 : forall A B C : Z, (ifeq A A B C) =? B.
Axiom ax_ifeq_axiom : forall A B C : Z, (ifeq2 A A B C) =? B.

Add_lemmas ax_j_times_inverse_h_is_k ax_h_times_b_is_j ax_d_times_inverse_b_is_h ax_c_times_inverse_a_is_d ax_a_times_b_is_c ax_x_cubed_is_identity_2 ax_x_cubed_is_identity_1 ax_associativity2 ax_associativity1 ax_total_function2 ax_total_function1 ax_right_inverse ax_left_inverse ax_right_identity ax_left_identity ax_ifeq_axiom_001 ax_ifeq_axiom.

(* Goal *)
Theorem check : (product k (inverse b) identity) =? true.
Proof.
  smt.
Qed.

Check check.

