(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter a2 : G.
Parameter double_divide : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_identity : forall A : G, identity = (double_divide A (inverse A)).
Axiom ax_inverse : forall A : G, (inverse A) = (double_divide A identity).
Axiom ax_multiply : forall A B : G, (multiply A B) = (double_divide (double_divide B A) identity).
Axiom ax_single_axiom : forall A B C : G, (double_divide (double_divide A (double_divide (double_divide (double_divide B A) C) (double_divide B identity))) (double_divide identity identity)) = C.


(* Goal *)
Theorem check : (multiply identity a2) = a2.
Proof.
  hammer.
Qed.

Check check.

