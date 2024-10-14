(* Generated by tptp2coqp *)
Require Import Setoid.
From CoqTwee Require Import Twee.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter double_divide : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_identity : forall A : G, identity = (double_divide A (inverse A)).
Axiom ax_inverse : forall A : G, (inverse A) = (double_divide A identity).
Axiom ax_multiply : forall A B : G, (multiply A B) = (double_divide (double_divide B A) identity).
Axiom ax_single_axiom : forall A B C : G, (double_divide (double_divide A (double_divide (double_divide (double_divide A B) C) (double_divide B identity))) (double_divide identity identity)) = C.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = identity.
Proof.
  twee ax_identity ax_inverse ax_multiply ax_single_axiom.
Qed.

Check check.

