(* Generated by tptp2coqp *)
Require Import Setoid.
From CoqTwee Require Import Twee.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter divide : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_identity : forall A : G, identity = (divide A A).
Axiom ax_inverse : forall A B : G, (inverse A) = (divide (divide B B) A).
Axiom ax_multiply : forall A B C : G, (multiply A B) = (divide A (divide (divide C C) B)).
Axiom ax_single_axiom : forall A B C : G, (divide (divide A B) (divide (divide A C) B)) = C.


(* Goal *)
Theorem check : (multiply a b) = (multiply b a).
Proof.
  twee ax_identity ax_inverse ax_multiply ax_single_axiom.
Qed.

Check check.

