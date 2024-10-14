(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter divide : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
(* HACK: for coq-completion *)
Hint Resolve a : hint_hack_compl.
Axiom ax_identity : forall A : G, identity = (divide A A).
Axiom ax_inverse : forall A : G, (inverse A) = (divide identity A).
Axiom ax_multiply : forall A B : G, (multiply A B) = (divide A (divide identity B)).
Axiom ax_single_axiom : forall A B C : G, (divide (divide identity (divide (divide (divide A B) C) A)) C) = B.

Complete ax_identity ax_inverse ax_multiply ax_single_axiom : a b divide identity inverse multiply : hint
  for ((multiply a b) = (multiply b a)).

(* Goal *)
Theorem check : (multiply a b) = (multiply b a).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

