(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a2 : G.
Parameter b2 : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
(* HACK: for coq-completion *)
Hint Resolve a2 : hint_hack_compl.
Axiom ax_single_axiom : forall A B C : G, (inverse (multiply (inverse (multiply A (inverse (multiply (inverse B) (multiply (inverse C) (inverse (multiply (inverse C) C))))))) (multiply A C))) = B.

Complete ax_single_axiom : a2 b2 inverse multiply : hint
  for ((multiply (multiply (inverse b2) b2) a2) = a2).

(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

