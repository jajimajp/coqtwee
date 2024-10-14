(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter a2 : G.
Parameter a3 : G.
Parameter a4 : G.
Parameter b1 : G.
Parameter b2 : G.
Parameter b3 : G.
Parameter b4 : G.
Parameter c3 : G.
Parameter double_divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
(* HACK: for coq-completion *)
Hint Resolve a1 : hint_hack_compl.
Axiom ax_multiply : forall X Y : G, (multiply X Y) = (inverse (double_divide Y X)).
Axiom ax_single_axiom : forall X Y Z : G, (double_divide (inverse (double_divide (double_divide X Y) (inverse (double_divide X (inverse Z))))) Y) = Z.

Complete ax_multiply ax_single_axiom : a1 a2 a3 a4 b1 b2 b3 b4 c3 double_divide inverse multiply : hint
  for ((multiply (inverse a1) a1) = (multiply (inverse b1) b1)).

(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

