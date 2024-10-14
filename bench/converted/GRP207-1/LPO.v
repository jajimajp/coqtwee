(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Parameter u : G.
Parameter x : G.
Parameter y : G.
Parameter z : G.
(* HACK: for coq-completion *)
Hint Resolve u : hint_hack_compl.
Axiom ax_single_non_axiom : forall U Y Z : G, (multiply U (inverse (multiply Y (multiply (multiply (multiply Z (inverse Z)) (inverse (multiply U Y))) U)))) = U.

Complete ax_single_non_axiom : inverse multiply u x y z : hint
  for ((multiply x (inverse (multiply y (multiply (multiply (multiply z (inverse z)) (inverse (multiply u y))) x)))) = u).

(* Goal *)
Theorem check : (multiply x (inverse (multiply y (multiply (multiply (multiply z (inverse z)) (inverse (multiply u y))) x)))) = u.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

