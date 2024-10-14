(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter c : G -> G -> G.
Parameter m : G -> G -> G.
Parameter x : G.
Parameter y : G.
Parameter z : G.
(* HACK: for coq-completion *)
Hint Resolve x : hint_hack_compl.
Axiom ax_assumption : forall X Y Z : G, (m X (m Y (m Z (m Y X)))) = (m Y (m X (m Z (m X Y)))).
Axiom ax_commutator : forall X Y : G, (m Y (m X (c X Y))) = (m X Y).
Axiom ax_cancellation_001 : forall X Y Z : G, (m Z X) = (m Z Y).
Axiom ax_cancellation : forall X Y Z : G, (m X Z) = (m Y Z).
Axiom ax_associativity : forall X Y Z : G, (m X (m Y Z)) = (m (m X Y) Z).

Complete ax_assumption ax_commutator ax_cancellation_001 ax_cancellation ax_associativity : c m x y z : hint
  for ((c (m x y) z) = (m (c x z) (c y z))).

(* Goal *)
Theorem check : (c (m x y) z) = (m (c x z) (c y z)).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

