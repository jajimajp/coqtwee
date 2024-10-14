(* Generated by tptp2coqp *)
Require Import Setoid.
From CoqTwee Require Import Twee.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter double_divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_multiply : forall A B : G, (multiply A B) = (inverse (double_divide B A)).
Axiom ax_single_axiom : forall A B C : G, (double_divide A (inverse (double_divide (inverse (double_divide (double_divide A B) (inverse C))) B))) = C.


(* Goal *)
Theorem check : (multiply a b) = (multiply b a).
Proof.
  twee ax_multiply ax_single_axiom.
Qed.

Check check.

