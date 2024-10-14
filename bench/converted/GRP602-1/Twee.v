(* Generated by tptp2coqp *)
Require Import Setoid.
From CoqTwee Require Import Twee.

(* axioms *)
Parameter G : Set.
Parameter a2 : G.
Parameter b2 : G.
Parameter double_divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_multiply : forall A B : G, (multiply A B) = (inverse (double_divide B A)).
Axiom ax_single_axiom : forall A B C : G, (inverse (double_divide (inverse (double_divide A (inverse (double_divide B (double_divide A C))))) C)) = B.


(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  twee ax_multiply ax_single_axiom.
Qed.

Check check.

