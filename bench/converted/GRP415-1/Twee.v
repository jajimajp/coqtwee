(* Generated by tptp2coqp *)
Require Import Setoid.
From CoqTwee Require Import Twee.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter b1 : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_single_axiom : forall A B C : G, (inverse (multiply A (inverse (multiply (inverse (multiply (inverse (multiply B A)) (multiply B (inverse C)))) (inverse (multiply (inverse A) A)))))) = C.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  twee ax_single_axiom.
Qed.

Check check.

