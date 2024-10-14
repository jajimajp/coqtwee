(* Generated by tptp2coqp *)
Require Import Setoid.
From CoqTwee Require Import Twee.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter a2 : G.
Parameter a3 : G.
Parameter b1 : G.
Parameter b2 : G.
Parameter b3 : G.
Parameter c3 : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_single_axiom : forall U X Y Z : G, (multiply X (inverse (multiply Y (multiply (multiply (multiply Z (inverse Z)) (inverse (multiply U Y))) X)))) = U.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  twee ax_single_axiom.
Qed.

Check check.

