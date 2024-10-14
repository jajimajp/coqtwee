(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter identity : G.
Parameter multiply : G -> G -> G.
Axiom ax_single_axiom2 : (multiply identity identity) = identity.
Axiom ax_single_axiom : forall X Y Z : G, (multiply Y (multiply (multiply Y (multiply (multiply Y Y) (multiply X Z))) (multiply Z (multiply Z Z)))) = X.


(* Goal *)
Theorem check : (multiply identity a) = a.
Proof.
  hammer.
Qed.

Check check.

