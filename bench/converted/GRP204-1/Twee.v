(* Generated by tptp2coqp *)
Require Import Setoid.
From CoqTwee Require Import Twee.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter identity : G.
Parameter left_inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_moufang1 : forall X Y Z : G, (multiply (multiply X (multiply Y Z)) X) = (multiply (multiply X Y) (multiply Z X)).
Axiom ax_left_inverse : forall X : G, (multiply (left_inverse X) X) = identity.
Axiom ax_left_identity : forall X : G, (multiply identity X) = X.


(* Goal *)
Theorem check : (multiply (multiply (multiply a b) c) b) = (multiply a (multiply b (multiply c b))).
Proof.
  twee ax_moufang1 ax_left_inverse ax_left_identity.
Qed.

Check check.

