(* Generated by tptp2coqp *)
Require Import Setoid.
From CoqTwee Require Import Twee.

(* axioms *)
Parameter G : Set.
Parameter a3 : G.
Parameter b3 : G.
Parameter c3 : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_single_axiom : forall A B C D : G, (multiply A (inverse (multiply (multiply (inverse (multiply (inverse B) (multiply (inverse A) C))) D) (inverse (multiply B D))))) = C.


(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3)).
Proof.
  twee ax_single_axiom.
Qed.

Check check.

