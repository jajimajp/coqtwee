(* Generated by tptp2coqp *)
Require Import Setoid.
From CoqTwee Require Import Twee.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter d : G.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Axiom ax_c08 : forall A B C : G, (mult (mult A B) (ld B (mult C B))) = (mult (mult A C) B).
Axiom ax_c07 : forall A B C : G, (mult (rd (mult A B) A) (mult A C)) = (mult A (mult B C)).
Axiom ax_c06 : forall A B : G, (mult (rd A B) B) = A.
Axiom ax_c05 : forall A B : G, (rd (mult A B) B) = A.
Axiom ax_c04 : forall A B : G, (ld A (mult A B)) = B.
Axiom ax_c03 : forall A B : G, (mult A (ld A B)) = B.
Axiom ax_c02 : forall A : G, (mult A unit) = A.
Axiom ax_c01 : forall A : G, (mult unit A) = A.


(* Goal *)
Theorem check : (mult a (mult b (ld (mult c d) (mult d c)))) = (mult (mult a b) (ld (mult c d) (mult d c))).
Proof.
  twee ax_c08 ax_c07 ax_c06 ax_c05 ax_c04 ax_c03 ax_c02 ax_c01.
Qed.

Check check.

