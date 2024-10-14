(* Generated by tptp2coqp *)
Require Import Setoid.
From CoqTwee Require Import Twee.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter i : G -> G.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Axiom ax_f11 : forall A B : G, (mult A B) = (mult B A).
Axiom ax_f10 : forall A : G, (mult (i A) A) = unit.
Axiom ax_f09 : forall A : G, (mult A (i A)) = unit.
Axiom ax_f08 : forall A B : G, (mult (mult A B) (i B)) = A.
Axiom ax_f07 : forall A B C : G, (mult (mult (mult A B) C) B) = (mult A (mult (mult B C) B)).
Axiom ax_f06 : forall A : G, (mult unit A) = A.
Axiom ax_f05 : forall A : G, (mult A unit) = A.
Axiom ax_f04 : forall A B : G, (rd (mult A B) B) = A.
Axiom ax_f03 : forall A B : G, (mult (rd A B) B) = A.
Axiom ax_f02 : forall A B : G, (ld A (mult A B)) = B.
Axiom ax_f01 : forall A B : G, (mult A (ld A B)) = B.


(* Goal *)
Theorem check : (mult (mult a b) (mult c a)) = (mult a (mult (mult b c) a)).
Proof.
  twee ax_f11 ax_f10 ax_f09 ax_f08 ax_f07 ax_f06 ax_f05 ax_f04 ax_f03 ax_f02 ax_f01.
Qed.

Check check.

