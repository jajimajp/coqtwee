(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter f : G -> G.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter unit : G.
Axiom ax_c09 : forall A : G, (mult (f A) (f A)) = A.
Axiom ax_c08 : forall A B : G, (mult (mult A B) A) = (mult A (mult B A)).
Axiom ax_c07 : forall A B C : G, (mult (mult A B) (mult (mult C B) C)) = (mult (mult A (mult (mult B C) B)) C).
Axiom ax_c06 : forall A : G, (mult unit A) = A.
Axiom ax_c05 : forall A : G, (mult A unit) = A.
Axiom ax_c04 : forall A B : G, (rd (mult A B) B) = A.
Axiom ax_c03 : forall A B : G, (mult (rd A B) B) = A.
Axiom ax_c02 : forall A B : G, (ld A (mult A B)) = B.
Axiom ax_c01 : forall A B : G, (mult A (ld A B)) = B.


(* Goal *)
Theorem check : (mult a (mult b (mult a c))) = (mult (mult (mult a b) a) c).
Proof.
  hammer.
Qed.

Check check.

