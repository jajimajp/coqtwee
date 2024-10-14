(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter a : G.
Parameter b : G.
Parameter c : G.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
(* HACK: for coq-completion *)
Hint Resolve a : hint_hack_compl.
Axiom ax_c07 : forall A B : G, (ld A (mult A (ld B B))) = (rd (mult (rd A A) B) B).
Axiom ax_c06 : forall A B C D : G, (rd (mult (mult A B) (rd C D)) (rd C D)) = (mult A (rd (mult B D) D)).
Axiom ax_c05 : forall A B C D : G, (ld (ld A B) (mult (ld A B) (mult C D))) = (mult (ld A (mult A C)) D).
Axiom ax_c04 : forall A B : G, (mult (rd A B) B) = (rd (mult A B) B).
Axiom ax_c03 : forall A B : G, (mult A (ld A B)) = (ld A (mult A B)).
Axiom ax_c02 : forall A : G, (rd (mult A A) A) = A.
Axiom ax_c01 : forall A : G, (ld A (mult A A)) = A.

Complete ax_c07 ax_c06 ax_c05 ax_c04 ax_c03 ax_c02 ax_c01 : a b c ld mult rd : hint
  for ((rd (mult a (mult b c)) (mult b c)) = (rd (mult a c) c)).

(* Goal *)
Theorem check : (rd (mult a (mult b c)) (mult b c)) = (rd (mult a c) c).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

