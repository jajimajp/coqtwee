(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter ld : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter rd : G -> G -> G.
Parameter x3 : G.
Parameter x4 : G.
Parameter x5 : G.
(* HACK: for coq-completion *)
Hint Resolve x3 : hint_hack_compl.
Axiom ax_f07 : forall A B : G, (ld A (mult A (ld B B))) = (rd (mult (rd A A) B) B).
Axiom ax_f06 : forall A B C D : G, (rd (mult (mult A B) (rd C D)) (rd C D)) = (mult A (rd (mult B D) D)).
Axiom ax_f05 : forall A B C D : G, (ld (ld A B) (mult (ld A B) (mult C D))) = (mult (ld A (mult A C)) D).
Axiom ax_f04 : forall A B : G, (mult (rd A B) B) = (rd (mult A B) B).
Axiom ax_f03 : forall A B : G, (mult A (ld A B)) = (ld A (mult A B)).
Axiom ax_f02 : forall A : G, (rd (mult A A) A) = A.
Axiom ax_f01 : forall A : G, (ld A (mult A A)) = A.

Complete ax_f07 ax_f06 ax_f05 ax_f04 ax_f03 ax_f02 ax_f01 : ld mult rd x3 x4 x5 : hint
  for ((mult x3 (ld x4 (mult x4 x5))) = (mult x3 x5)).

(* Goal *)
Theorem check : (mult x3 (ld x4 (mult x4 x5))) = (mult x3 x5).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

