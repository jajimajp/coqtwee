Require Import Setoid.
Declare ML Module "coqtwee.plugin".


(* axioms *)
Parameter G : Set.
Parameter add : G -> G -> G.
Parameter mult : G -> G -> G.
Parameter s : G -> G.
Parameter z : G.
Axiom mult_s : forall X Y : G, (mult (s X) Y) = (add (mult X Y) Y).
Axiom mult_z : forall Y : G, (mult z Y) = z.
Axiom add_s : forall X Y : G, (add (s X) Y) = (s (add X Y)).
Axiom add_z : forall Y : G, (add z Y) = Y.


(* Goal *)
Theorem check : (mult (s (s (s (s z)))) (s (s (s (s z))))) = (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s z)))))))))))))))).
Proof.
  twee mult_s mult_z add_s add_z.
Qed.

Check check.

