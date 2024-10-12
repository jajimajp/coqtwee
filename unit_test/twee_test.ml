open Coqtwee.Twee

let%expect_test "parse_axiom" =
  (match parse_axiom "Axiom 1 (right_identity): f(X, e) = f(X,f(Y,Z))." with
  | Ok (Axiom (id, name, eq)) ->
    Printf.printf "Axiom %d (%s): %s = %s\n" id name (string_of_term (fst eq)) (string_of_term (snd eq))
  | Ok _ -> assert false
  | Error msg -> prerr_endline msg
  );
  [%expect {| Axiom 1 (right_identity): f<X, e> = f<X, f<Y, Z>> |}]

let goal =
  {|Goal 1 (left_inverse): f(i(x), x) = e.
Proof:
  f(i(x), x)
= { by axiom 1 (right_identity) R->L }
  f(f(i(x), x), e)
= { by axiom 2 (right_inverse) R->L }
  f(f(i(x), x), f(i(x), i(i(x))))
= { by axiom 3 (associativity) R->L }
  f(i(x), f(x, f(i(x), i(i(x)))))
= { by axiom 3 (associativity) }
  f(i(x), f(f(x, i(x)), i(i(x))))
= { by axiom 2 (right_inverse) }
  f(i(x), f(e, i(i(x))))
= { by axiom 3 (associativity) }
  f(f(i(x), e), i(i(x)))
= { by axiom 1 (right_identity) }
  f(i(x), i(i(x)))
= { by axiom 2 (right_inverse) }
  e

|}

let%expect_test "parse_goal" =
  let string_of_tactic = function
    | ByAxiom (id, rule, l2r) -> Printf.sprintf "axiom %d (%s) %s" id rule 
      (if l2r then "->" else "<-") in
  (match parse_goal (String.split_on_char '\n' goal) with
  | Ok (Goal (id, name, eq, (fst_term, rewrites)), lines) ->
    Printf.printf "Goal %d (%s): %s = %s.\n" id name (string_of_term (fst eq)) (string_of_term (snd eq));
    Printf.printf "Proof:\n";
    Printf.printf "  %s\n" (string_of_term fst_term);
    List.iter (fun (term, tactic) ->
      Printf.printf "= { by %s }\n" (string_of_tactic tactic);
      Printf.printf "  %s\n" (string_of_term term)
    ) rewrites
  | Ok _ -> assert false
  | Error msg -> prerr_endline msg
  );
  [%expect {|
    Goal 1 (left_inverse): f<i<x>, x> = e.
    Proof:
      f<i<x>, x>
    = { by axiom 1 (right_identity) <- }
      f<f<i<x>, x>, e>
    = { by axiom 2 (right_inverse) <- }
      f<f<i<x>, x>, f<i<x>, i<i<x>>>>
    = { by axiom 3 (associativity) <- }
      f<i<x>, f<x, f<i<x>, i<i<x>>>>>
    = { by axiom 3 (associativity) -> }
      f<i<x>, f<f<x, i<x>>, i<i<x>>>>
    = { by axiom 2 (right_inverse) -> }
      f<i<x>, f<e, i<i<x>>>>
    = { by axiom 3 (associativity) -> }
      f<f<i<x>, e>, i<i<x>>>
    = { by axiom 1 (right_identity) -> }
      f<i<x>, i<i<x>>>
    = { by axiom 2 (right_inverse) -> }
      e |}]

let example : Tptp.t =
  let open Tptp in
  let const name = T (name, []) in
  let app name args = T (name, args) in
  let e = const "e" in
  let x, y, z = const "X", const "Y", const "Z" in
  let i v = app "i" [v] in
  let f l r = app "f" [l; r] in
  let (=) l r = (l, r) in
  [ ("right_identity", Axiom,
      With_univ (["X"], (f x e) = x))
  ; ("right_inverse", Axiom,
      With_univ (["X"], (f x (i x)) = e))
  ; ("associativity", Axiom,
      With_univ (["X"; "Y"; "Z"], (f x (f y z)) = (f (f x y) z)))
  ; ("left_inverse", Conjecture,
      With_univ (["X"], (f (i x) x) = e))
  ]

let%expect_test "Tptp.to_string" =
  let content = Tptp.to_string example in
  print_endline content;
  [%expect {|
    fof(right_identity, axiom, ![X]: f(X, e) = X).
    fof(right_inverse, axiom, ![X]: f(X, i(X)) = e).
    fof(associativity, axiom, ![X,Y,Z]: f(X, f(Y, Z)) = f(f(X, Y), Z)).
    fof(left_inverse, conjecture, ![X]: f(i(X), X) = e).|}]

let%expect_test "twee" =
  let content = Tptp.to_string example in
  let lines = twee content in
  List.iter print_endline lines;
  [%expect {|
    The conjecture is true! Here is a proof.

    Axiom 1 (right_identity): f(X, e) = X.
    Axiom 2 (right_inverse): f(X, i(X)) = e.
    Axiom 3 (associativity): f(X, f(Y, Z)) = f(f(X, Y), Z).

    Goal 1 (left_inverse): f(i(x), x) = e.
    Proof:
      f(i(x), x)
    = { by axiom 1 (right_identity) R->L }
      f(f(i(x), x), e)
    = { by axiom 2 (right_inverse) R->L }
      f(f(i(x), x), f(i(x), i(i(x))))
    = { by axiom 3 (associativity) R->L }
      f(i(x), f(x, f(i(x), i(i(x)))))
    = { by axiom 3 (associativity) }
      f(i(x), f(f(x, i(x)), i(i(x))))
    = { by axiom 2 (right_inverse) }
      f(i(x), f(e, i(i(x))))
    = { by axiom 3 (associativity) }
      f(f(i(x), e), i(i(x)))
    = { by axiom 1 (right_identity) }
      f(i(x), i(i(x)))
    = { by axiom 2 (right_inverse) }
      e

    RESULT: Theorem (the conjecture is true). |}]