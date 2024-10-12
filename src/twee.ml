(** Wrapper for twee *)

open Unix

let twee_version = "2.4.2"

(** Check if twee is installed and it's version is acceptable.
    Prints error in stderr if there is any problems, otherwise does nothing. *)
let doctor () =
  let print_errmsg () =
      prerr_endline
        ("Please install twee " ^ twee_version ^
            " and make it accessible from the PATH envirnment variable.") in
  try
    (* twee outputs version in stderr *)
    let (in_channel, out_channel, err_in_channel) =
      open_process_args_full "twee" [|"twee"; "--version"|] [||] in
    let () = close_in in_channel in (* We do not use stdout of twee *)
    let () = close_out out_channel in (* We do not use input for twee *)
    let output = input_line err_in_channel in
    if output = ("twee version " ^ twee_version) then
      ()
    else
      print_errmsg ()
  with
  | End_of_file ->
      print_errmsg ()


(** Subset of TPTP *)
module Tptp = struct
  type t = clause list
  and clause = string * clause_type * clause_term
  and clause_type = Axiom | Conjecture
  and clause_term = Eq of eq | With_univ of eq with_univ_qunr
  and eq = term * term
  and term = T of string * term list
  (* variables will be ("V", []) *)

  and 'a with_univ_qunr = string list * 'a
  (** Universal quantifiers *)


  let rec to_string t =
    List.map string_of_clause t
    |> String.concat "\n" 

  and string_of_clause clause =
    let (name, clause_type, clause_term) = clause in
    Printf.sprintf "fof(%s, %s, %s)."
        name
        (match clause_type with Axiom -> "axiom" | Conjecture -> "conjecture")
        (string_of_clause_term clause_term)

  and string_of_clause_term = function
    | Eq eq -> string_of_eq eq
    | With_univ (univs, eq) ->
        Printf.sprintf "![%s]: %s" (String.concat "," univs) (string_of_eq eq)

  and string_of_eq (l, r) = string_of_term l ^ " = " ^ string_of_term r

  and string_of_term = function
    | T (name, []) -> name
    | T (name, terms) ->
        let terms = List.map string_of_term terms |> String.concat ", " in
        name ^ "(" ^ terms ^ ")"
end


let twee (input : string) : string list =
  let (in_channel, out_channel, err_in_channel) =
    open_process_args_full "twee" [|"twee"; "-"; "--quiet"; "--no-colour"|] [||] in
  output_string out_channel input;
  close_out out_channel;
  close_in err_in_channel;
  let lines = ref [] in
  begin try
    while true do
      lines := (input_line in_channel) :: !lines
    done
  with
  | End_of_file -> ()
  end;
  List.rev !lines


(* tests *)
let () = doctor ()

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

let () =
  let content = Tptp.to_string example in
  print_endline content;
  print_newline ();
  let lines = twee content in
  (* let print_endline _ = () in *)
  List.iter print_endline lines
