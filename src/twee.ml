open Unix

let twee_version = "2.4.2"
(** twee version which our plugin use. *)

let doctor () : (unit, string) result  =
  let err =
    Error ("Please install twee " ^ twee_version ^
            " and make it accessible from the PATH envirnment variable." ^
            "See https://nick8325.github.io/twee/") in
  try
    (* twee outputs version in stderr *)
    let (in_channel, out_channel, err_in_channel) =
      open_process_args_full "twee" [|"twee"; "--version"|] [||] in
    let () = close_in in_channel in (* We do not use stdout of twee *)
    let () = close_out out_channel in (* We do not use input for twee *)
    let output = input_line err_in_channel in
    if output = ("twee version " ^ twee_version) then
      Ok ()
    else
      err
  with
  | End_of_file ->
      err


(** Subset of TPTP *)
module Tptp = struct
  type t = clause list
  and clause = string * clause_type * clause_term
  and clause_type = Axiom | Conjecture
  and clause_term = Eq of eq | With_univ of eq with_univ_qunr
  and eq = term * term
  and term = T of string * term list
  and 'a with_univ_qunr = string list * 'a

  let rec sanitize t =
    let clauses, mapping = List.fold_left (fun (sanitized_cls, mapping) clause ->
      let clause, mapping = sanitize_clause mapping clause in
      ((clause :: sanitized_cls, mapping))) ([], []) t in
    (List.rev clauses, mapping)

  and sanitize_clause mapping (name, clause_type, clause_term) =
    let name, mapping = sanitize_name mapping name in
    let clause_term, mapping = match clause_term with
      | Eq eq ->
        let eq, mapping = sanitize_eq mapping eq in
          Eq eq, mapping
      | With_univ (univs, eq) ->
          let eq, mapping = sanitize_eq mapping eq in
          With_univ (univs, eq), mapping in
    (name, clause_type, clause_term), mapping

  and sanitize_eq mapping (l, r) =
    let l, mapping = sanitize_term mapping l in
    let r, mapping = sanitize_term mapping r in
    (l, r), mapping

  and sanitize_term mapping = function
    | T (name, []) ->
      let name, mapping = sanitize_name mapping name in
      T (name, []), mapping
    | T (name, terms) ->
      let name, mapping = sanitize_name mapping name in
      let terms, mapping = List.fold_left (fun (terms, mapping) term ->
        let term, mapping = sanitize_term mapping term in
        (term :: terms, mapping)) ([], mapping) terms in
      T (name, List.rev terms), mapping

  and sanitize_name mapping name =
    try
      let v = List.assoc name mapping in
      (v, mapping)
    with Not_found ->
      begin
        try
          let _idx = String.index name '.' in
          let last = String.split_on_char '.' name |> List.rev |> List.hd in
          let mapping = (name, last) :: mapping in
          (last, mapping)
        with Not_found -> (name, mapping)
      end
    

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


type output = entry list

and entry =
  | Axiom of id * string * eq
  | Lemma of id * eq * proof
  | Goal of id * string * eq * proof

and id = int

and eq = term * term

and term =
  | Var of string
  | App of string * term list

and proof = term * rewrite list
(** Proof. (start_term, rewrite list) *)

and rewrite = term * tactic
(** Rewrite step. (next_term, to) *)

and tactic =
  | ByAxiom of id * string * bool (* (id, name, left_to_right?) *)


let rec string_of_output (output : output) : string =
  List.map string_of_entry output |> String.concat "\n"

and string_of_entry = function
  | Axiom (id, name, eq) ->
    Printf.sprintf "Axiom %d (%s): %s = %s" id name (string_of_term (fst eq)) (string_of_term (snd eq))
  | Lemma (id, eq, proof) ->
    Printf.sprintf "Lemma %d: %s = %s\n%s" id (string_of_term (fst eq)) (string_of_term (snd eq)) (string_of_proof proof)
  | Goal (id, name, eq, proof) ->
    Printf.sprintf "Goal %d (%s): %s = %s\n%s" id name (string_of_term (fst eq)) (string_of_term (snd eq)) (string_of_proof proof)

and string_of_id = string_of_int

and string_of_eq (l, r) = string_of_term l ^ " = " ^ string_of_term r

and string_of_term = function
  | Var v -> v
  | App (f, args) ->
    f ^ "<" ^ (List.map string_of_term args |> String.concat ", ") ^ ">"

and string_of_proof (start_term, rewrites) =
  string_of_term start_term ^ "\n" ^ (List.map string_of_rewrite rewrites |> String.concat "\n")

and string_of_rewrite (next_term, tactic) =
  "= { by " ^ string_of_tactic tactic ^ " } " ^ string_of_term next_term

and string_of_tactic = function
  | ByAxiom (id, name, l2r) ->
    Printf.sprintf "axiom %d (%s)%s" id name (if l2r then "" else " R->L")


exception Parse_proof_error of string


let rec parse_output (lines : string list) : (output, string) result =
  match lines with [] -> Error "Empty output from twee."
  | fst :: lines ->
  
  if fst <> "The conjecture is true! Here is a proof." then
    Error ("Proof failed: " ^ fst)
  else
  
  let rec parse_entries (acc : entry list) (lines : string list) : (entry list, string) result =
    match lines with
    | [] -> Error "Unexpected end of entry"
    | fst :: lines ->
      let fst_word = String.split_on_char ' ' fst |> List.hd in
      match fst_word with
      | "" -> parse_entries acc lines
      | "RESULT:" -> Ok (List.rev acc)
      | "Axiom" -> ((* Assume this entry needs only one line *)
        match parse_axiom fst with
        | Ok entry -> parse_entries (entry :: acc) lines
        | Error msg -> Error msg
      )
      | "Goal" -> (
        match parse_goal (fst :: lines) with
        | Ok (entry, lines) -> parse_entries (entry :: acc) lines
        | Error msg -> Error msg
      )
      | _ -> Error ("Unexpected entry: " ^ fst) in
  
  parse_entries [] lines
    
(* Example: "Axiom 1 (right_identity): f(X, e) = X." *)
and parse_axiom (line : string) : (entry, string) result =
  let regexp = Str.regexp "Axiom \\([0-9]+\\) (\\([^:]+\\)): \\([^.]*\\)\\." in
  if not (Str.string_match regexp line 0) then
    Error ("Invalid axiom: " ^ line)
  else
  let id = Str.matched_group 1 line |> int_of_string in
  let name = Str.matched_group 2 line in
  let eq = Str.matched_group 3 line |> parse_eq in
  Ok (Axiom (id, name, eq))

and parse_eq (s : string) : eq =
  match String.split_on_char '=' s |> List.map String.trim with
  | [l; r] -> (parse_term l, parse_term r)
  | _ -> raise (Invalid_argument "Invalid equation")

and parse_term (s : string) : term =
  try
    let i = String.index s '(' in
    let f = String.sub s 0 i |> String.trim in
    if f = "" then raise (Invalid_argument "Empty function name") else
    let s = String.sub s (i + 1) (String.length s - i - 1) in
    let args = String.split_on_char ')' s |> List.rev |> List.tl |> List.rev |> String.concat ")" in
    let args = args |> split_args |> List.map parse_term in
    App (f, args)
  with Not_found ->
    Var (String.trim s)

(** split strings by comma only if it is not inside parentheses *)
and split_args (s : string) : string list =
  let rec aux (depth : int) (reading : string) (acc : string list) (s : string) : string list =
    if s = "" then List.rev (reading :: acc) else
    let c = String.get s 0 in
    let s = String.sub s 1 (String.length s - 1) in
    match c with
    | '(' -> aux (depth + 1) (reading ^ "(") acc s
    | ')' -> aux (depth - 1) (reading ^ ")") acc s
    | ',' when depth = 0 -> aux depth "" (reading :: acc) s
    | _ -> aux depth (reading ^ String.make 1 c) acc s in 
  aux 0 "" [] s


(** Example: "Lemma 4: f(i(X), f(X, Y)) = Y." *)
and parse_lemma (lines : string list) : (entry * string list, string) result =
  let line = List.hd lines in
  let regexp = Str.regexp "Lemma \\([0-9]+\\): \\([^.]*\\)\\." in
  if not (Str.string_match regexp line 0) then
    Error ("Invalid lemma: " ^ line)
  else
  let id = Str.matched_group 1 line |> int_of_string in
  let eq = Str.matched_group 2 line |> parse_eq in
  let lines = List.tl lines in
  match parse_proof lines with
  | Ok (proof, lines) -> Ok (Lemma (id, eq, proof), lines)
  | Error msg -> Error msg


(** Example: "Goal 1 (left_inverse): f(i(x), x) = e." *)
and parse_goal (lines : string list) : (entry * string list, string) result =
  let line = List.hd lines in
  let regexp = Str.regexp "Goal \\([0-9]+\\) (\\([^:]+\\)): \\([^.]*\\)\\." in
  if not (Str.string_match regexp line 0) then
    Error ("Invalid goal: " ^ line)
  else
  let id = Str.matched_group 1 line |> int_of_string in
  let name = Str.matched_group 2 line in
  let eq = Str.matched_group 3 line |> parse_eq in
  let lines = List.tl lines in
  match parse_proof lines with
  | Ok (proof, lines) -> Ok (Goal (id, name, eq, proof), lines)
  | Error msg -> Error msg


and parse_proof (lines : string list) : (proof * string list, string) result =
  match lines with [] -> Error "Unexpected end of proof"
  | fst :: lines ->
    if fst <> "Proof:" then Error ("Invalid proof: " ^ fst) else
    let consume_term_line (lines : string list) : term * string list =
      match lines with [] -> raise (Parse_proof_error "Unexpected end of proof")
      | fst :: lines ->
        let term = parse_term fst in
        (term, lines) in
    
    let fst_term, lines = consume_term_line lines in

    let rec aux (acc : rewrite list) (lines : string list) : (rewrite list * string list, string) result =
      match lines with [] -> Error "Unexpected end of proof"
      | fst :: snd :: lines ->
        if fst = "" then Ok (List.rev acc, snd :: lines) else
        let tactic = parse_tactic fst in
        let next_term = parse_term snd in
        aux ((next_term, tactic) :: acc) lines
      | _ -> Error "Unexpected end of proof" in
    
    match aux [] lines with
    | Ok (rewrites, lines) -> Ok ((fst_term, rewrites), lines)
    | Error msg -> Error msg

(* example: "= { by axiom 1 (right_identity) R->L }", "R->L" may be absent *)
and parse_tactic (line : string) : tactic =
  let regexp = Str.regexp "= { by axiom \\([0-9]+\\) (\\([^)]+\\))\\( R->L\\)? }" in
  if not (Str.string_match regexp line 0) then
    raise (Invalid_argument ("Invalid tactic: " ^ line))
  else
  let id = Str.matched_group 1 line |> int_of_string in
  let name = Str.matched_group 2 line in
  let r2l = try ignore (Str.matched_group 3 line); true with Not_found -> false in
  ByAxiom (id, name, not r2l)
  

let twee (input : Tptp.t) : (output, string) result =
  let input = Tptp.to_string input in
  let (in_channel, out_channel, err_in_channel) =
    open_process_args_full "twee" [|"twee"; "-"; "--quiet"; "--no-colour"|] [||] in
  output_string out_channel input;
  close_out out_channel;

  begin try
    while true do
      Feedback.msg_debug Pp.(str "twee stderr" ++ spc() ++ str (input_line err_in_channel))
    done
  with
  | End_of_file -> ()
  end;

  close_in err_in_channel;
  let lines = ref [] in
  begin try
    while true do
      lines := (input_line in_channel) :: !lines
    done
  with
  | End_of_file -> ()
  end;
  let lines = List.rev !lines in
  parse_output lines
