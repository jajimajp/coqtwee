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


type output = entry list

and entry =
  | Axiom of id * string * eq
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
[@@deriving_inline show]

let _ = fun (_ : output) -> ()
let _ = fun (_ : entry) -> ()
let _ = fun (_ : id) -> ()
let _ = fun (_ : eq) -> ()
let _ = fun (_ : term) -> ()
let _ = fun (_ : proof) -> ()
let _ = fun (_ : rewrite) -> ()
let _ = fun (_ : tactic) -> ()
let rec pp_output
  : Ppx_deriving_runtime.Format.formatter ->
      output -> Ppx_deriving_runtime.unit
  =
  ((let __0 = pp_entry in
    ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
        fun fmt ->
          fun x ->
            Ppx_deriving_runtime.Format.fprintf fmt "@[<2>[";
            ignore
              (List.fold_left
                 (fun sep ->
                    fun x ->
                      if sep
                      then Ppx_deriving_runtime.Format.fprintf fmt ";@ ";
                      (__0 fmt) x;
                      true) false x);
            Ppx_deriving_runtime.Format.fprintf fmt "@,]@]")
      [@ocaml.warning "-A"]))
  [@ocaml.warning "-39"])
and show_output : output -> Ppx_deriving_runtime.string =
  fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_output x[@@ocaml.warning
                                                                  "-32"]
and pp_entry
  : Ppx_deriving_runtime.Format.formatter ->
      entry -> Ppx_deriving_runtime.unit
  =
  ((let __4 = pp_proof
    and __3 = pp_eq
    and __2 = pp_id
    and __1 = pp_eq
    and __0 = pp_id in
    ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
        fun fmt ->
          function
          | Axiom (a0, a1, a2) ->
              (Ppx_deriving_runtime.Format.fprintf fmt "(@[<2>Twee.Axiom (@,";
               (((__0 fmt) a0;
                 Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%S") a1);
                Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                (__1 fmt) a2);
               Ppx_deriving_runtime.Format.fprintf fmt "@,))@]")
          | Goal (a0, a1, a2, a3) ->
              (Ppx_deriving_runtime.Format.fprintf fmt "(@[<2>Twee.Goal (@,";
               ((((__2 fmt) a0;
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (Ppx_deriving_runtime.Format.fprintf fmt "%S") a1);
                 Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                 (__3 fmt) a2);
                Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                (__4 fmt) a3);
               Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
      [@ocaml.warning "-A"]))
  [@ocaml.warning "-39"])
and show_entry : entry -> Ppx_deriving_runtime.string =
  fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_entry x[@@ocaml.warning
                                                                 "-32"]
and pp_id
  : Ppx_deriving_runtime.Format.formatter -> id -> Ppx_deriving_runtime.unit
  =
  ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
      fun fmt -> Ppx_deriving_runtime.Format.fprintf fmt "%d")
  [@ocaml.warning "-39"][@ocaml.warning "-A"])
and show_id : id -> Ppx_deriving_runtime.string =
  fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_id x[@@ocaml.warning
                                                              "-32"]
and pp_eq
  : Ppx_deriving_runtime.Format.formatter -> eq -> Ppx_deriving_runtime.unit
  =
  ((let __1 = pp_term
    and __0 = pp_term in
    ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
        fun fmt ->
          fun (a0, a1) ->
            Ppx_deriving_runtime.Format.fprintf fmt "(@[";
            ((__0 fmt) a0;
             Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
             (__1 fmt) a1);
            Ppx_deriving_runtime.Format.fprintf fmt "@])")
      [@ocaml.warning "-A"]))
  [@ocaml.warning "-39"])
and show_eq : eq -> Ppx_deriving_runtime.string =
  fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_eq x[@@ocaml.warning
                                                              "-32"]
and pp_term
  : Ppx_deriving_runtime.Format.formatter ->
      term -> Ppx_deriving_runtime.unit
  =
  ((let __0 = pp_term in
    ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
        fun fmt ->
          function
          | Var a0 ->
              (Ppx_deriving_runtime.Format.fprintf fmt "(@[<2>Twee.Var@ ";
               (Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
               Ppx_deriving_runtime.Format.fprintf fmt "@])")
          | App (a0, a1) ->
              (Ppx_deriving_runtime.Format.fprintf fmt "(@[<2>Twee.App (@,";
               ((Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                ((fun x ->
                    Ppx_deriving_runtime.Format.fprintf fmt "@[<2>[";
                    ignore
                      (List.fold_left
                         (fun sep ->
                            fun x ->
                              if sep
                              then
                                Ppx_deriving_runtime.Format.fprintf fmt ";@ ";
                              (__0 fmt) x;
                              true) false x);
                    Ppx_deriving_runtime.Format.fprintf fmt "@,]@]")) a1);
               Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
      [@ocaml.warning "-A"]))
  [@ocaml.warning "-39"])
and show_term : term -> Ppx_deriving_runtime.string =
  fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_term x[@@ocaml.warning
                                                                "-32"]
and pp_proof
  : Ppx_deriving_runtime.Format.formatter ->
      proof -> Ppx_deriving_runtime.unit
  =
  ((let __1 = pp_rewrite
    and __0 = pp_term in
    ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
        fun fmt ->
          fun (a0, a1) ->
            Ppx_deriving_runtime.Format.fprintf fmt "(@[";
            ((__0 fmt) a0;
             Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
             ((fun x ->
                 Ppx_deriving_runtime.Format.fprintf fmt "@[<2>[";
                 ignore
                   (List.fold_left
                      (fun sep ->
                         fun x ->
                           if sep
                           then Ppx_deriving_runtime.Format.fprintf fmt ";@ ";
                           (__1 fmt) x;
                           true) false x);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,]@]")) a1);
            Ppx_deriving_runtime.Format.fprintf fmt "@])")
      [@ocaml.warning "-A"]))
  [@ocaml.warning "-39"])
and show_proof : proof -> Ppx_deriving_runtime.string =
  fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_proof x[@@ocaml.warning
                                                                 "-32"]
and pp_rewrite
  : Ppx_deriving_runtime.Format.formatter ->
      rewrite -> Ppx_deriving_runtime.unit
  =
  ((let __1 = pp_tactic
    and __0 = pp_term in
    ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
        fun fmt ->
          fun (a0, a1) ->
            Ppx_deriving_runtime.Format.fprintf fmt "(@[";
            ((__0 fmt) a0;
             Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
             (__1 fmt) a1);
            Ppx_deriving_runtime.Format.fprintf fmt "@])")
      [@ocaml.warning "-A"]))
  [@ocaml.warning "-39"])
and show_rewrite : rewrite -> Ppx_deriving_runtime.string =
  fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_rewrite x[@@ocaml.warning
                                                                   "-32"]
and pp_tactic
  : Ppx_deriving_runtime.Format.formatter ->
      tactic -> Ppx_deriving_runtime.unit
  =
  ((let __0 = pp_id in
    ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
        fun fmt ->
          function
          | ByAxiom (a0, a1, a2) ->
              (Ppx_deriving_runtime.Format.fprintf fmt
                 "(@[<2>Twee.ByAxiom (@,";
               (((__0 fmt) a0;
                 Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%S") a1);
                Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                (Ppx_deriving_runtime.Format.fprintf fmt "%B") a2);
               Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
      [@ocaml.warning "-A"]))
  [@ocaml.warning "-39"])
and show_tactic : tactic -> Ppx_deriving_runtime.string =
  fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_tactic x[@@ocaml.warning
                                                                  "-32"]
let _ = pp_output
and _ = show_output
and _ = pp_entry
and _ = show_entry
and _ = pp_id
and _ = show_id
and _ = pp_eq
and _ = show_eq
and _ = pp_term
and _ = show_term
and _ = pp_proof
and _ = show_proof
and _ = pp_rewrite
and _ = show_rewrite
and _ = pp_tactic
and _ = show_tactic
[@@@deriving.end]


let rec string_of_term = function
  | Var v -> v
  | App (f, args) ->
    f ^ "<" ^ (List.map string_of_term args |> String.concat ", ") ^ ">"


exception Parse_proof_error of string


let rec parse_output (lines : string list) : (output, string) result =
  match lines with [] -> Error "Empty output from twee" |
  fst :: lines ->
  
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
        if fst = "" then Ok (List.rev acc, lines) else
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
