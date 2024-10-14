open Twee

let extract_univ_qunrs (constr : Constr.t) : string list * Constr.t =
  let open Constr in
  let rec aux acc constr =
    match kind constr with
    | Prod (name, _, body) ->
      let name = match Context.binder_name name with
      | Names.Name.Anonymous -> "_"
      | Names.Name.Name name -> Names.Id.to_string name in
      aux (name :: acc) body
      (* TODO: check consistency on 2nd value. *)
    | _ -> (List.rev acc, constr)
  in
  aux [] constr

let label_of_constr (constr : Constr.t) : string =
  let open Constr in
  match kind constr with
  | Rel       _ ->  "Rel       "
  | Var       _ ->  "Var       "
  | Meta      _ ->  "Meta      "
  | Evar      _ ->  "Evar      "
  | Sort      _ ->  "Sort      "
  | Cast      _ ->  "Cast      "
  | Prod      _ ->  "Prod      "
  | Lambda    _ ->  "Lambda    "
  | LetIn     _ ->  "LetIn     "
  | App       _ ->  "App       "
  | Const     _ ->  "Const     "
  | Ind       _ ->  "Ind       "
  | Construct _ ->  "Construct "
  | Case      _ ->  "Case      "
  | Fix       _ ->  "Fix       "
  | CoFix     _ ->  "CoFix     "
  | Proj      _ ->  "Proj      "
  | Int       _ ->  "Int       "
  | Float     _ ->  "Float     "
  | Array     _ ->  "Array     "

let destruct_eq (constr : Constr.t) : Constr.t * Constr.t =
  let open Constr in
  match kind constr with
  | App (c, [|_; l; r|]) ->
    if not (isInd c) then raise (Invalid_argument "destruct_eq: not an equality")
    else
    let (mutind, _), _ = destInd c in
    if not ("Coq.Init.Logic.eq" = Names.MutInd.to_string mutind) then
      raise (Invalid_argument ("destruct_eq: not an equality " ^ Names.MutInd.to_string mutind))
    else (l, r)
  | App (_, args) -> raise (Invalid_argument ("destruct_eq: not an equality" ^ string_of_int (Array.length args)))
  | _ -> failwith ("destruct_eq: not an equality " ^ label_of_constr constr)

let string_of_constr ~(rel_name : int -> string) (constr : Constr.t) : string =
  let open Constr in
  match kind constr with
  | Rel i -> rel_name i
  | Var id -> Names.Id.to_string id
  | Const (c, _univ) -> Names.Constant.to_string c
  | _ -> failwith ("string_of_constr: unsupported " ^ label_of_constr constr)

let term_of_constr ~(rel_name : int -> string) (constr : Constr.t) : Tptp.term =
  let open Constr in
  let open Tptp in
  let rec aux constr =
    match kind constr with
    | Rel i -> T (rel_name i, [])
    | Var id -> T (Names.Id.to_string id, [])
    | Const (c, _univ) -> T (Names.Constant.to_string c, [])
    | App (c, args) -> T (string_of_constr ~rel_name c, Array.map aux args |> Array.to_list)
    | _ -> failwith ("term_of_constr: unsupported " ^ label_of_constr constr)
  in
  aux constr

let clause_of_constr (name : string) (constr : Constr.t) : Tptp.clause =
  let univ_qunrs, constr = extract_univ_qunrs constr in
  let l, r = destruct_eq constr in
  let rel_name i = List.nth (List.rev univ_qunrs) (i - 1) in (* Rel is 1-indexed *)
  let l = term_of_constr ~rel_name l in
  let r = term_of_constr ~rel_name r in
  match univ_qunrs with
  | [] -> (name, Axiom, Eq (l, r))
  | _ -> (name, Axiom, With_univ (univ_qunrs, (l, r)))

let clause_of_concl (name : string) (concl : Constr.t) : Tptp.clause =
  let univ_qunrs, concl = extract_univ_qunrs concl in
  let l, r = destruct_eq concl in
  let rel_name i = List.nth (List.rev univ_qunrs) (i - 1) in (* Rel is 1-indexed *)
  let l = term_of_constr ~rel_name l in
  let r = term_of_constr ~rel_name r in
  match univ_qunrs with
  | [] -> (name, Conjecture, Eq (l, r))
  | _ -> (name, Conjecture, With_univ (univ_qunrs, (l, r)))
