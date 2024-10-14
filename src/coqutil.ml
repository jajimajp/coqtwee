(** Utilities for Coq *)

(** {2 String conversions} *)

let rec show_globref (gr : Names.GlobRef.t) : string =
  let open Names in
  let open GlobRef in
  let s = match gr with
  | VarRef var -> "VarRef " ^ show_var var
  | ConstRef c -> "ConstRef " ^ show_kn (Constant.canonical c)
  | IndRef (mutind, i) -> "IndRef " ^ show_kn (MutInd.canonical mutind) ^ " " ^ string_of_int i
  | ConstructRef ((mutind, mi), i) -> "ConstructRef " ^ show_kn (MutInd.canonical mutind) ^ " " ^ string_of_int mi ^ " " ^ string_of_int i in
  "(" ^ s ^ ")"

and show_var (v : Names.Id.t) : string =
  "(Id " ^ Names.Id.(to_string v) ^ ")"

and show_kn (kn : Names.KerName.t) : string =
  "(" ^ Names.KerName.(to_string kn) ^ ")"


(** {2 EConstr.t extractors} *)

let rec constr_of_globref (env : Environ.env) = function
| Names.GlobRef.VarRef v ->
  Environ.named_type v env
| Names.GlobRef.ConstRef c ->
  constr_of_constant env c
| _ -> Constr.mkVar (Names.Id.of_string "Dummy_for_unimplemented")

and constr_of_constant env (c : Names.Constant.t) =
  let constant_body = Environ.lookup_constant c env in
  constant_body.const_type