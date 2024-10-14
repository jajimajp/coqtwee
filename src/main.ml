let twee_doctor () =
  match Twee.doctor () with
  | Ok () -> Feedback.msg_info Pp.(strbrk "Correct version of twee found.")
  | Error msg -> Feedback.msg_warning Pp.(strbrk msg)


(** Extracts TPTP clauses from the axioms and the goal.
    NOTE: Converted TPTP may contain names that cannot be used in twee.
      Consider using [Twee.Tptp.sanitize] to convert names to valid twee names. *)
let extract_tptp (axioms : Names.GlobRef.t list) (goal : Proofview.Goal.t) : Twee.Tptp.t =
  let env = Proofview.Goal.env goal in
  let axiom_clauses = List.map (fun axiom ->
    let constr = Coqutil.constr_of_globref env axiom in
    let name = Pp.string_of_ppcmds (Names.GlobRef.print axiom) in
    Prover.clause_of_constr name constr) axioms in
  let concl = Proofview.Goal.concl goal in
  let sigma = Proofview.Goal.sigma goal in
  let concl = EConstr.to_constr sigma concl in

  let clause = Prover.clause_of_concl "goal" concl in

  axiom_clauses @ [clause]


let prove_with_twee_goal
(env : Environ.env) (sigma : Evd.evar_map) (goal : Twee.id * string * Twee.eq * Twee.proof)
: unit Proofview.tactic =
    let id, name, (l, r), (start_term, rewrites) = goal in
    let rewrites =
      rewrites |> List.map (function _term, Twee.ByAxiom (_id, name, l2r) ->
        let delayed_constr = (fun env sigma ->
          let constr =
            if name = "h" then
              EConstr.mkVar (Names.Id.of_string "h") (* TODO: Remember input and use it *)
            else
              let qualid = Libnames.qualid_of_string name in
              EConstr.mkRef (Nametab.global qualid, EConstr.EInstance.empty) in

          let constr_with_bindings = constr, Tactypes.NoBindings in
          sigma, constr_with_bindings) in
        let occs = Locus.OnlyOccurrences [1] in (* TODO: iterate over all occurrences *)
        let rewrite_in = None in
        Rewrite.cl_rewrite_clause delayed_constr l2r occs rewrite_in)
      |> List.fold_left (fun tac1 tac2 -> Proofview.tclTHEN tac1 tac2) Proofview.(tclUNIT ()) in
    Proofview.tclTHEN rewrites Tactics.reflexivity
  

let prove_with_twee_output
(env : Environ.env) (sigma : Evd.evar_map) (output : Twee.output)
: unit Proofview.tactic =
    output |> List.map (function
    | Twee.Axiom (_, name, _) ->
      Proofview.tclUNIT (Feedback.msg_debug
        Pp.(str "Do nothing for axiom" ++ spc() ++ str name ++
            str ". This may cause problems."))
    | Twee.Goal (id, name, eq, proof) ->
      prove_with_twee_goal env sigma (id, name, eq, proof))
    |> List.fold_left (fun tac1 tac2 -> Proofview.tclTHEN tac1 tac2) Proofview.(tclUNIT ())


let twee (axioms : Names.GlobRef.t list) : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    let tptp = extract_tptp axioms gl in
    let tptp, _mapping = Twee.Tptp.sanitize tptp in
    (* TODO: reconstruct using mapping *)

    Feedback.msg_debug Pp.(str "tptp " ++ str (Twee.Tptp.to_string tptp));

    match Twee.twee tptp with
    | Error msg ->
      Feedback.msg_warning Pp.(str "Error in twee execution: " ++ str msg)
      |> Proofview.tclUNIT
    | Ok output ->

    Pp.pr_vertical_list (fun entry ->
      Pp.(str (Twee.string_of_entry entry)))
      output
    |> Feedback.msg_debug;

    let (env, sigma) = Proofview.Goal.(env gl, sigma gl) in

    prove_with_twee_output env sigma output)
