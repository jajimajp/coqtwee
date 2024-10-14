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


let econstr_of_twee_eq (env : Environ.env) (sigma : Evd.evar_map) (set : Libnames.qualid) (eq : Twee.eq)
  : Evd.evar_map * Evd.econstr =
    let rec constrexpr (univ_qunrs : string list) (eq : Twee.eq) =
      let l, r = eq in
      let l, r = constrexpr_of_term l, constrexpr_of_term r in
      let open Constrexpr in
      CAst.make
        (CProdN
        ( [
            CLocalAssum
              ( List.map
                  (fun name ->
                    CAst.make (Names.Name.mk_name (Names.Id.of_string name)))
                  univ_qunrs,
                None,
                Default Explicit,
                CAst.make (CRef (set, None)) );
          ],
          CAst.make
            (CApp
              ( CAst.make (CRef (Libnames.qualid_of_string "eq", None)),
                [ (l, None); (r, None) ] )) ))

    and constrexpr_of_term (term : Twee.term) =
      let open Constrexpr in
      match term with
      | App (f, args) ->
          let args_constr =
            List.map (fun arg -> (constrexpr_of_term arg, None)) args
          in
          CAst.make
            (CApp (CAst.make (CRef (Libnames.qualid_of_string f, None)), args_constr))
      | Var x -> CAst.make (CRef (Libnames.qualid_of_string x, None)) in
    
    let variables (eq : Twee.eq) : string list =
      let rec variables_in_term (term : Twee.term) : string list =
        match term with
        | App (_, args) -> List.concat (List.map variables_in_term args)
        | Var x -> [x] in
      let l, r = eq in
      List.sort_uniq String.compare (variables_in_term l @ variables_in_term r) in

    let word_starts_with_upper_case (word : string) : bool =
      let first_char = String.get word 0 in
      Char.uppercase_ascii first_char = first_char in
    let univ_qunrs eq = variables eq |> List.filter word_starts_with_upper_case in
    let constrex = constrexpr (univ_qunrs eq) eq in

    Constrintern.interp_constr_evars env sigma constrex

  
exception Outer_proof_failed (* Unrecoverable error *)
exception Inner_proof_failed (* Recoverable error *)
let prove_with_twee_proof (env : Environ.env) (sigma : Evd.evar_map) (proof : Twee.proof) : unit Proofview.tactic =
  let (_term, rewrites) = proof in
  let finalizer : unit Proofview.tactic =
    Proofview.tclPROGRESS (Tactics.intros_reflexivity) in
  let rewrites =
    rewrites
    |> List.rev (* List.fold_right is not tail-rec, so use rev + fold_left *)
    |> List.fold_left (fun rest_tacs (term, tactic) ->
      let rewrite_single_at (at : int) = match tactic with
        | Twee.ByAxiom (_id, name, l2r) ->
          let delayed_constr = (fun env sigma ->
            let constr =
              if name = "h" then
                EConstr.mkVar (Names.Id.of_string "h") (* TODO: Remember input and use it *)
              else
                let qualid = Libnames.qualid_of_string name in
                EConstr.mkRef (Nametab.global qualid, EConstr.EInstance.empty) in

            let constr_with_bindings = constr, Tactypes.NoBindings in
            sigma, constr_with_bindings) in
          let occs = Locus.OnlyOccurrences [at] in
          let rewrite_in = None in
          Rewrite.cl_rewrite_clause delayed_constr l2r occs rewrite_in
        | Twee.ByLemma (id, l2r) ->
          let delayed_constr = (fun env sigma ->
            let constr =
              let name = "h_lemma_" ^ string_of_int id in (* TODO: Protect from name conflicts *)
              EConstr.mkVar (Names.Id.of_string name) in (* TODO: Remember input and use it *)

            let constr_with_bindings = constr, Tactypes.NoBindings in
            sigma, constr_with_bindings) in
          let occs = Locus.OnlyOccurrences [at] in
          let rewrite_in = None in
          Rewrite.cl_rewrite_clause delayed_constr l2r occs rewrite_in in
      
      let rec rewrite (at : int) : unit Proofview.tactic =
        Proofview.tclIFCATCH
          (Proofview.tclTHEN
            (Proofview.tclIFCATCH 
              (rewrite_single_at at)
              (fun _ -> Feedback.msg_debug Pp.(str "Succeed (out) " ++ str (Twee.string_of_term term)) |> Proofview.tclUNIT)
              (fun _ -> Feedback.msg_debug Pp.(str "Failed (out) " ++ str (Twee.string_of_term term)); Proofview.tclZERO (Outer_proof_failed)))
            (Proofview.tclIFCATCH
              rest_tacs
              (fun _ -> Feedback.msg_debug Pp.(str "Succeed (in) " ++ str (Twee.string_of_term term)) |> Proofview.tclUNIT)
              (fun _ -> Feedback.msg_debug Pp.(str "Failed (in) " ++ str (Twee.string_of_term term)); Proofview.tclZERO (Inner_proof_failed))))
          (fun _ -> Feedback.msg_debug Pp.(str "Succeed (tot) " ++ str (Twee.string_of_term term)) |> Proofview.tclUNIT)
          (fun (exn, _) ->
            Feedback.msg_debug Pp.(str "Failed (tot) " ++ str (Twee.string_of_term term));
            match exn with
            | Outer_proof_failed -> Proofview.tclZERO Outer_proof_failed
            | Inner_proof_failed -> rewrite (at + 1)) in
      
      rewrite 1) finalizer in
  rewrites


let assert_lemma_as_hyp (env : Environ.env) (sigma : Evd.evar_map) (name : string) (lemma : Twee.id * Twee.eq * Twee.proof) =
  let id, (l, r), proof = lemma in
  let sigma, econstr = econstr_of_twee_eq env sigma (Libnames.qualid_of_string "G" (* TODO *)) (l, r) in
  Proofview.tclIFCATCH
    (Tactics.assert_by (Names.Name.mk_name (Names.Id.of_string name)) econstr (prove_with_twee_proof env sigma proof))
    (fun _ -> Feedback.msg_debug Pp.(str "Succeed lemma " ++ str name) |> Proofview.tclUNIT)
    (fun _ -> Feedback.msg_debug Pp.(str "Failed lemma " ++ str name) |> Proofview.tclUNIT)
  

let prove_with_twee_goal
(env : Environ.env) (sigma : Evd.evar_map) (goal : Twee.id * string * Twee.eq * Twee.proof)
: unit Proofview.tactic =
    let id, name, (l, r), proof = goal in

    Proofview.tclIFCATCH
      (prove_with_twee_proof env sigma proof)
      (fun _ -> Feedback.msg_debug Pp.(str "Succeed goal " ++ str name) |> Proofview.tclUNIT)
      (fun _ -> Feedback.msg_debug Pp.(str "Failed goal " ++ str name) |> Proofview.tclUNIT)
  

let prove_with_twee_output
(env : Environ.env) (sigma : Evd.evar_map) (output : Twee.output)
: unit Proofview.tactic =
    output |> List.map (function
    | Twee.Axiom (_, name, _) ->
      Proofview.tclUNIT (Feedback.msg_debug
        Pp.(str "Do nothing for axiom" ++ spc() ++ str name ++
            str ". This may cause problems."))
    | Twee.Lemma (id, eq, proof) ->
      let name = "h_lemma_" ^ string_of_int id in (* TODO: Protect from name conflicts *)
      assert_lemma_as_hyp env sigma name (id, eq, proof)
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
