(** Wrapper for twee *)

(** {2 Utilities} *)

val doctor : unit -> (unit, string) result
(** Checks twee installation and version of twee.
    Returns [Error msg] if twee is not installed or version is incorrect. *)


(** {2 TPTP representations} *)

(** Subset of TPTP *)
module Tptp : sig
  type t = clause list

  and clause = string * clause_type * clause_term
  (** Represents a clause in TPTP format.
      {b Example} "fof(name, axiom, <term>)" is represented as ("name", Axiom, <term>). *)

  and clause_type = Axiom | Conjecture
  and clause_term = Eq of eq | With_univ of eq with_univ_qunr
  and eq = term * term
  and term = T of string * term list
  (* variables will be ("V", []) *)

  and 'a with_univ_qunr = string list * 'a
  (** Universal quantifiers *)

  (** {3 Sanitizer} *)

  val sanitize : t -> t * (string * string) list
  (** Sanitizes the given TPTP clauses.
      First element of the tuple is the sanitized clauses.
      Second element of the tuple is the mapping from original names to sanitized names.
      NOTE: Unchanged names are not included in the mapping.  *)

  (** {3 String conversions} *)

  val to_string : t -> string
  val string_of_clause : clause -> string
  val string_of_clause_term : clause_term -> string
  val string_of_eq : eq -> string
  val string_of_term : term -> string
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
(** start_term * rewrites *)

and rewrite = term * tactic
(** Single step of rewriting. (next_term, tactic) *)

and tactic =
  | ByAxiom of int * string * bool (** (id, name, left_to_right?) *)
  | ByLemma of int * bool (** (id, left_to_right?) *)


(** {2 String conversions} *)

val string_of_output : output -> string
val string_of_entry : entry -> string
val string_of_id : id -> string
val string_of_eq : eq -> string
val string_of_term : term -> string
val string_of_proof : proof -> string
val string_of_rewrite : rewrite -> string
val string_of_tactic : tactic -> string


(** {2 Main functions} *)
val twee : Tptp.t -> (output, string) result
(** [twee tptp] returns a proof for the given TPTP clauses.
    Returns [Ok output] if proof is found.
    Returns [Error msg] if something goes wrong. *)

(** {2 Internal functions}
    Exported for testing purposes. Do not use. *)

val parse_axiom : string -> (entry, string) result
val parse_goal : string list -> (entry * string list, string) result
val parse_lemma : string list -> (entry * string list, string) result
val parse_output : string list -> (output, string) result