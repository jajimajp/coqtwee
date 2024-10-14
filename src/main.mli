(** Main functions. Used by G_syntax *)

val twee_doctor : unit -> unit
(** Checks twee installation and version of twee.
    Prints result using Feedback.msg_notice. *)

val twee : Names.GlobRef.t list -> unit Proofview.tactic
(** The `twee` tactic.
    [twee axioms] returns tactic for given [axioms]. *)

