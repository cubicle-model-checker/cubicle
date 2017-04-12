(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2014                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

(** Statistics *)

exception ReachedLimit
(** raised if the search exceeds the allocated limits *)

val cpt_delete : int ref
(** number of delted nodes *)

val new_node : Node.t -> unit
(** register the treatment of a new node *)

val fixpoint : Node.t -> int list -> unit
(** register the result of a successful fixpoint check *)

val restart : unit -> unit
(** resisters a backtrack and restart *)

val remaining : (unit -> int * int) -> unit
(** outputs number of remaining nodes in the queues given a function to count
    them. This function will be called only if {! Options.quiet} is false *)

val delete : int -> unit
(** [delete nb] registers [nb] deletions *)

val candidate : Node.t -> Node.t -> unit
(** [candidate n c ] registers a new candidate [c] emerging from node [n] *)

val print_report : safe:bool -> Node.t list -> Node.t list -> unit
(** prints a complete report. Additionally, if {! Options.profiling} is set
    then output timing information. *)

val print_stats_certificate : Node.t list -> string -> unit

                                                         
val error_trace : Ast.t_system -> Node.t -> unit
(** print an error trace given a faulty node *)

val check_limit : Node.t -> unit
(** Raises [ReachedLimit] if the limits given in {! Options} have been
    exceeded *)
