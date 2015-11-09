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

open Ast

(** Enumerative forward search *)

val search : Variable.t list -> t_system -> unit
(** [search procs init] performs enumerative forward search. States are
    stored in an internal hash-table. *)

val resume_search_from : Variable.t list -> t_system -> unit

val replay_trace_and_expand : Variable.t list -> t_system -> Node.t -> unit

val smallest_to_resist_on_trace : Node.t list -> Node.t list
(** Given a list of candidate approximations (and their permutations),
    checks if one is satisfiable on the finite model constructed by
    [search]. *)

(** {2 Exported functions to construct enumeration based oracles } *)

type env

type state = int array

val empty_env : env

val mk_env : int -> t_system -> env

val int_of_term : env -> Types.term -> int

val next_id : env -> int

val new_empty_state : env -> state

val register_state : env -> state -> unit

val size_of_env : env -> int

val no_scan_states : env -> unit

val print_last : env -> unit

(** {2 Oracle interface } *)

(** see {! Oracle.S} *)

include Oracle.S
