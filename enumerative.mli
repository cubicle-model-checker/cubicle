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
(** The type of environments for enumerative explorations *)

type state = private int array
(** The type of states, we allow states to be constructed from the outside by
    calling the function [new_undef_state]. *)

val print_state : env -> Format.formatter -> state -> unit
(** Printing a state. It is decoded to an {!SAtom} in a very inefficient
    manner. This function should only be used for debugging. *)

val empty_env : env
(** A dummy empty environment. *)

val mk_env : int -> t_system -> env
(** [mk_env nb sys] creates an environment for the enumerative exploration of
    the transition system [sys] with a fixed number [nb] of processes. *)

val int_of_term : env -> Types.term -> int
(** Encoding of a term in the enumerative environment. *)

val next_id : env -> int
(** Returns the next free integer that is not used for encoding terms. *)

val new_undef_state : env -> state
(** Returns a new uninitialized state from an enumertive environment *)

val empty_state : state
(** A dummy empty state. *)

val register_state : env -> state -> unit
(** Register the given state as an explored state in the environment. *)

val size_of_env : env -> int
(** Returns the (heuristically) computed size of tables needed for the
    exploration. *)

val no_scan_states : env -> unit
(** Prevent the GC from scanning the list of states stored in the environemnt
    as it is going to be kept in memory all the time. Call this function once
    the exploration is finished. *)

val print_last : env -> unit

(** {2 Oracle interface } *)

(** see {! Oracle.S} *)

include Oracle.S
