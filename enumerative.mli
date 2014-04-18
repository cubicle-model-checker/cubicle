(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2013                          *)
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

val search : Variable.t list -> t_system -> unit
(** [search procs init] performs enumerative forward search. States are
    stored in an internal hash-table. *)

val resume_search_from : Variable.t list -> t_system -> unit

val replay_trace_and_expand : Variable.t list -> t_system -> unit

val smallest_to_resist_on_trace : Node.t list -> Node.t list
(** Given a list of candidate approximations (and their permutations),
    checks if one is satisfiable on the finite model constructed by
    [search]. *)


val init : t_system -> unit

val first_good_candidate : Node.t list -> Node.t option 
