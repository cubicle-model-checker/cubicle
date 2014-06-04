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

(* module HI : Hashtbl.S with type key = int *)

val search : Hstring.t list -> t_system -> unit
(** [search procs init] performs enumerative forward search. States are
    stored in an internal hash-table. *)

val resume_search_from : Hstring.t list -> t_system -> unit

val replay_trace_and_expand : Hstring.t list -> t_system -> unit

val hist_cand : Ast.t_system -> int ref -> (int array * Hstring.t list) list

val smallest_to_resist_on_trace : int ref -> Ast.t_system list -> Ast.t_system list

(** Given a list of candidate approximations (and their permutations),
    checks if one is satisfiable on the finite model constructed by
    [search]. *)
