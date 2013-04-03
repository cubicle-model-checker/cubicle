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

val resume_search_from : Hstring.t list -> t_system -> unit

val replay_trace_and_expand : Hstring.t list -> t_system -> unit

val smallest_to_resist_on_trace : t_system list list -> t_system list









