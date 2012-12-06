(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                  Universite Paris-Sud 11                               *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

open Ast

(* module HI : Hashtbl.S with type key = int *)

val search : Hstring.t list -> t_system -> unit

val stateless_search : Hstring.t list -> t_system -> t_system list

val local_stateless_search : Hstring.t list -> t_system -> t_system list

val smallest_to_resist_on_trace : t_system list -> t_system list









