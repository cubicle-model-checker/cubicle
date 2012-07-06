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

module HSA : Hashtbl.S with type key = SAtom.t

module MA : Map.S

(* val search : Hstring.t list -> t_system -> SAtom.t list *)

val search_nb : int -> t_system -> unit HSA.t

val search_stateless_nb : int -> t_system -> SAtom.t MA.t

(* val search_only : t_system -> SAtom.t list *)


val extract_candidates_from_trace : unit HSA.t -> t_system -> t_system list

val extract_candidates_from_compagnons : 
  SAtom.t MA.t -> t_system -> t_system list


val select_relevant_candidates : t_system -> t_system list -> t_system list
