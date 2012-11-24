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

module MA : Map.S with type key = Atom.t

type inst_trans =
    {
      i_reqs : SAtom.t;
      i_udnfs : SAtom.t list list;
      i_actions : SAtom.t;
      i_touched_terms : STerm.t;
    }

(* val search : Hstring.t list -> t_system -> SAtom.t list *)

val procs_from_nb : int -> Hstring.t list

val search : Hstring.t list -> t_system -> unit HSA.t

val search_stateless : Hstring.t list -> t_system -> (SAtom.t * STerm.t) MA.t

(* val search_only : t_system -> SAtom.t list *)

val extract_candidates_from_trace : 
  unit HSA.t -> STerm.t -> t_system -> t_system list

val extract_candidates_from_compagnons : 
  (SAtom.t * STerm.t) MA.t -> t_system -> t_system list


val select_relevant_candidates : t_system -> t_system list -> t_system list

val post_system : t_system -> t_system list

val instantiate_transitions : Hstring.t list -> Hstring.t list ->
  transition list -> inst_trans list

val missing_args : Hstring.t list -> Hstring.t list ->
  Hstring.t list * Hstring.t list

val abstract_others : SAtom.t -> Hstring.t list -> SAtom.t

val reachable_on_trace :
  t_system -> (transition * Hstring.t list) list -> bool
