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
open Types

module HSA : Hashtbl.S with type key = SAtom.t

module MA : Map.S with type key = Atom.t

type inst_trans =
    {
      i_reqs : SAtom.t;
      i_udnfs : SAtom.t list list;
      i_actions : SAtom.t;
      i_touched_terms : Term.Set.t;
    }

type possible_result = 
  | Reach of (transition * Variable.subst) list 
  | Spurious of trace
  | Unreach

(* val search : Hstring.t list -> t_system -> SAtom.t list *)

val search : Hstring.t list -> t_system -> unit HSA.t

val search_stateless : Hstring.t list -> t_system -> (SAtom.t * Term.Set.t) MA.t


val instantiate_transitions : Variable.t list -> Variable.t list ->
  transition list -> inst_trans list

val abstract_others : SAtom.t -> Hstring.t list -> SAtom.t

val reachable_on_trace_from_init :
  t_system -> Node.t -> trace -> possible_result

val spurious : Node.t -> bool
			     
val spurious_error_trace : t_system -> Node.t -> bool

val spurious_due_to_cfm : t_system -> Node.t -> bool

val conflicting_from_trace : t_system -> trace -> SAtom.t list

val uguard_dnf : 
  Variable.subst ->
  Variable.t list -> Variable.t list ->
  (Variable.t * SAtom.t list) list -> SAtom.t list list
