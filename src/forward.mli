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
open Cubtypes

(** Symbolic forward exploration *)


module HSA : Hashtbl.S with type key = SAtom.t

module MA : Map.S with type key = Atom.t

(** the type of instantiated transitions *)
type inst_trans =
    {
      i_reqs : SAtom.t;
      i_udnfs : SAtom.t list list;
      i_actions : SAtom.t;
      i_touched_terms : Term.Set.t;
    }

type possible_result =
  | Reach of (SAtom.t * transition_info * Variable.subst * SAtom.t) list 
  | Spurious of trace
  | Unreach

(* val search : Hstring.t list -> t_system -> SAtom.t list *)

val all_var_terms : Variable.t list -> t_system -> Term.Set.t

val search : Hstring.t list -> t_system -> unit HSA.t

val search_stateless : Hstring.t list -> t_system -> (SAtom.t * Term.Set.t) MA.t


(** instantiate transitions with a list of possible parameters *)
val instantiate_transitions : Variable.t list -> Variable.t list ->
  transition list -> inst_trans list

val abstract_others : SAtom.t -> Hstring.t list -> SAtom.t

val reachable_on_trace_from_init :
  t_system -> Node.t -> trace -> possible_result


(** check if the history of a node is spurious *)
val spurious : Node.t -> bool

(** check if an error trace is spurious *)
val spurious_error_trace : t_system -> Node.t -> bool

(** check if an error trace is spurious due to the {b Crash Failure Model } *)
val spurious_due_to_cfm : t_system -> Node.t -> bool

(** Replays the history of a faulty node and returns (possibly) an error
    trace *)
val replay_history :
  t_system -> Node.t ->
  (SAtom.t * transition_info * Variable.subst * SAtom.t) list option

(** check if an error trace is spurious due to the {b Crash Failure Model } *)
val conflicting_from_trace : t_system -> trace -> SAtom.t list

(** put a universal guard in disjunctive normal form *)
val uguard_dnf : 
  Variable.subst ->
  Variable.t list -> Variable.t list ->
  (Variable.t * SAtom.t list) list -> SAtom.t list list
