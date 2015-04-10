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

open Types

(** Generation of graphical search graphs with dot/graphviz *)

val new_node : Node.t -> unit

val candidate : Node.t -> Node.t -> unit

val fixpoint : Node.t -> int list -> unit

val restart : unit -> unit

val error_trace : Node.t -> unit

val open_dot : unit -> (unit -> unit)

val delete_node_by : Node.t -> Node.t -> unit

val new_node_ic3 : string -> unit

val new_relations_ic3 : ?style:string -> ?color:string -> string -> (string * Ast.transition) list -> unit

val new_relation_step_ic3 : ?style:string -> ?color:string -> string -> string -> Ast.transition -> int -> unit

val new_relation_ic3 : ?style:string -> ?color:string -> string -> string -> Ast.transition  -> unit
