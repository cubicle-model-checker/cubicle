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

(** Pre-image computation *)

val make_tau : transition_info -> transition_func
(** functional form of transition *)

val pre_image : transition list -> Node.t -> Node.t list * Node.t list
(** [pre-image tau n] returns the pre-image of [n] by the transition relation
    [tau] as a disjunction of cubes in the form of two lists of new nodes. The
    second list is used to store nodes to postpone depending on a predefined
    strategy. *)

val pre : transition -> SAtom.t -> transition_info * Cube.t * Variable.t list

val make_cubes : Node.t list * Node.t list -> Variable.t list -> Node.t -> Ast.transition_info -> Cube.t -> Node.t list * Node.t list
