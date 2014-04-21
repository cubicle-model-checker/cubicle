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

type t = node_cube
(** the type of nodes constructed during the search *)

val variables : t -> Variable.t list
val array : t -> ArrayAtom.t
val litterals : t -> SAtom.t
val size : t -> int
val card : t -> int

val create :
  ?kind:kind -> ?from:(transition * Variable.t list * t) option -> Cube.t -> t
(** given a cube creates a node with a given kind, and a history *)

val origin : t -> t
(** returns the origin of the node, i.e. its further ancestor *)

val has_deleted_ancestor : t -> bool
(** returns [true] if one of the ancestor has been set to deleted *)

val ancestor_of : t -> t -> bool
(** [ancestor_of a b] returns [true] if [a] is an ancestor of [b] *)

val subset : t -> t -> bool
(** returns true if the set of litterals of the cube associated with the first
    arguement is a subset of the second argument *)

val print :  Format.formatter -> t -> unit
(** prints the cube of a node *)

val print_history :  Format.formatter -> t -> unit
(** prints the trace corresponding to the history of a node *)
