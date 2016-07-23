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

(** Node of the search graph *)

type t = node_cube
(** the type of nodes constructed during the search *)

val variables : t -> Variable.t list
(** returns the variables of the associated cube *)

val array : t -> ArrayAtom.t
(** returns the conjunction in array form of the associated cube *)

val litterals : t -> SAtom.t
(** returns the conjunction of litterals of the associated cube *)
                                 
val dim : t -> int
(** returns the dimension of the associated cube (see {! Cube.dim}) *)

val size : t -> int
(** returns the size of the associated cube (see {! Cube.size}) *)

val create :
  ?kind:kind -> ?from:trace_step option -> ?hist:t option -> Cube.t -> t
(** given a cube creates a node with a given kind, and a history *)

val compare_by_breadth : t -> t -> int
(** compare two nodes with a heuristic to find the most general one. Gives
    priority to nodes that have smaller depth in the search graph *)

val compare_by_history : t -> t -> int
(** compare two nodes with a heuristic to find the most general one. Gives
    priority to nodes that have most coherent trace in the search graph *)

val compare_by_depth : t -> t -> int
(** compare two nodes with a heuristic to find the most general one. Gives
    priority to nodes that have bigger depth in the search graph *)

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
