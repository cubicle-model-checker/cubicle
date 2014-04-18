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
open Types

type kind = Node | Approx | Inv

type t =
    { 
      cube : Cube.t;
      alpha : Variable.t list * ArrayAtom.t;
      tag : int;
      kind : kind;
      depth : int;
      mutable deleted : bool;
      from : (transition * Variable.t list * t) list;
    }

val variables : t -> Variable.t list
val array : t -> ArrayAtom.t
val litterals : t -> SAtom.t

val create :
  ?kind:kind -> ?from:(transition * Variable.t list * t) option -> Cube.t -> t

val origin : t -> t

val has_deleted_ancestor : t -> bool
val ancestor_of : t -> t -> bool
val subset : t -> t -> bool

val print :  Format.formatter -> t -> unit
val print_history :  Format.formatter -> t -> unit
