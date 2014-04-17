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

type kind = Node | Approx | Inv

type t =
    { 
      cube : Cube.t;
      alpha : Variable.t list * Atom.Array.t;
      tag : int;
      kind : kind;
      mutable deleted : bool;
      from : (transition * Variable.t list * t) list;
    }

val variables : t -> Variable.t list
val array : t -> Atom.Array.t

val create :
  ?kind:kind -> ?from:(Ast.transition * Variable.t list * t) option -> t

val origin : t -> t

val has_deleted_ancestor : t -> bool

(* TODO *)
val add_and_resolve : t -> t Cubetrie.t -> t Cubetrie.t

val print :  Format.formatter -> t -> unit
val print_history :  Format.formatter -> t -> unit
