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

type kind = Node | Approx | Inv

type t =
    { 
      cube : Cube.t;
      alpha : Variable.t list * Atom.Array.t;
      tag : int;
      kind : kind;
      mutable deleted : bool;
      from : (transition * Variable.t list * node) list;
    }

val create :
  ?kind:kind -> ?from:(Ast.transition * Variable.t list * t) option -> t

val origin : t -> t

val has_deleted_ancestor : t -> bool

val print :  Format.formatter -> t -> unit
