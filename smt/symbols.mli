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

type operator = 
  | Plus | Minus | Mult | Div | Modulo | Record | Access of Hstring.t
  | Concat of Hstring.t | Extract of Hstring.t
  | Get | Set

type name_kind = Ac | Constructor | Other

type t = 
  | True 
  | False
  | Name of Hstring.t * name_kind
  | Int of Hstring.t
  | Real of Hstring.t
  | Op of operator
  | Var of Hstring.t
  | Bitv of string

val name : ?kind:name_kind -> Hstring.t -> t
val var : string -> t
val int : string -> t
val real : string -> t

val is_ac : t -> bool

val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int

val print : Format.formatter -> t -> unit

module Map : Map.S with type key = t
module Set : Set.S with type elt = t

