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

type t = 
  | Tint
  | Treal
  | Tbool
  | Tabstract of Hstring.t
  | Tsum of Hstring.t * Hstring.t list
  | Trecord of trecord
  | Tnull of trecord
and trecord = { name: Hstring.t;
		lbs: (Hstring.t * t) list
	      }

val hash : t -> int
val equal : t -> t -> bool
val compare : t -> t -> int
val print : Format.formatter -> t -> unit
