(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2015                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

(* Don't edit this file, but muparser_prefix.mli instead! *)

(** State being currently constructed *)
val st : int array ref

val env : Enumerative.env ref

(** Called by {!Mulexer} *)
val new_state : unit -> unit

(** Filled by {!Murphi.mk_encoding_table} *)
val encoding : (string, int) Hashtbl.t
