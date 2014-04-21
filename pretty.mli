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

open Format

(** {b Pretty printing functions } *)

val vt_width : int
(** Width of the virtual terminal (80 if cannot be detected) *)

val print_line : formatter -> unit -> unit
(** prints separating line *)

val print_double_line : formatter -> unit -> unit
(** prints separating double line *)

val print_title : formatter -> string -> unit
(** prints section title for stats *)
