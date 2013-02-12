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

open Format
open Ast

val vt_width : int

val green : string -> string
val red : string -> string
val blue : string -> string
val cyan : string -> string
val magenta : string -> string
val bold : string -> string
val boldu : string -> string
val underline : string -> string
val greenbg : string -> string
val redbg : string -> string
val magentabg : string -> string
val yellowbg : string -> string

val print_term : formatter -> term -> unit

val print_atom : formatter -> Atom.t -> unit

val print_cube : formatter -> SAtom.t -> unit

val print_array : formatter -> ArrayAtom.t -> unit

val print_system : formatter -> t_system -> unit

val print_args : formatter -> Hstring.t list -> unit

val print_subst : formatter -> (Hstring.t * Hstring.t) list -> unit

val print_unsafe : formatter -> t_system -> unit

val print_node : formatter -> t_system -> unit

val print_bad : formatter -> t_system -> unit

val print_dead_node : formatter -> (t_system * int list) -> unit

val print_dead_node_to_cand : formatter -> (t_system * int list) -> unit

val print_verbose_node : formatter -> t_system -> unit

val syscall : string -> string
