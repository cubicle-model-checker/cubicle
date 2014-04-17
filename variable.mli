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

type t = Hstring.t

type subst = (t * t) list

val proc_vars : t list
val proc_vars_int : int list
val alpha_vars : t list
val fresh_vars : t list
val number : t -> int

val build_subst : t list -> t list -> subst
val subst : subst -> t -> t

val all_permutations : t list -> t list -> subst list
val all_instantiations : t list -> t list -> subst list
val all_arrangements : int -> t list -> subst list
val all_arrangements_arity : Hstring.t -> t list -> subst list
val permutations_missing : t list -> t list -> subst list

val print : formatter -> t -> unit
val print_vars : formatter -> t list -> unit
val print_subst : formatter -> subst -> unit
