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

module Set : Set.S with type elt = t

val procs : t list
val proc_vars_int : int list
val alphas : t list
val freshs : t list
val number : t -> int

val build_subst : t list -> t list -> subst
val subst : subst -> t -> t
val is_subst_identity : subst -> bool

val all_permutations : t list -> t list -> subst list
val all_instantiations : t list -> t list -> subst list
val all_arrangements : int -> t list -> t list list
val all_arrangements_arity : Hstring.t -> t list -> t list list
val permutations_missing : t list -> t list -> subst list

val extra_vars : t list -> t list -> t list
val extra_procs : t list -> t list -> t list
val append_extra_procs : t list -> t list -> t list
val give_procs : int -> t list

val print : formatter -> t -> unit
val print_vars : formatter -> t list -> unit
val print_subst : formatter -> subst -> unit
