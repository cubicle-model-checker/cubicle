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

(** {b Variables of the parameterized domain} *)

type t = Hstring.t
(** the type of variables *)

type subst = (t * t) list
(** the type of variable substitutions *)

module Set : Set.S with type elt = t
(** set of variables *)

(** {3 Predefinied variables } *)

val procs : t list
(** predefinied list of skolem variables [#1], [#2], [#3], ... Their number is
    controlled by {! Options.max_proc } *)

val proc_vars_int : int list
val alphas : t list
val freshs : t list
val number : t -> int


val is_proc : t -> bool
(** returns [true] if the variable is a skolem process [#i] *)

(** {3 Substitutions } *)

val build_subst : t list -> t list -> subst
(** constructs a variable substitution *)

val subst : subst -> t -> t
(** apply a variable substitution to a variable *)

val is_subst_identity : subst -> bool
(** returns [true] if the substitution is the identity function *)


(** {3 Variable instantiation } *)

val all_permutations : 'a list -> 'a list -> ('a * 'a) list list
(** [all_permutations l1 l2] returns all possible substitutions from 
    [l1] to [l2] assuming that the variables of both lists are distinct.
    [l2] must be longer than (or the same size as) [l1] *)

val all_instantiations : t list -> t list -> subst list
(** same as {! all_permutations} but does not assume elements of [l1] to be
    distinct. [l1] can be longer than [l2]. *)

val all_arrangements : int -> t list -> t list list
val all_arrangements_arity : Hstring.t -> t list -> t list list
val permutations_missing : t list -> t list -> subst list

val extra_vars : t list -> t list -> t list
val extra_procs : t list -> t list -> t list
val append_extra_procs : t list -> t list -> t list
val give_procs : int -> t list


(** {3 Printing } *)

val print : formatter -> t -> unit
val print_vars : formatter -> t list -> unit
val print_subst : formatter -> subst -> unit
