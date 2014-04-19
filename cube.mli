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

open Types

type t =
 private {
   vars : Variable.t list;
   litterals : SAtom.t;
   array : ArrayAtom.t;
 }

val create : Variable.t list -> SAtom.t -> t
val normal_form : t -> t
val create_normal : SAtom.t -> t
val subst : Variable.subst -> t -> t

val size : t -> int
val card: t -> int

val inconsistent : ?use_sets:bool -> t -> bool
val inconsistent_2 : ?use_sets:bool -> t -> t -> bool

val inconsistent_set : SAtom.t -> bool
val inconsistent_array : ArrayAtom.t -> bool

val simplify_atoms_base : SAtom.t -> SAtom.t -> SAtom.t
val simplify_atoms : SAtom.t -> SAtom.t
val elim_ite_simplify_atoms : SAtom.t -> SAtom.t list

val simplify : t -> t
val elim_ite_simplify : t -> t list

val resolve_two : t -> t -> t option
val satom_globs : SAtom.t -> Term.Set.t

val print :  Format.formatter -> t -> unit
