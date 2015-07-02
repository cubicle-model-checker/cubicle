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

open Types

(** Cubes and simplifications *)


type t =
 private {
   vars : Variable.t list; (** existential variables, all distinct *)
   litterals : SAtom.t; (** conjunction of litterals as a set *)
   array : ArrayAtom.t; (** conjunction of litterals as an array *)
 }
(** the type of cubes, i.e. a conjunction of litterals existentially quanfified
    by distinct variables. The invariant that the array and the set correspond
    to the same conjunction is enforced. *)

val create : Variable.t list -> SAtom.t -> t
(** create a cube given its existential variables and a conjunction *)

val normal_form : t -> t
(** puts a cube in normal form, so as to have the existential variables
    contiguous ([#1], [#2], [#3], ...). Performs variable renaming if
    necessary. *)

val create_normal : SAtom.t -> t
(** create a cube in normal form by finding the quantified variables *)

val subst : Variable.subst -> t -> t
(** apply a substitution on a cube *)

val dim : t -> int
(** returns the number of exitential distinct variables, i.e. the {e dimension}
    of the cube *)

val size: t -> int
(** returns the number of atoms in the conjuction *)

val compare_cubes : t -> t -> int
(** compare two cubes [c1] and [c2]
    [c1] > [c2] if [c1] has less variables or less litterals *)

(** {2 Inconsistencies detection } *)

(** The following five functions implements cheap checks for detecting
    inconsistencies *)

val inconsistent : ?use_sets:bool -> t -> bool

val inconsistent_2 : ?use_sets:bool -> t -> t -> bool
(** is the conjunction of [c1] and [c2] inconsistent knowing that [c1] and [c2]
    are consistent on their own. *)

val inconsistent_set : SAtom.t -> bool
(** returns [true] if the conjunction inconsistent *)

val inconsistent_array : ArrayAtom.t -> bool
(** same as {! inconsistent_set} but for arrays *)

val inconsistent_2arrays : ArrayAtom.t -> ArrayAtom.t -> bool
(** same as {! inconsistent_2} but for arrays *)


(** {2 Simplifications of cubes } *)

val simplify_atoms_base : SAtom.t -> SAtom.t -> SAtom.t
(** [simplify_atoms_base b c] simplifies [c] in the context of [b].
    Raises [Exit] if it becomes inconsistent *)

val simplify_atoms : SAtom.t -> SAtom.t
(** simplify a conjunction. Raises [Exit] if it becomes inconsistent. *)

val simplify : t -> t
(** simplify a cube. Raises [Exit] if it becomes inconsistent. *)

val elim_ite_simplify_atoms : SAtom.t -> SAtom.t list
(** lifts [if-then-else] constructs and simplify a conjunction *)

val elim_ite_simplify : t -> t list
(** lifts [if-then-else] constructs and simplify a cube *)


(** {2 Misc } *)

val resolve_two : t -> t -> t option
val satom_globs : SAtom.t -> Term.Set.t

val print :  Format.formatter -> t -> unit

(** {IC3 } *)

val equivalent : t -> t -> bool
(* val is_subformula : t -> t -> bool *)
val test_is_subformula : t -> t -> bool
