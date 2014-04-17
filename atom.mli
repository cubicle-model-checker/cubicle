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

module rec Type : sig
  type t =
    | True
    | False
    | Comp of Term.t * Term.op_comp * Term.t
    | Ite of Set.t * t * t
end
and Atom : sig
  type t =
    | True
    | False
    | Comp of Term.t * Term.op_comp * Term.t
    | Ite of Set.t * t * t

  val compare : t -> t -> int
  val trivial_is_implied : t -> t -> int
  val neg : t -> t
  val hash : t -> int
  val equal : t -> t -> bool
  val subst : Variable.subst -> ?sigma_sort:Term.subst_sort -> t -> t
  val has_var : Variable.t -> t -> bool
  val variables : t -> Variables.Set.t
  val print : Format.formatter -> t -> unit
end
and Set : sig 
  include Set.S with type elt = t

  val equal : t -> t -> bool
  val hash : t -> int
  val subst : Variable.subst -> ?sigma_sort:Term.subst_sort -> t -> t
  val variables : t -> Variable.Set.t
  val glob_terms : t -> Term.Set.t
end

module Array : sig
  type atom = t
  type t = atom array
  val equal : t -> t -> bool
  val hash : t -> int
  val subset : t -> t -> bool
  val trivial_is_implied : t -> t -> bool
  val of_satom : Set.t -> t
  val to_satom : t -> Set.t
  val union : t -> t -> t
  val apply_subst : Variable.subst -> t -> t
  val nb_diff : t -> t -> int
  val compare_nb_diff : t -> t -> t -> int
  val compare_nb_common : t -> t -> t -> int
  val diff : t -> t -> t
  val alpha : t -> Variable.t list -> Variable.t list * t
end

(* type aliases for convenience *)

module type S = sig
  type t =
    | True
    | False
    | Comp of Term.t * Term.op_comp * Term.t
    | Ite of Set.t * t * t

  val compare : t -> t -> int
  val trivial_is_implied : t -> t -> int
  val neg : t -> t
  val hash : t -> int
  val equal : t -> t -> bool
  val subst : Variable.subst -> ?sigma_sort:Term.subst_sort -> t -> t
  val has_var : Variable.t -> t -> bool
  val variables : t -> Variables.Set.t
  val print : Format.formatter -> t -> unit
end

include S with type t = Atom.t

type array = Array.t

type set = Set.t
