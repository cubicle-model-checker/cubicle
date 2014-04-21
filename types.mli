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

type op_comp = Eq | Lt | Le | Neq
type op_arith = Plus | Minus
type sort = Glob | Constr | Var
type subst_sort = (sort * sort) list

type const =
    ConstInt of Num.num | ConstReal of Num.num | ConstName of Hstring.t
                                                                
module MConst : sig 
  include Map.S with type key = const
  val choose : int t -> key * int
  val is_num : int t -> Num.num option
end

val subst_sort : subst_sort -> sort -> sort

val compare_constants : int MConst.t -> int MConst.t -> int
val add_constants : int MConst.t -> int MConst.t -> int MConst.t
val const_sign : int MConst.t -> int option
val const_nul : int MConst.t -> bool
val mult_const : int -> int MConst.t -> int MConst.t


type term =
  | Const of int MConst.t
  | Elem of Hstring.t * sort
  | Access of Hstring.t * Variable.t list
  | Arith of term * int MConst.t


module Term : sig

  type t = term

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
  val subst : Variable.subst -> ?sigma_sort:subst_sort -> t -> t
  val htrue : Hstring.t
  val hfalse : Hstring.t
  val variables : t -> Variable.Set.t
  val variables_proc : t -> Variable.Set.t
  val type_of : t -> Smt.Type.t
  val print : Format.formatter -> t -> unit

  module Set : Set.S with type elt = t

end



module rec Atom : sig
  type t =
    | True
    | False
    | Comp of Term.t * op_comp * Term.t
    | Ite of SAtom.t * t * t

  val compare : t -> t -> int
  val trivial_is_implied : t -> t -> int
  val neg : t -> t
  val hash : t -> int
  val equal : t -> t -> bool
  val subst : Variable.subst -> ?sigma_sort:subst_sort -> t -> t
  val has_var : Variable.t -> t -> bool
  val has_vars : Variable.t list -> t -> bool
  val variables : t -> Variable.Set.t
  val variables_proc : t -> Variable.Set.t
  val print : Format.formatter -> t -> unit
end
and SAtom : sig 
  include Set.S with type elt = Atom.t

  val equal : t -> t -> bool
  val hash : t -> int
  val subst : Variable.subst -> ?sigma_sort:subst_sort -> t -> t
  val variables : t -> Variable.Set.t
  val variables_proc : t -> Variable.Set.t
  val print : Format.formatter -> t -> unit
  val print_inline : Format.formatter -> t -> unit
end

module ArrayAtom : sig
  type t = Atom.t array
  val equal : t -> t -> bool
  val hash : t -> int
  val subset : t -> t -> bool
  val trivial_is_implied : t -> t -> bool
  val of_satom : SAtom.t -> t
  val to_satom : t -> SAtom.t
  val union : t -> t -> t
  val apply_subst : Variable.subst -> t -> t
  val nb_diff : t -> t -> int
  val compare_nb_diff : t -> t -> t -> int
  val compare_nb_common : t -> t -> t -> int
  val diff : t -> t -> t
  val alpha : t -> Variable.t list -> Variable.t list * t
  val print : Format.formatter -> t -> unit
end
