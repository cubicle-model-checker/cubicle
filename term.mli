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

module type SType = sig
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

  type t = 
    | Const of int MConst.t
    | Elem of Hstring.t * sort
    | Access of Hstring.t * Variable.t list
    | Arith of t * int MConst.t
end

module Type : SType

include SType

val subst_sort : subst_sort -> sort -> sort

val compare_constants : int MConst.t -> int MConst.t -> int
val add_constants : int MConst.t -> int MConst.t -> int MConst.t
val const_sign : int MConst.t -> int option
val mult_const : int -> int MConst.t -> int MConst.t

val compare : t -> t -> int

val hash : t -> int

val subst : Variables.subst -> ?sigma_sort:subst_sort -> t -> t

val htrue : Hstring.t
val hfalse : Hstring.t

val procs_of : t -> Variable.Set.t
val type_of : t -> Smt.Type.t

module Set : Set.S with type elt = t
