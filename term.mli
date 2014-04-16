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

open Options

type op_comp = Eq | Lt | Le | Neq
type op_arith = Plus | Minus

type sort = Glob | Constr | Var
type subst_sort = (sort * sort) list

val subst_sort : subst_sort -> sort -> sort

type const = ConstInt of Num.num | ConstReal of Num.num | ConstName of Hstring.t

module MConst : sig 
  include Map.S with type key = const
  val choose : int t -> key * int
  val is_num : int t -> Num.num option
end

val compare_constants : int MConst.t -> int MConst.t -> int

type t = 
  | Const of int MConst.t
  | Var of Variable.t
  | Constr of Hstring.t
  | Glob of Hstring.t
  | Access of Hstring.t * Variable.t list
  | Arith of t * int MConst.t

val compare : t -> t -> int

val hash : t -> int

val subst : Variables.subst -> ?sigma_sort:subst_sort -> t -> t

val htrue : Hstring.t
val hfalse : Hstring.t

type acc_eq = { a : Hstring.t; i: Hstring.t; e: t }
