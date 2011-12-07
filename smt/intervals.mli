(**************************************************************************)
(*                                                                        *)
(*     The Alt-ergo theorem prover                                        *)
(*     Copyright (C) 2006-2010                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
(*     Alain Mebsout                                                      *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

open Num

type t

exception NotConsistent of Explanation.t
exception Not_a_float

val undefined : Ty.t -> t

val point : num -> Ty.t -> Explanation.t -> t

val doesnt_contain_0 : t -> Sig.answer

val is_strict_smaller : t -> t -> bool

val new_borne_sup : Explanation.t -> num -> is_le : bool -> t -> t

val new_borne_inf : Explanation.t -> num -> is_le : bool -> t -> t

val is_point : t -> (num * Explanation.t) option

val intersect : t -> t -> t

val exclude : t -> t -> t

val mult : t -> t -> t

val power : int -> t -> t

val sqrt : t -> t

val root : int -> t -> t 

val add : t -> t -> t

val scale : num -> t -> t

val print : Format.formatter -> t -> unit

val finite_size : t -> num option

val borne_inf : t -> num * Explanation.t

val div : t -> t -> t
