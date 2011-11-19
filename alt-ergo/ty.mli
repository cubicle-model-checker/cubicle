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

type t = 
    | Tint
    | Treal
    | Tbool
    | Tunit
    | Tvar of tvar
    | Tbitv of int
    | Text of t list * Hstring.t
    | Tfarray of t * t
    | Tnext of t
    | Tsum of Hstring.t * Hstring.t list
    | Trecord of trecord

and tvar = { v : int ; mutable value : t option }
and trecord = { 
  mutable args : t list; 
  name : Hstring.t; 
  mutable lbs :  (Hstring.t * t) list
}


type subst

val esubst : subst

exception TypeClash of t*t

val tunit : t

val text : t list -> string -> t
val tsum : string -> string list -> t
val trecord : t list -> string -> (string * t) list -> t

val shorten : t -> t

val fresh_var : unit -> tvar
val fresh_empty_text : unit -> t

val fresh : t -> subst -> t * subst
val fresh_list : t list -> subst -> t list * subst

val equal : t -> t -> bool
val hash : t -> int
val compare : t -> t -> int

val unify : t -> t -> unit
val matching : subst -> t -> t -> subst

val apply_subst : subst -> t -> t
val instantiate : t list -> t list -> t -> t

(* Applique la seconde substitution sur la premiere 
   puis fais l'union des map avec prioritée à la première *)
val union_subst : subst -> subst -> subst

val compare_subst : subst -> subst -> int

val print : Format.formatter -> t -> unit
(*val printl : Format.formatter -> t list -> unit*)

module Svty : Set.S

val vty_of : t -> Svty.t

val monomorphize: t -> t

val print_subst: Format.formatter -> subst -> unit
