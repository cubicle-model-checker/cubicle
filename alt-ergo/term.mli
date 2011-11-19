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

type t

module Map : Map.S with type key = t
module Set : Set.S with type elt = t

type view = private {f: Symbols.t ; xs: t list; ty: Ty.t; tag : int}

type subst = t Subst.t * Ty.subst

val view : t -> view
val make : Symbols.t -> t list -> Ty.t -> t

val shorten : t -> t

val vrai : t
val faux : t
val void : t

val int : string -> t
val real : string -> t
val bitv : string -> Ty.t -> t

val fresh_name : Ty.t -> t

val is_int : t -> bool
val is_real : t -> bool

val compare : t -> t -> int
val equal : t -> t -> bool
val hash : t -> int

val vars_of : t -> Symbols.Set.t
val vars_of_as_term : t -> Set.t
val vty_of : t -> Ty.Svty.t

val pred : t -> t

val apply_subst : subst -> t -> t
val compare_subst : subst -> subst -> int
val fold_subst_term : (Symbols.t -> t -> 'b -> 'b) -> subst -> 'b -> 'b

val union_subst : subst -> subst -> subst

val print : Format.formatter -> t -> unit
val print_list : Format.formatter -> t list -> unit

val dummy : t 

val subterms : Set.t -> t -> Set.t
