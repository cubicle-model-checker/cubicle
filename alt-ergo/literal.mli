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


module type OrderedType = sig
  type t
  val compare : t -> t -> int
  val hash :  t -> int
  val print : Format.formatter -> t -> unit
end

type 'a view = 
  | Eq of 'a * 'a 
  | Distinct of bool * 'a list
  | Builtin of bool * Hstring.t * 'a list

module type S = sig
  type elt
  type t

  val make : elt view -> t
  val view : t -> elt view

  val neg : t -> t

  val add_label : Hstring.t -> t -> unit
  val label : t -> Hstring.t

  val print : Format.formatter -> t -> unit

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int

  module Map : Map.S with type key = t
  module Set : Set.S with type elt = t

end

module Make ( X : OrderedType ) : S with type elt = X.t

module type S_Term = sig

  include S with type elt = Term.t

  val mk_pred : Term.t -> t
  val vrai : t
  val faux : t

  val apply_subst : Term.subst -> t -> t

  val terms_of : t -> Term.Set.t
  val vars_of : t -> Symbols.Set.t

end

module LT : S_Term


