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

type gsubst = { sbt : Term.subst ; gen : int ; goal : bool}

type trigger_info = {
  trigger_query : Literal.LT.t option; 
  trigger_age : int ; 
  trigger_orig : Formula.t ; 
  trigger_formula : Formula.t ; 
  trigger_dep : Explanation.t ;
}

type term_info = {
  term_age : int ; 
  term_from_goal : bool ;
  term_orig : Formula.t option
}

module type X = sig
  type t

  val class_of : t -> Term.t -> Term.t list
  val query : Literal.LT.t -> t -> Sig.answer
end

module type S = sig
  type t
  type uf

  val empty : t
  val add_term : term_info -> Term.t -> t -> t 
  val add_trigger : trigger_info -> Term.t list -> t -> t
  val query : t -> uf -> (trigger_info * gsubst list) list

end

module Make (X : X) : S with type uf = X.t
