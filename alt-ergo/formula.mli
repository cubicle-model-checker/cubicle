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

type lemma =
    { qvars: Symbols.Set.t;  (* toplevel quantified variables *)
      triggers : (Term.t list * Literal.LT.t option) list; (* multi-triggers *)
      main : t;  (* the main lemma's formula *)
      name : string; }
      
and llet = {
  let_var: Symbols.t;
  let_subst : Term.subst;
  let_term : Term.t;
  let_f : t;
}

and skolem = {
  sko_subst : Term.subst;
  sko_f : t;
}

and view = 
    Unit of t*t  (* unit clauses *)
  | Clause of t*t      (* a clause (t1 or t2) *)
  | Literal of Literal.LT.t   (* an atom *)
  | Lemma of lemma   (* a lemma *)
  | Skolem of skolem  (* lazy substitution *)
  | Let of llet (* a binding of a term *)

val mk_not : t -> t
val mk_and : t -> t -> int -> t
val mk_or : t -> t -> int -> t
val mk_imp : t -> t -> int -> t
val mk_if : Term.t -> t -> t -> int -> t
val mk_iff : t -> t -> int -> t
val mk_lit : Literal.LT.t -> int -> t
val mk_forall : Term.Set.t -> Term.Set.t -> 
  (Term.t list * Literal.LT.t option) list -> t ->
  string -> int -> t
val mk_exists : Term.Set.t -> Term.Set.t -> 
  (Term.t list * Literal.LT.t option) list -> t ->
  string -> int -> t
val mk_let : Term.Set.t -> Symbols.t -> Term.t -> t -> int -> t

val add_label : Hstring.t -> t -> unit
val label : t -> Hstring.t

val view : t -> view
val size : t -> int
val id : t -> int

val print : Format.formatter -> t -> unit

val terms : t -> Term.Set.t
val free_vars : t -> Symbols.Set.t

val apply_subst : Term.subst -> t -> t 

val compare : t -> t -> int
val equal : t -> t -> bool
val hash : t -> int

module Set : Set.S with type elt = t
module Map : Map.S with type key = t


val simplify : t -> t
val cnf : t -> Literal.LT.t list list
val dnf : t -> Literal.LT.t list list
