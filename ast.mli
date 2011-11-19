(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon, Universite Paris-Sud 11              *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

type op_comp = Eq | Lt | Le | Neq
type op_arith = Plus | Minus

type term = 
  | Const of int
  | Elem of Hstring.t
  | Access of Hstring.t * Hstring.t
  | Arith of Hstring.t * op_arith * int

val compare_term : term -> term -> int

type acc_eq = { a : Hstring.t; i: Hstring.t; e: term }

module rec Atom : sig
  type t =
    | True
    | False
    | Comp of term * op_comp * term
    | Ite of SAtom.t * t * t

  val compare : t -> t -> int
end 
and SAtom : Set.S with type elt = Atom.t

val alpha_args : Hstring.t list
val add : Atom.t -> SAtom.t -> SAtom.t
val svar : Hstring.t -> Hstring.t -> Hstring.t -> Hstring.t
val subst_term : (Hstring.t * Hstring.t) list -> term -> term
val subst_atom : (Hstring.t * Hstring.t) list -> Atom.t -> Atom.t
val subst_atoms : (Hstring.t * Hstring.t) list -> SAtom.t -> SAtom.t
val build_subst : Hstring.t list -> Hstring.t list -> 
  (Hstring.t * Hstring.t) list

module TimerSubset : Timer.S
module TimerApply  : Timer.S

module ArrayAtom : sig
  type t = Atom.t array
  val equal : t -> t -> bool
  val subset : t -> t -> bool
  val of_satom : SAtom.t -> t
  val union : t -> t -> t
  val apply_subst : (Hstring.t * Hstring.t) list -> t -> t
  val nb_diff : t -> t -> int
  val alpha : t -> Hstring.t list -> Hstring.t list * t
end

type update = {
  up_arr : Hstring.t;
  up_arg : Hstring.t;
  up_swts : (SAtom.t * term) list * term;
}

type transition = {
  tr_name : Hstring.t;
  tr_args : Hstring.t list;
  tr_reqs : SAtom.t;
  tr_ureq : (Hstring.t * SAtom.t) option;
  tr_assigns : (Hstring.t * term) list;
  tr_upds : update list;
  tr_nondets : Hstring.t list;
}

type elem = Hstring.t * (Hstring.t list)

type system = {
  globals : (Hstring.t * Hstring.t) list;
  arrays : (Hstring.t * (Hstring.t * Hstring.t)) list;
  elems : elem list;
  init : Hstring.t option * SAtom.t;
  invs : (Hstring.t list * SAtom.t) list;
  unsafe : Hstring.t list * SAtom.t;
  trans : transition list
}

(* Types AST *)

type sort = Glob | Arr | Constr | Var

val sort_of : (sort * AltErgo.Ty.t * AltErgo.Term.t) Hstring.H.t ->
  Hstring.t -> sort

type t_system = {
  t_from : (Hstring.t * t_system) list;
  t_env : (sort * AltErgo.Ty.t * AltErgo.Term.t) Hstring.H.t;
  t_init : Hstring.t option * SAtom.t;
  t_invs : (Hstring.t list * SAtom.t) list;
  t_unsafe : Hstring.t list * SAtom.t;
  t_arru : ArrayAtom.t;
  t_alpha : Hstring.t list * ArrayAtom.t;
  t_trans : transition list;
  mutable t_deleted : bool
}


