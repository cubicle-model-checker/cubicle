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
  | Elem of string 
  | Access of string * string 
  | Arith of string * op_arith * int

type acc_eq = { a : string; i: string; e: term }

module rec Atom : sig
  type t =
    | True
    | False
    | Comp of term * op_comp * term
    | Ite of SAtom.t * t * t

  val compare : t -> t -> int
end 
and SAtom : Set.S with type elt = Atom.t

val add : Atom.t -> SAtom.t -> SAtom.t
val svar : string -> string -> string -> string
val subst_term : (string * string) list -> term -> term
val subst_atom : (string * string) list -> Atom.t -> Atom.t
val subst_atoms : (string * string) list -> SAtom.t -> SAtom.t

type update = {
  up_arr : string;
  up_arg : string;
  up_swts : (SAtom.t * term) list * term;
}

type transition = {
  tr_name : string;
  tr_args : string list;
  tr_reqs : SAtom.t;
  tr_ureq : (string * SAtom.t) option;
  tr_assigns : (string * term) list;
  tr_upds : update list;
  tr_nondets : string list;
}

type elem = string * (string list)

type system = {
  globals : (string * string) list;
  arrays : (string * (string * string)) list;
  elems : elem list;
  init : string option * SAtom.t;
  invs : (string list * SAtom.t) list;
  unsafe : string list * SAtom.t;
  trans : transition list
}

(* Types AST *)

open AltErgo

type sort = Glob | Arr | Constr | Var

type t_system = {
  t_from : (string * SAtom.t) list;
  t_env : (string, (sort * Ty.t * Term.t)) Hashtbl.t;
  t_init : string option * SAtom.t;
  t_invs : (string list * SAtom.t) list;
  t_unsafe : string list * SAtom.t;
  t_trans : transition list
}



