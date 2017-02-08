(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2015                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)


open Cubtypes
open Util

type term =
  | TVar of Variable.t
  | TTerm of Term.t
    
type atom =
  | AVar of Variable.t
  | AAtom of Atom.t
  | ABinop of term * Cubtypes.op_comp * term

type formula =
  | PAtom of atom
  | PNot of formula
  | PAnd of formula list
  | POr of formula list
  | PImp of formula * formula
  | PEquiv of formula * formula
  | PIte of formula * formula * formula
  | PForall of Variable.t list * formula
  | PExists of Variable.t list * formula
  | PForall_other of Variable.t list * formula
  | PExists_other of Variable.t list * formula
  | PCount of Variable.t list * formula * op_comp * int MConst.t

type term_or_formula = PF of formula | PT of term


type cformula = formula
  
(* type atom = [ PAtom of Atom.t ] *)

(* type clause = [atom | POr of atom list] *)

(* type conj = [atom | PAnd of atom list] *)

(* type cnf = [clause | PAnd of clause list] *)

(* type dnf = [conj | POr of conj list] *)

(* type uguard = [PForall_other of Variable.t list * dnf] *)

(* type guard = [dnf | uguard] *)

(* type prenex_forall_dnf = [dnf | PForall of Variable.t list * dnf] *)

(* type cube = [conj | PExists of Variable.t list * conj] *)


type pswts = (cformula * term) list

type pglob_update = PUTerm of term | PUCase of pswts

type pupdate = {
  pup_loc : loc;
  pup_arr : Hstring.t;
  pup_arg : Variable.t list;
  pup_swts : pswts;
}

type ptransition = {
  ptr_name : Hstring.t;
  ptr_args : Variable.t list;
  ptr_reqs : cformula;
  ptr_assigns : (Hstring.t * pglob_update) list;
  ptr_upds : pupdate list;
  ptr_nondets : Hstring.t list;
  ptr_loc : loc;
}

type pregexp = 
    | PEpsilon 
    | PChar of Hstring.t * Hstring.t list
    | PUnion of pregexp list
    | PConcat of pregexp list
    | PStar of pregexp
    | PPlus of pregexp
    | POption of pregexp

type psystem = {
  pglobals : (loc * Hstring.t * Smt.Type.t) list;
  pconsts : (loc * Hstring.t * Smt.Type.t) list;
  parrays : (loc * Hstring.t * (Smt.Type.t list * Smt.Type.t)) list;
  ptype_defs : (loc * Ast.type_constructors) list;
  pinit : loc * Variable.t list * cformula;
  pinvs : (loc * Variable.t list * cformula) list;
  punsafe : (loc * Variable.t list * cformula) list;
  ptrans : ptransition list;
  pmetatrans : ptransition list;
  punivtrans : ptransition list;
  phidetrans : Hstring.t list;
  pregexps : pregexp list;
}


type pdecl =
  | PInit of (loc * Variable.t list * cformula)
  | PInv of (loc * Variable.t list * cformula)
  | PUnsafe of (loc * Variable.t list * cformula)
  | PTrans of ptransition
  | PMetaTrans of ptransition
  | PUnivTrans of ptransition
  | PHideTrans of Hstring.t list
  | PFun
  | PRegExp of pregexp


val add_fun_def : Hstring.t -> Variable.t list -> formula -> unit

val app_fun : Hstring.t -> term_or_formula list -> formula

val encode_psystem : psystem -> Ast.system

val psystem_of_decls:
  pglobals : (loc * Hstring.t * Smt.Type.t) list ->
  pconsts : (loc * Hstring.t * Smt.Type.t) list ->
  parrays : (loc * Hstring.t * (Smt.Type.t list * Smt.Type.t)) list ->
  ptype_defs : (loc * Ast.type_constructors) list ->
  pdecl list -> psystem

val get_rnumber : unit ->  int
