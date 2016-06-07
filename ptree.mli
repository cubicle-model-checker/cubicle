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


open Types
open Util


type hstr_info = { hstr : Hstring.t ; hstr_i : info }

type var = hstr_info

type arr = { arr_n : hstr_info; arr_arg : var list}

type array = arr option

type term_info = Term.t * info 

type term =
  | TVar of var * info
  | TTerm of term_info * array 
    
type atom =
  | AVar of var * info
  | AAtom of Atom.t * info 
  | AEq of term * term * info 
  | ANeq of term * term * info 
  | ALe of term * term * info
  | ALt of term * term * info
    
type formula =
  | PAtom of atom 
  | PNot of info * formula * info
  | PAnd of formula list * info
  | POr of formula list * info 
  | PImp of formula * formula * info 
  | PEquiv of formula * formula * info 
  | PIte of formula * formula * formula * info
  | PForall of var list * formula * info  
  | PExists of var list * formula * info  
  | PForall_other of var list * formula * info 
  | PExists_other of var list * formula * info


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





type pup_psw = {pup_form : cformula ; pup_t : term ; pup_i : info}

type pswts  =  (pup_psw list * info)

type pglob_update = PUTerm of (term * info) | PUCase of (pswts)

type pup_arg = { arg_v : var list ; arg_i : info }

type pupdate = {
  pup_loc : info;
  pup_arr : hstr_info;
  pup_arg : var list * info;
  pup_swts : pswts ;
  pup_info : (Hstring.t * var list * term)  option;
}

type ptrans_pupdate = { t_pup_l : pupdate list ; t_pup_i : info}

type ptrans_req = { r_f : cformula ; r_i : info }

type ptrans_assign = { a_n : hstr_info; a_p : pglob_update ; a_i : info } 

type ptrans_nondet = { n_n : hstr_info ; n_i : info}

type ptrans_s = { ptr_assigns : ptrans_assign list; ptr_upds : ptrans_pupdate ; 
                  ptr_nondets : ptrans_nondet list; ptr_i : info}

type ptransition = {
  mutable ptr_name : hstr_info ;
  ptr_args : hstr_info list;
  ptr_reqs : ptrans_req ;
  ptr_s : ptrans_s;
  ptr_loc : info;
}


type ptr_type_constructors =  hstr_info * hstr_info list 
  
(* type smt_info = { smt : Smt.Type.t ; smt_i : info} *)

type psystem = {
  pglobals : (info * hstr_info * hstr_info) list;
  pconsts : (info * hstr_info * hstr_info) list;
  parrays : (info * hstr_info  * (hstr_info  list * hstr_info)) list;
  ptype_defs : (info * ptr_type_constructors) list;
  pinit : info *  hstr_info list * cformula;
  pinvs : (info * hstr_info list * cformula) list;
  punsafe : (info * hstr_info list * cformula) list;
  ptrans : ptransition list;
}



type pdecl =
  | PInit of (info * hstr_info list * cformula)
  | PInv of (info * hstr_info list * cformula)
  | PUnsafe of (info * hstr_info list * cformula)
  | PTrans of ptransition
  | PFun

val add_fun_def : Hstring.t-> Smt.Type.t list -> formula -> unit

val app_fun : Hstring.t -> term_or_formula list -> formula

(* val encode_psystem : psystem -> Ast.system *)

val psystem_of_decls:
  pglobals : (info * hstr_info * hstr_info) list ->
  pconsts : (info * hstr_info * hstr_info) list ->
  parrays : (info * hstr_info  * (hstr_info list * hstr_info)) list ->
  ptype_defs : (info * ptr_type_constructors) list ->
  pdecl list -> psystem
