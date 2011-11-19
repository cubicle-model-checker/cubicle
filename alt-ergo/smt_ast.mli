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

type loc = Lexing.position * Lexing.position

type annot = string * string option
type binder = { var: string ; sort: string }

type term = { term: term_node; tloc: loc}
and term_node = 
  | Num of string
  | Rat of string
  | Var of string
  | Fun of string * term list 
  | Ite of formula * term * term
and formula = { formula : form_node; floc : loc }
and form_node =
    Flet of string * formula * formula 
  | Let of string * term * formula 
  | Forall of binder list * formula
  | Exists of binder list * formula
  | And of formula list 
  | Or of formula list 
  | Not of formula
  | Implies of formula * formula
  | Xor of formula list 
  | Iff of formula list 
  | Fite of formula * formula * formula 
  | True
  | False
  | Fvar of string
  | Distinct of term list 
  | Equals of term list
  | Pred of string * term list 

type pred_sig = { 
  pname: string;  
  pargs: (loc * string) list; }

type fun_sig = {
  fname: string;
  fargs: (loc * string) list;
  fres: loc * string }

type ptheory_attrib =
    Tsorts of (loc *string) list
  | Funs of (loc * fun_sig) list 
  | Preds of (loc * pred_sig) list
  | Definition of string 
  | Axioms of formula list
  | Tcomment

type ptheory = string * ptheory_attrib list

type plogic_attrib = Ltheory of string | Lcomment

type plogic = string * plogic_attrib list

type status = Sat | Unsat | Unknown

type pbench_attrib = 
    Pblogic of string
  | Pbstatus of status
  | Pbextr_sorts of (loc * string) list
  | Pbextr_funs of (loc * fun_sig) list
  | Pbextr_preds of (loc *pred_sig) list
  | Pbformula of loc * formula 
  | Pbassumption of loc * formula 
  | Pbrewriting of loc * formula list
  | Pannotation

type pbench = string * pbench_attrib list * status
	  






