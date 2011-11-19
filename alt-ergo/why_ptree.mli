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

type constant =
  | ConstBitv of string
  | ConstInt of string
  | ConstReal of Num.num
  | ConstTrue
  | ConstFalse
  | ConstVoid

type pp_infix = 
  | PPand | PPor | PPimplies | PPiff 
  | PPlt | PPle | PPgt | PPge | PPeq | PPneq
  | PPadd | PPsub | PPmul | PPdiv | PPmod
	  
type pp_prefix = 
  | PPneg | PPnot

type ppure_type =
  | PPTint
  | PPTbool
  | PPTreal
  | PPTunit
  | PPTbitv of int
  | PPTvarid of string * loc
  | PPTexternal of ppure_type list * string * loc
  
type lexpr = 
  { pp_loc : loc; pp_desc : pp_desc }

and pp_desc =
  | PPvar of string
  | PPapp of string * lexpr list
  | PPdistinct of lexpr list
  | PPconst of constant
  | PPinfix of lexpr * pp_infix * lexpr
  | PPprefix of pp_prefix * lexpr
  | PPget of lexpr * lexpr
  | PPset of lexpr * lexpr * lexpr
  | PPdot of lexpr * string
  | PPrecord of (string * lexpr) list
  | PPwith of lexpr * (string * lexpr) list
  | PPextract of lexpr * lexpr * lexpr
  | PPconcat of lexpr * lexpr
  | PPif of lexpr * lexpr * lexpr
  | PPforall of string list * ppure_type * lexpr list list * lexpr
  | PPexists of string list * ppure_type * lexpr
  | PPnamed of string * lexpr
  | PPlet of string * lexpr * lexpr

(* Declarations. *)

type plogic_type =
  | PPredicate of ppure_type list
  | PFunction of ppure_type list * ppure_type

type name_kind = Symbols.name_kind

type body_type_decl = 
  | Record of (string * ppure_type) list  (* lbl : t *)
  | Enum of string list
  | Abstract

type decl = 
  | Axiom of loc * string * lexpr
  | Rewriting of loc * string * lexpr list
  | Goal of loc * string * lexpr
  | Logic of loc * name_kind * string list * plogic_type
  | Predicate_def of loc * string * (loc * string * ppure_type) list * lexpr
  | Function_def 
      of loc * string * (loc * string * ppure_type) list * ppure_type * lexpr
  | TypeDecl of loc * string list * string * body_type_decl

type file = decl list

(*** typed ast *)

type ('a, 'b) annoted =
    { c : 'a;
      annot : 'b }

type tconstant =
  | Tint of string
  | Treal of Num.num
  | Tbitv of string
  | Ttrue
  | Tfalse
  | Tvoid

type 'a tterm = 
    { tt_ty : Ty.t; tt_desc : 'a tt_desc }
and 'a tt_desc = 
  | TTconst of tconstant
  | TTvar of Symbols.t
  | TTinfix of ('a tterm, 'a) annoted * Symbols.t * ('a tterm, 'a) annoted
  | TTprefix of Symbols.t * ('a tterm, 'a) annoted 
  | TTapp of Symbols.t * ('a tterm, 'a) annoted list
  | TTget of ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTset of 
      ('a tterm, 'a) annoted * ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTextract of 
      ('a tterm, 'a) annoted * ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTconcat of ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTdot of ('a tterm, 'a) annoted * Hstring.t
  | TTrecord of (Hstring.t * ('a tterm, 'a) annoted) list
  | TTlet of Symbols.t * ('a tterm, 'a) annoted * ('a tterm, 'a) annoted

type 'a tatom = 
  | TAtrue
  | TAfalse
  | TAeq of ('a tterm, 'a) annoted list
  | TAdistinct of ('a tterm, 'a) annoted list
  | TAneq of ('a tterm, 'a) annoted list
  | TAle of ('a tterm, 'a) annoted list
  | TAlt of ('a tterm, 'a) annoted list
  | TApred of ('a tterm, 'a) annoted
  | TAbuilt of Hstring.t * ('a tterm, 'a) annoted list

type 'a oplogic = 
    OPand |OPor | OPimp | OPnot | OPiff 
  | OPif of ('a tterm, 'a) annoted

type 'a quant_form = {       
  (* quantified variables that appear in the formula *)
  qf_bvars : (Symbols.t * Ty.t) list ;
  qf_upvars : (Symbols.t * Ty.t) list ;
  qf_triggers : ('a tterm, 'a) annoted list list ;
  qf_form : ('a tform, 'a) annoted
}

and 'a tform =
  | TFatom of ('a tatom, 'a) annoted
  | TFop of 'a oplogic * (('a tform, 'a) annoted) list
  | TFforall of 'a quant_form
  | TFexists of 'a quant_form
  | TFlet of (Symbols.t * Ty.t) list * Symbols.t * 
      ('a tterm, 'a) annoted * ('a tform, 'a) annoted
  | TFnamed of Hstring.t * ('a tform, 'a) annoted


type 'a rwt_rule = {
  rwt_vars : (Symbols.t * Ty.t) list;
  rwt_left : 'a;
  rwt_right : 'a
}

type 'a tdecl = 
  | TAxiom of loc * string * ('a tform, 'a) annoted
  | TRewriting of loc * string * (('a tterm, 'a) annoted rwt_rule) list
  | TGoal of loc * string * ('a tform, 'a) annoted
  | TLogic of loc * string list * plogic_type
  | TPredicate_def of 
      loc * string * (string * ppure_type) list * ('a tform, 'a) annoted
  | TFunction_def of 
      loc * string * (string * ppure_type) list * 
	ppure_type * ('a tform, 'a) annoted
  | TTypeDecl of loc * string list * string * body_type_decl


(* Sat entry *)

type sat_decl_aux = 
  | Assume of Formula.t * bool 
  | PredDef of Formula.t
  | RwtDef of (Term.t rwt_rule) list
  | Query of string * Formula.t * Literal.LT.t list

type sat_tdecl = {
  st_loc : loc;
  st_decl : sat_decl_aux
}
