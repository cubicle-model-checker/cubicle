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

open Why_ptree
open Format

type error = 
  | BitvExtract of int*int
  | BitvExtractRange of int*int
  | ClashType of string
  | ClashLabel of string * string
  | ClashParam of string
  | TypeDuplicateVar of string
  | UnboundedVar of string
  | UnknownType of string
  | WrongArity of string * int
  | SymbAlreadyDefined of string 
  | SymbUndefined of string
  | NotAPropVar of string
  | NotAPredicate of string
  | Unification of Ty.t * Ty.t
  | ShouldBeApply of string
  | WrongNumberofArgs of string
  | ShouldHaveType of Ty.t * Ty.t
  | ShouldHaveTypeIntorReal of Ty.t
  | ShouldHaveTypeInt of Ty.t
  | ShouldHaveTypeBitv of Ty.t
  | ArrayIndexShouldHaveTypeInt
  | ShouldHaveTypeArray
  | ShouldHaveTypeRecord of Ty.t
  | ShouldBeARecord
  | ShouldHaveLabel of string * string
  | NoLabelInType of Hstring.t * Ty.t
  | ShouldHaveTypeProp
  | NoRecordType of Hstring.t
  | DuplicateLabel of Hstring.t
  | WrongLabel of Hstring.t * Ty.t
  | WrongNumberOfLabels
  | Notrigger 
  | CannotGeneralize
  | SyntaxError

exception Error of error * loc
exception Warning of error * loc

let report fmt = function
  | BitvExtract(i,j) -> 
      fprintf fmt "bitvector extraction malformed (%d>%d)" i j
  | BitvExtractRange(n,j) -> 
      fprintf fmt "extraction out of range (%d>%d)" j n
  | ClashType s -> 
      fprintf fmt "the type %s is already defined" s
  | ClashParam s -> 
      fprintf fmt "parameter %s is bound twice" s
  | ClashLabel (s,t) -> 
      fprintf fmt "the label %s already appears in type %s" s t
  | CannotGeneralize -> 
      fprintf fmt "cannot generalize the type of this expression"
  | TypeDuplicateVar s ->
      fprintf fmt "duplicate type variable %s" s
  | UnboundedVar s ->
      fprintf fmt "unbounded variable %s" s
  | UnknownType s -> 
      fprintf fmt "unknown type %s" s
  | WrongArity(s,n) -> 
      fprintf fmt "the type %s has %d arguments" s n
  | SymbAlreadyDefined s -> 
      fprintf fmt "the symbol %s is already defined" s
  | SymbUndefined s -> 
      fprintf fmt "undefined symbol %s" s
  | NotAPropVar s -> 
      fprintf fmt "%s is not a propositional variable" s
  | NotAPredicate s -> 
      fprintf fmt "%s is not a predicate" s
  | Unification(t1,t2) ->
      fprintf fmt "%a and %a cannot be unified" Ty.print t1 Ty.print t2
  | ShouldBeApply s -> 
      fprintf fmt "%s is a function symbol, it should be apply" s
  | WrongNumberofArgs s ->
      fprintf fmt "Wrong number of arguments when applying %s" s
  | ShouldHaveType(ty1,ty2) ->
      fprintf fmt "this expression has type %a but is here used with type %a"
	Ty.print ty1 Ty.print ty2
  | ShouldHaveTypeBitv t -> 
      fprintf fmt "this expression has type %a but it should be a bitvector"
	Ty.print t
  | ShouldHaveTypeIntorReal t ->
      fprintf fmt 
	"this expression has type %a but it should have type int or real"
	Ty.print t
  | ShouldHaveTypeInt t ->
      fprintf fmt 
	"this expression has type %a but it should have type int"
	Ty.print t
  | ShouldHaveTypeArray ->
      fprintf fmt "this expression should have type farray"
  | ShouldHaveTypeRecord t ->
      fprintf fmt "this expression has type %a but it should have a record type"
	Ty.print t
  | ShouldBeARecord ->
      fprintf fmt "this expression should have a record type"
  | ShouldHaveLabel (s, a) ->
      fprintf fmt "this expression has type %s which has no label %s" s a
  | NoLabelInType (lb, ty) ->
      fprintf fmt "no label %s in type %a" (Hstring.view lb) Ty.print ty
  | ShouldHaveTypeProp -> 
      fprintf fmt "this expression should have type prop"
  | NoRecordType s ->
      fprintf fmt "no record type has label %s" (Hstring.view s)
  | DuplicateLabel s -> 
      fprintf fmt "label %s is defined several times" (Hstring.view s)
  | WrongLabel (s, ty) -> 
      fprintf fmt "wrong label %s in type %a" (Hstring.view s) Ty.print ty
  | WrongNumberOfLabels -> 
      fprintf fmt "wrong number of labels"
  | ArrayIndexShouldHaveTypeInt -> 
      fprintf fmt "index of arrays should hava type int"
  | Notrigger -> 
      fprintf fmt "No trigger for this lemma"
  | SyntaxError -> 
      fprintf fmt "syntax error"

let error e l = raise (Error(e,l))
let warning e l = raise (Warning(e,l))

let rec print_term fmt t = match t.c.tt_desc with
  | TTconst Ttrue -> 
      fprintf fmt "true"
  | TTconst Tfalse -> 
      fprintf fmt "false"
  | TTconst Tvoid -> 
      fprintf fmt "void"
  | TTconst (Tint n) -> 
      fprintf fmt "%s" n
  | TTconst (Treal n) -> 
      fprintf fmt "%s" (Num.string_of_num n)
  | TTconst Tbitv s -> 
      fprintf fmt "%s" s
  | TTvar s -> 
      fprintf fmt "%a" Symbols.print s
  | TTapp(s,l) -> 
      fprintf fmt "%a(%a)" Symbols.print s print_term_list l
  | TTinfix(t1,s,t2) -> 
      fprintf fmt "%a %a %a" print_term t1 Symbols.print s print_term t2
  | TTprefix (s, t') ->
      fprintf fmt "%a %a" Symbols.print s print_term t'
  | TTget (t1, t2) ->
      fprintf fmt "%a[%a]" print_term t1 print_term t2
  | TTset (t1, t2, t3) ->
      fprintf fmt "%a[%a<-%a]" print_term t1 print_term t2 print_term t3
  | TTextract (t1, t2, t3) ->
      fprintf fmt "%a^{%a,%a}" print_term t1 print_term t2 print_term t3
  | TTconcat (t1, t2) ->
      fprintf fmt "%a @ %a" print_term t1 print_term t2
  | TTdot (t1, s) ->
      fprintf fmt "%a.%s" print_term t1 (Hstring.view s)
  | TTrecord l ->
      fprintf fmt "{ ";
      List.iter 
	(fun (s, t) -> fprintf fmt "%s = %a" (Hstring.view s) print_term t) l;
      fprintf fmt " }"
  | TTlet (s, t1, t2) ->
      fprintf fmt "let %a=%a in %a" Symbols.print s print_term t1 print_term t2

and print_term_list fmt = List.iter (fprintf fmt "%a," print_term)

let print_atom fmt a = 
    match a.c with
      | TAtrue ->
	  fprintf fmt "True"
      | TAfalse ->
	  fprintf fmt "True"
      | TAeq [t1; t2] -> 
	  fprintf fmt "%a = %a" print_term t1 print_term t2
      | TAneq [t1; t2] ->
	  fprintf fmt "%a <> %a" print_term t1 print_term t2
      | TAle [t1; t2] ->
	  fprintf fmt "%a <= %a" print_term t1 print_term t2
      | TAlt [t1; t2] ->
	  fprintf fmt "%a < %a" print_term t1 print_term t2
      | TApred t -> 
	  print_term fmt t
      | TAbuilt(s, l) ->
	  fprintf fmt "%s(%a)" (Hstring.view s) print_term_list l
      | _ -> assert false

let string_of_op = function
  | OPand -> "and"
  | OPor -> "or"
  | OPimp -> "->"
  | OPiff -> "<->"
  | _ -> assert false

let print_binder fmt (s, t) =
  fprintf fmt "%a:%a" Symbols.print s Ty.print t

let print_binders fmt l = 
  List.iter (fun c -> fprintf fmt "%a, " print_binder c) l

let print_triggers fmt = List.iter (fprintf fmt "%a | " print_term_list)
 
let rec print_formula fmt f = 
  match f.c with
  | TFatom a -> 
      print_atom fmt a
  | TFop(OPnot, [f]) -> 
      fprintf fmt "not %a" print_formula f
  | TFop(OPif(t), [f1;f2]) -> 
      fprintf fmt "if %a then %a else %a" 
	print_term t print_formula f1 print_formula f2
  | TFop(op, [f1; f2]) -> 
      fprintf fmt "%a %s %a" print_formula f1 (string_of_op op) print_formula f2

  | TFforall {qf_bvars = l; qf_triggers = t; qf_form = f} -> 
      fprintf fmt "forall %a [%a]. %a" 
	print_binders l print_triggers t print_formula f
  | _ -> assert false

and print_form_list fmt = List.iter (fprintf fmt "%a" print_formula)

let fresh_string = 
  let cpt = ref 0 in
  fun () ->
    incr cpt;
    "!k" ^ (string_of_int !cpt)

let fake_eq =  Symbols.name "@eq"
let fake_neq =  Symbols.name "@neq"
let fake_lt =  Symbols.name "@lt"
let fake_le =  Symbols.name "@le"

