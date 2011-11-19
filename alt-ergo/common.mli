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

val report : Format.formatter -> error -> unit
val error : error -> loc -> 'a
val warning : error -> loc -> 'a

val print_term : Format.formatter -> ('a tterm, 'a) annoted -> unit
val print_formula : Format.formatter -> ('a tform, 'a) annoted 
  -> unit
val print_binders : Format.formatter -> (Symbols.t * Ty.t) list -> unit
val print_triggers : 
  Format.formatter -> (('a tterm, 'a) annoted list) list  -> unit
val fresh_string : unit -> string

val fake_eq : Symbols.t
val fake_neq : Symbols.t
val fake_lt : Symbols.t
val fake_le : Symbols.t
