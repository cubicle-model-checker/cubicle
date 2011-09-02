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

open Format
open Ast
open Atom

module AE = AltErgo

let op_comp = function Eq -> "=" | Lt -> "<" | Le -> "<=" | Neq -> "<>"
let op_arith = function Plus -> "+" | Minus -> "-"

let rec print_strings fmt = function
  | [] -> ()
  | [s] -> fprintf fmt "%s" s
  | s :: l -> fprintf fmt "%s %a" s print_strings l

let rec print_term fmt = function
  | Const i -> fprintf fmt "%d" i
  | Elem s -> fprintf fmt "%s" s
  | Access (a, i) -> fprintf fmt "%s[%s]" a i
  | Arith (x, op, i) -> fprintf fmt "@[%s %s %d@]" x (op_arith op) i 

let rec print_atom fmt = function
  | True -> fprintf fmt "true"
  | False -> fprintf fmt "false"
  | Comp (x, op, y) -> 
      fprintf fmt "%a %s %a" print_term x (op_comp op) print_term y
  | Ite (la, a1, a2) ->
      fprintf fmt "@[ite(%a,@ %a,@ %a)@]" 
	(print_atoms "&&") (SAtom.elements la) print_atom a1 print_atom a2

and print_atoms sep fmt = function
  | [] -> ()
  | [a] -> print_atom fmt a
  | a::l -> fprintf fmt "@[%a %s@ %a@]" print_atom a sep (print_atoms sep) l

let print_unsafe fmt sa = print_atoms "&&" fmt (SAtom.elements sa)

let print_system fmt s = 
  (*List.iter 
    (fun ini -> 
       match ini with
	 | Array (a, e) ->
	     fprintf fmt "@.  Init : forall i. %a[i]=%a &&@." 
	       AE.Term.print a AE.Term.print e
	 | Global (g, e) ->
	     fprintf fmt "@.  Init :  %a=%a &&@." 
	       AE.Term.print g AE.Term.print e ) 
    s.t_init;*)
  fprintf fmt "  Unsafe property (from %s):@.%a@."
    s.t_from print_unsafe (snd s.t_unsafe)

