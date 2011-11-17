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
  | Elem s -> fprintf fmt "%s" (Hstring.view s)
  | Access (a, i) -> fprintf fmt "%s[%s]" (Hstring.view a) (Hstring.view i)
  | Arith (x, op, i) -> fprintf fmt "@[%s %s %d@]" (Hstring.view x) (op_arith op) i

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
  | a::l -> fprintf fmt "%a %s@\n%a" print_atom a sep (print_atoms sep) l

let print_cube fmt sa = 
  fprintf fmt "@[%a@]" (print_atoms "&&") (SAtom.elements sa)

let print_system fmt s = print_cube fmt (snd s.t_unsafe)

let print_unsafe fmt s = 
  fprintf fmt "  Unsafe property (from %a):@.        %a@."
    (fun fmt ->
       List.iter (fun (l, _) -> 
		    fprintf fmt "[%s]" (Hstring.view l))) s.t_from
    print_system s


let print_node fmt s =
  List.iter (fun (l, _) -> fprintf fmt "[%s]" (Hstring.view l)) s.t_from 
