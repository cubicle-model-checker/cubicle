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

(* Captures the output and exit status of a unix command : aux func*)
let syscall cmd =
  let ic, oc = Unix.open_process cmd in
  let buf = Buffer.create 16 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  let _ = Unix.close_process (ic, oc) in
  (Buffer.contents buf)

let rec remove_trailing_whitespaces_end str =
  if String.length str > 0 && 
    (str.[String.length str - 1] = '\n' 
    || str.[String.length str - 1] = ' '
      || str.[String.length str - 1] = '\t')  then
    remove_trailing_whitespaces_end (String.sub str 0 (String.length str - 1))
  else str

(* Set width of pretty printing boxes to number of columns *)
let _ =
  try
    let scol = syscall "tput cols" in
    set_margin (int_of_string (remove_trailing_whitespaces_end scol));
  with Not_found | Failure _ -> ()


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

let print_array fmt a =
  fprintf fmt "@[%a@]" (print_atoms "&&") (Array.to_list a)

let print_system fmt s = print_cube fmt (snd s.t_unsafe)

let rec print_args fmt = function
  | [] -> ()
  | [a] -> fprintf fmt "%s" (Hstring.view a)
  | a::r -> fprintf fmt "%s, %a" (Hstring.view a) print_args r

let print_unsafe fmt s = 
  fprintf fmt "  Unsafe property (from %aunsafe):@.        %a@."
    (fun fmt ->
       List.iter 
	 (fun (l, args, _) -> 
	   fprintf fmt "%s(%a) -> " 
	     (Hstring.view l) print_args args)) s.t_from
    print_system s


let print_node fmt s =
  (* fprintf fmt "(%d -> %d) " s.t_nb_father s.t_nb; *)
  List.iter (fun (l, args, _) -> fprintf fmt "%s(%a) ->@ " 
    (Hstring.view l) print_args args) s.t_from;
  fprintf fmt "unsafe"
