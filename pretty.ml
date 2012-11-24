(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                  Universite Paris-Sud 11                               *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

open Format
open Ast
open Atom
open Options

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

let print_const fmt = function
  | ConstInt n | ConstReal n -> fprintf fmt "%s" (Num.string_of_num n)
  | ConstName n -> fprintf fmt "%a" Hstring.print n

let print_cs fmt cs =
  MConst.iter 
    (fun c i ->
       fprintf fmt " %s %a" 
	 (if i = 1 then "+" else if i = -1 then "-" 
	  else if i < 0 then "- "^(string_of_int (abs i)) 
	  else "+ "^(string_of_int (abs i)))
	 print_const c) cs

let rec print_term fmt = function
  | Const cs -> print_cs fmt cs
  | Elem (s, _) -> fprintf fmt "%a" Hstring.print s
  | Access (a, i, _) -> fprintf fmt "%a[%a]" Hstring.print a Hstring.print i
  | Arith (x, cs) -> 
      fprintf fmt "@[%a%a@]" print_term x print_cs cs

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
  | [a] ->
    let s = Hstring.view a in
    let s = if dmcmt then (String.sub s 1 (String.length s - 1)) else s in
    if dmcmt then fprintf fmt "_%s" s
    else fprintf fmt "%s" s
  | a::r -> 
    let s = Hstring.view a in
    let s = if dmcmt then (String.sub s 1 (String.length s - 1)) else s in
    if dmcmt then  fprintf fmt "_%s%a" s print_args r
    else  fprintf fmt "%s, %a" s print_args r

let rec print_subst fmt = function
  | [] -> ()
  | [x,y] ->
    fprintf fmt "%a -> %a" Hstring.print x Hstring.print y
  | (x,y)::r -> 
    fprintf fmt "%a -> %a, %a" Hstring.print x Hstring.print y print_subst r

let print_unsafe fmt s = 
  fprintf fmt "  Unsafe property (from %aunsafe):@.        %a@."
    (fun fmt ->
       List.iter 
	 (fun (tr, args, _) ->
	   if dmcmt then 
	     fprintf fmt "[%s%a]" (Hstring.view tr.tr_name) print_args args
	   else
	     fprintf fmt "%s(%a) -> " (Hstring.view tr.tr_name) print_args args
	 )) s.t_from
    print_system s

let rec print_atom_dot fmt = function
  | True -> fprintf fmt "true"
  | False -> fprintf fmt "false"
  | Comp (x, Eq,  Elem (n, Constr)) when Hstring.equal n htrue -> 
      fprintf fmt "%a" print_term x
  | Comp (x, Eq, Elem (n, Constr)) when  Hstring.equal n hfalse-> 
      fprintf fmt "!%a" print_term x
  | Comp (x, op, y) -> 
      fprintf fmt "%a %s %a" print_term x (op_comp op) print_term y
  | Ite (la, a1, a2) ->
      fprintf fmt "@[ite(%a,@ %a,@ %a)@]" 
	print_atoms_dot (SAtom.elements la) 
	print_atom_dot a1 print_atom_dot a2

and print_atoms_dot fmt = function
  | [] -> ()
  | [a] -> print_atom_dot fmt a
  | a::l -> fprintf fmt "%a\\n%a" print_atom_dot a print_atoms_dot l

let print_cube_dot fmt sa = 
  fprintf fmt "@[%a@]" print_atoms_dot (SAtom.elements sa)

let print_system_dot fmt s = 
  if verbose = 3 then print_cube_dot fmt (snd s.t_unsafe)
  else fprintf fmt "%d" s.t_nb

let print_node fmt s =
  if dot then
    begin
      if List.length s.t_from  = 0 then
	if s.t_nb = 0 then
	  fprintf fmt "%d [label=\"%a\", color = green, style=filled];" 
	    s.t_nb print_system_dot s
	else 
	  fprintf fmt "%d [label=\"%a\"];" s.t_nb print_system_dot s
      else
	let (tr, args, _)= List.hd s.t_from in 
	fprintf fmt "%d -> %d [label=\"%s(%a)\"];@." 
	  s.t_nb_father s.t_nb (Hstring.view tr.tr_name) print_args args;
	if s.t_nb = 0 then
	  fprintf fmt "%d [label=\"%a\", color = green, style = filled];" 
	    s.t_nb print_system_dot s
	else 
	  fprintf fmt "%d [label=\"%a\"];" s.t_nb print_system_dot s
    end
  else
    begin
(*      fprintf fmt "@.%a" print_system s*)
     List.iter 
       (fun (tr, args, _) ->
	  if dmcmt then 
	    fprintf fmt "[%s%a]" (Hstring.view tr.tr_name) print_args args
	  else 
	    fprintf fmt "%s(%a) ->@ " (Hstring.view tr.tr_name) print_args args
       ) s.t_from;
     if dmcmt then fprintf fmt "[0]  " else fprintf fmt "unsafe"
   end

let print_dead_node fmt (s, db) =
  if dot && verbose > 0 then
    begin
      if List.length s.t_from  = 0 then
	if verbose = 1 then
	  if s.t_nb = 0 then 
	    fprintf fmt "%d [color = green, style = filled];" s.t_nb
	  else 
	    fprintf fmt "%d [color = red];" s.t_nb
	else
	  begin
	    (if s.t_nb = 0 then
	      fprintf fmt 
		"%d [label=\"%a\" , color = green, style=filled];" 
		s.t_nb print_system_dot s
	    else 
	      fprintf fmt 
		"%d [label=\"%a\" color = red];" s.t_nb print_system_dot s);
	    if verbose >= 2 then 
	      begin
		fprintf fmt "@.";
		List.iter 
		  (fun d -> fprintf fmt " %d -> %d [style=dotted] @." 
		     s.t_nb d) db
	      end
	  end
      else
	let (tr, args, _) = List.hd s.t_from in 
	fprintf fmt "%d -> %d [label=\"%s(%a)\"];@." 
	  s.t_nb_father s.t_nb (Hstring.view tr.tr_name) print_args args;
	if verbose = 1 then 
	  if s.t_nb = 0 then
	    fprintf fmt "%d [label=\"\" , color=green, style = filled];" s.t_nb
	  else 
	    fprintf fmt "%d [label=\"\" color=red];" s.t_nb
	else
	  begin
	    fprintf fmt "%d [label=\"%a\" color=red];" 
	      s.t_nb print_system_dot s;
	    if verbose >= 2 then
	      begin
		fprintf fmt "@.";
		List.iter 
		  (fun d -> fprintf fmt " %d -> %d [style=dotted] @." 
		     s.t_nb d) db
	      end
	  end
    end

let print_verbose_node fmt s =
  if verbose = 0 then print_node fmt s else begin
    (* fprintf fmt "(%d -> %d) " s.t_nb_father s.t_nb; *)
    fprintf fmt " %a\n@." print_system s;
    List.iter 
      (fun (tr, args, s') ->
	 fprintf fmt "  %s(%a) -> %a\n@." (Hstring.view tr.tr_name) 
           print_args args print_system s'
      ) s.t_from;
    fprintf fmt "    = unsafe"
  end
