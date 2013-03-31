(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2013                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
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
let vt_width =
  try
    let scol = syscall "tput cols" in
    let w = int_of_string (remove_trailing_whitespaces_end scol) in
    set_margin w;
    w
  with Not_found | Failure _ -> 80



type style =
  | User of int
  | Normal
  | Bold
  | Bold_off
  | Dim
  | Underline
  | Underline_off
  | Inverse
  | Inverse_off
  | Blink_off
  | FG_Black
  | FG_Red
  | FG_Green
  | FG_Yellow
  | FG_Blue
  | FG_Magenta
  | FG_Cyan
  | FG_Gray
  | FG_Default
  | BG_Black
  | BG_Red
  | BG_Green
  | BG_Yellow
  | BG_Blue
  | BG_Magenta
  | BG_Cyan
  | BG_Gray
  | BG_Default
  | FG_Black_B
  | FG_Red_B
  | FG_Green_B
  | FG_Yellow_B
  | FG_Blue_B
  | FG_Magenta_B
  | FG_Cyan_B
  | FG_Gray_B
  | FG_Default_B
  | BG_Black_B
  | BG_Red_B
  | BG_Green_B
  | BG_Yellow_B
  | BG_Blue_B
  | BG_Magenta_B
  | BG_Cyan_B
  | BG_Gray_B
  | BG_Default_B


let assoc_style =  function
  | User i  -> string_of_int i
  | Normal -> "0"
  | Bold -> "1"
  | Bold_off -> "22"
  | Dim ->  "2"
  | Underline -> "4"
  | Underline_off -> "24"
  | Inverse -> "7"
  | Inverse_off -> "27"
  | Blink_off -> "22"
  | FG_Black -> "30"
  | FG_Red -> "31"
  | FG_Green -> "32"
  | FG_Yellow -> "33"
  | FG_Blue -> "34"
  | FG_Magenta -> "35"
  | FG_Cyan -> "36"
  | FG_Gray -> "37"
  | FG_Default -> "39"
  | BG_Black -> "40"
  | BG_Red -> "41"
  | BG_Green -> "42"
  | BG_Yellow -> "43"
  | BG_Blue -> "44"
  | BG_Magenta -> "45"
  | BG_Cyan -> "46"
  | BG_Gray -> "47"
  | BG_Default -> "49"
  | FG_Black_B -> "90"
  | FG_Red_B -> "91"
  | FG_Green_B -> "92"
  | FG_Yellow_B -> "93"
  | FG_Blue_B -> "94"
  | FG_Magenta_B -> "95"
  | FG_Cyan_B -> "96"
  | FG_Gray_B -> "97"
  | FG_Default_B -> "99"
  | BG_Black_B -> "100"
  | BG_Red_B -> "101"
  | BG_Green_B -> "102"
  | BG_Yellow_B -> "103"
  | BG_Blue_B -> "104"
  | BG_Magenta_B -> "105"
  | BG_Cyan_B -> "106"
  | BG_Gray_B -> "107"
  | BG_Default_B -> "109"


let style_of_tag = function
  | "n" -> Normal
  | "b" -> Bold
  | "/b" -> Bold_off
  | "dim" -> Dim
  | "u" -> Underline
  | "/u" -> Underline_off
  | "i" -> Inverse
  | "/i" -> Inverse_off
  | "/bl" -> Blink_off
  | "fg_black" -> FG_Black
  | "fg_red" -> FG_Red
  | "fg_green" -> FG_Green
  | "fg_yellow" -> FG_Yellow
  | "fg_blue" -> FG_Blue
  | "fg_magenta" -> FG_Magenta
  | "fg_cyan" -> FG_Cyan
  | "fg_gray" -> FG_Gray
  | "fg_default" -> FG_Default
  | "bg_black" -> BG_Black
  | "bg_red" -> BG_Red
  | "bg_green" -> BG_Green
  | "bg_yellow" -> BG_Yellow
  | "bg_blue" -> BG_Blue
  | "bg_magenta" -> BG_Magenta
  | "bg_cyan" -> BG_Cyan
  | "bg_gray" -> BG_Gray
  | "bg_default" -> BG_Default
  | "fg_black_b" -> FG_Black_B
  | "fg_red_b" -> FG_Red_B
  | "fg_green_b" -> FG_Green_B
  | "fg_yellow_b" -> FG_Yellow_B
  | "fg_blue_b" -> FG_Blue_B
  | "fg_magenta_b" -> FG_Magenta_B
  | "fg_cyan_b" -> FG_Cyan_B
  | "fg_gray_b" -> FG_Gray_B
  | "fg_default_b" -> FG_Default_B
  | "bg_black_b" -> BG_Black_B
  | "bg_red_b" -> BG_Red_B
  | "bg_green_b" -> BG_Green_B
  | "bg_yellow_b" -> BG_Yellow_B
  | "bg_blue_b" -> BG_Blue_B
  | "bg_magenta_b" -> BG_Magenta_B
  | "bg_cyan_b" -> BG_Cyan_B
  | "bg_gray_b" -> BG_Gray_B
  | "bg_default_b" -> BG_Default_B
  | _ -> raise Not_found


let start_tag t = 
  try Printf.sprintf "[%sm" (assoc_style (style_of_tag t))
  with Not_found -> ""

let stop_tag t = 
  let st = match style_of_tag t with
    | Bold -> Bold_off
    | Underline -> Underline_off
    | Inverse -> Inverse_off

    | FG_Black | FG_Red | FG_Green | FG_Yellow | FG_Blue
    | FG_Magenta | FG_Cyan | FG_Gray | FG_Default -> FG_Default

    | BG_Black | BG_Red | BG_Green | BG_Yellow | BG_Blue 
    | BG_Magenta | BG_Cyan | BG_Gray | BG_Default -> BG_Default

    | FG_Black_B | FG_Red_B | FG_Green_B | FG_Yellow_B | FG_Blue_B 
    | FG_Magenta_B | FG_Cyan_B | FG_Gray_B | FG_Default_B -> FG_Default
 
    | BG_Black_B | BG_Red_B | BG_Green_B | BG_Yellow_B | BG_Blue_B
    | BG_Magenta_B | BG_Cyan_B | BG_Gray_B | BG_Default_B -> BG_Default

    | _ -> Normal
  in
  Printf.sprintf "[%sm" (assoc_style st)
        

let add_colors formatter =
  pp_set_tags formatter true;
  let old_fs = Format.pp_get_formatter_tag_functions formatter () in
  Format.pp_set_formatter_tag_functions formatter
    { old_fs with
      Format.mark_open_tag = start_tag;
      Format.mark_close_tag = stop_tag }

let _ =
  if not nocolor then begin
    add_colors std_formatter;
    add_colors err_formatter;
  end

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
  | Access (a, li) ->
      fprintf fmt "%a[%a]" Hstring.print a (Hstring.print_list ", ") li
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

let print_trace fmt s =
  let last = List.fold_left 
    (fun last (tr, args, uns) ->
      if dmcmt then 
	fprintf fmt "[%s%a]" (Hstring.view tr.tr_name) print_args args
      else 
	fprintf fmt "%s(%a) ->@ " (Hstring.view tr.tr_name) print_args args;
      uns
    ) s s.t_from in
  if dmcmt then fprintf fmt "[0]  "
  else
    if last.t_nb < 0 then 
      fprintf fmt "@{<fg_blue>approx[%d]@}" last.t_nb
    else 
      fprintf fmt "@{<fg_magenta>unsafe[%d]@}" last.t_nb

let print_unsafe fmt s = 
  fprintf fmt "Unsafe property (from %a):@\n        %a@."
    print_trace s print_system s

let rec print_atom_dot fmt = function
  | True -> fprintf fmt "true"
  | False -> fprintf fmt "false"
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
	if s.t_nb >= 0 then
	  fprintf fmt "%d [label=\"%a\", color = red, shape=tripleoctagon, style=filled];" 
	    s.t_nb print_system_dot s
	else
	  fprintf fmt "%d [label=\"%a\", color = orange, shape=doubleoctagon, style=filled];" 
	    s.t_nb print_system_dot s
      else
	let (tr, args, _)= List.hd s.t_from in 
	fprintf fmt "%d -> %d [label=\"%s(%a)\"];@." 
	  s.t_nb_father s.t_nb (Hstring.view tr.tr_name) print_args args;
	if s.t_nb = 0 then
	  fprintf fmt "%d [label=\"%a\", color = red, shape=tripleoctagon, style = filled];" 
	    s.t_nb print_system_dot s
	else 
	  fprintf fmt "%d [label=\"%a\"];" s.t_nb print_system_dot s
    end
  else
    print_trace fmt s

let print_bad fmt s =
  if List.length s.t_from  = 0 then
      fprintf fmt "%d [label=\"%a\", color = green, shape=doublecircle, style=filled];" 
	s.t_nb print_system_dot s
  else
    let (tr, args, _)= List.hd s.t_from in 
    fprintf fmt "%d -> %d [label=\"%s(%a)\"];@." 
      s.t_nb_father s.t_nb (Hstring.view tr.tr_name) print_args args;
    fprintf fmt "%d [label=\"%a\", color = green, shape=doublecircle, style = filled];" 
	s.t_nb print_system_dot s
  

let print_subsumed_node cand fmt (s, db) =
  let db = List.filter (fun x -> x <> s.t_nb) db in 
  if dot && verbose > 0 then
    begin
      if List.length s.t_from  = 0 then
	if verbose = 1 then
	  if s.t_nb = 0 then 
	    fprintf fmt "%d [color = red, shape=tripleoctagon, style = filled];" s.t_nb
	  else 
	    fprintf fmt "%d [color = gray, fontcolor=gray];" s.t_nb
	else
	  begin
	    (if s.t_nb = 0 then
	      fprintf fmt 
		"%d [label=\"%a\" , color = red, shape=tripleoctagon,  style=filled];" 
		s.t_nb print_system_dot s
	    else 
	      fprintf fmt 
		"%d [label=\"%a\" color = gray, fontcolor=gray];" s.t_nb print_system_dot s);
	    if verbose >= 2 then 
	      begin
		fprintf fmt "@.";
		List.iter 
		  (fun d -> fprintf fmt " %d -> %d [style=dashed, arrowhead=onormal, color=%s %s] @." 
		     s.t_nb d 
                    (if cand then "orange" else "gray")
                    (if cand then ", penwidth=4" else ", constraint=false")
                  ) db
	      end
	  end
      else
	let (tr, args, _) = List.hd s.t_from in 
	fprintf fmt "%d -> %d [label=\"%s(%a)\"];@." 
	  s.t_nb_father s.t_nb (Hstring.view tr.tr_name) print_args args;
	if verbose = 1 then 
	  if s.t_nb = 0 then
	    fprintf fmt "%d [label=\"\" , color = red, shape=tripleoctagon, style = filled];" s.t_nb
	  else 
	    fprintf fmt "%d [label=\"\" color = gray, fontcolor=gray];" s.t_nb
	else
	  begin
	    fprintf fmt "%d [label=\"%a\" color = gray, fontcolor=gray];" 
	      s.t_nb print_system_dot s;
	    if verbose >= 2 then
	      begin
		fprintf fmt "@.";
		List.iter 
		  (fun d -> fprintf fmt " %d -> %d [style=dashed, arrowhead=onormal, color=%s %s] @." 
		     s.t_nb d
                    (if cand then "orange" else "gray")
                    (if cand then ", penwidth=4" else ", constraint=false")
                  ) db
	      end
	  end
    end


let print_dead_node  = print_subsumed_node false

let print_dead_node_to_cand  = print_subsumed_node true


let print_verbose_node fmt s =
  if false && verbose = 0 then print_node fmt s else begin
    (* fprintf fmt "(%d -> %d) " s.t_nb_father s.t_nb; *)
    fprintf fmt " %a\n@." print_system s;
    let last = List.fold_left
      (fun last (tr, args, s') ->
	 fprintf fmt "  %s(%a) -> %a\n@." (Hstring.view tr.tr_name) 
           print_args args print_system s';
        s'
      ) s s.t_from in
    
    if last.t_nb < 0 then 
      fprintf fmt "    = @{<fg_blue>approx[%d]@}" last.t_nb
    else 
      fprintf fmt "    = @{<fg_magenta>unsafe[%d]@}" last.t_nb
  end
