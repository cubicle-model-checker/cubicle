(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2014                          *)
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
open Options
open Ast
open Util
open Types

type t = node_cube


let variables {cube = {Cube.vars = vars }} = vars 

let array n = n.cube.Cube.array

let litterals n = n.cube.Cube.litterals

let dim n = Cube.dim n.cube

let size n = Cube.size n.cube

let compare_kind s1 s2 =
  match s1.kind, s2.kind with
  | Approx, Approx -> 0
  | Approx, _ -> -1
  | _, Approx -> 1
  | k1, k2 -> Pervasives.compare k1 k2

let compare_by_breadth s1 s2 =
  let v1 = dim s1 in
  let v2 = dim s2 in
  let c = Pervasives.compare v1 v2 in
  if c <> 0 then c else
    let c1 = size s1 in
    let c2 = size s2 in
    let c = Pervasives.compare c1 c2 in
    if c <> 0 then c else
      let c =  compare_kind s1 s2 in
      if c <> 0 then c else
        let c = Pervasives.compare s1.depth s2.depth in 
        if c <> 0 then c else
          Pervasives.compare (abs s1.tag) (abs s2.tag)

let compare_by_history s1 s2 =
  (* let c = Pervasives.compare s1.heuristic s2.heuristic in *)
  (* if c <> 0 then c else *)
    let v1 = dim s1 in
    let v2 = dim s2 in
    let c = Pervasives.compare v1 v2 in
    if c <> 0 then c else
      let c1 = size s1 in
      let c2 = size s2 in
      let c = Pervasives.compare c1 c2 in
      if c <> 0 then c else
        let c =  compare_kind s1 s2 in
        if c <> 0 then c else
          let c = Pervasives.compare s1.depth s2.depth in 
          if c <> 0 then c else
            Pervasives.compare (abs s1.tag) (abs s2.tag)

let compare_by_depth s1 s2 =
  let v1 = dim s1 in
  let v2 = dim s2 in
  let c = Pervasives.compare v1 v2 in
  if c <> 0 then c else
    let c1 = size s1 in
    let c2 = size s2 in
    let c = Pervasives.compare c1 c2 in
    if c <> 0 then c else
      let c =  compare_kind s1 s2 in
      if c <> 0 then c else
        let c = Pervasives.compare s2.depth s1.depth in 
        if c <> 0 then c else
          Pervasives.compare (abs s1.tag) (abs s2.tag)

let rec origin n = match n.from with
  | [] -> n
  | (_,_, p)::_ ->
     if p.kind = Approx then p
     else origin p

let new_tag =
  let cpt_pos = ref 0 in
  let cpt_neg = ref 0 in
  fun ?(kind=Node) () -> 
  match kind with 
  | Approx -> decr cpt_neg; !cpt_neg
  | _ -> incr cpt_pos; !cpt_pos

let create ?(kind=Node) ?(from=None) ?(hist=None) cube =
  let from, heuristic = match from, hist with
    | None, None -> [], -1
    | None, Some s -> s.from, s.heuristic
    | Some ((_, _, n) as f), _ -> f :: n.from , n.heuristic
  in
  { 
    cube = cube;
    tag = new_tag ~kind ();
    kind = kind;
    depth = List.length from;
    deleted = false;
    from;
    heuristic;
  }

let has_deleted_ancestor n =
  let rec has acc = function
    | [] -> false, acc
    | (_, _, a) :: r ->
       if a.deleted then true, acc
       else has (a :: acc) r
  in
  let del, children = has [] n.from in
  if del then List.iter (fun a -> a.deleted <- true) children;
  del
    
let has_deleted_ancestor n =
  List.exists (fun (_, _, a) -> a.deleted) n.from

let ancestor_of n s =
  (* not (List.exists (fun (_,anc) -> n == anc) s.t_from) *)
  (* List.exists (fun (_,_,anc) -> ArrayAtom.equal n.t_arru anc.t_arru) s.t_from *)
  List.exists (fun (_, _, ps) -> n.tag = ps.tag) s.from


let subset n1 n2 = ArrayAtom.subset (array n1) (array n2)
       
let print fmt n = 
  fprintf fmt "%a%s" Cube.print n.cube
    (if approx_history then sprintf " heur = %d%%" n.heuristic else "")

let print_list fmt nl =
  List.iter (Format.fprintf fmt "%a@\n@\n" print) nl
    
module Latex = struct
(* Latex printing of nodes, experimental - to rewrite *)


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
    | Elem (s, Var) -> fprintf fmt "%a" Hstring.print s
    | Elem (s, Glob) -> fprintf fmt "\\texttt{%a}" Hstring.print s
    | Elem (s, Constr) -> fprintf fmt "\\textsf{%a}" Hstring.print s
    | Access (a, li) ->
       fprintf fmt "\\texttt{%a}[%a]" Hstring.print a (Hstring.print_list ", ") li
    | Arith (x, cs) -> 
       fprintf fmt "@[%a%a@]" print_term x print_cs cs

  let str_op_comp =
    function Eq -> "=" | Lt -> "<" | Le -> "\\le" | Neq -> "\\neq"

  let rec print_atom fmt = function
    | Atom.True -> fprintf fmt "true"
    | Atom.False -> fprintf fmt "false"
    | Atom.Comp (x, op, y) -> 
       fprintf fmt "%a %s %a" print_term x (str_op_comp op) print_term y
    | Atom.Ite (la, a1, a2) ->
       fprintf fmt "@[ite(%a,@ %a,@ %a)@]"
	       (print_atoms false "\\land") (SAtom.elements la)
               print_atom a1 print_atom a2

  and print_atoms inline sep fmt = function
    | [] -> ()
    | [a] -> print_atom fmt a
    | a::l -> 
       if inline then 
         fprintf fmt "%a %s@ %a" print_atom a sep (print_atoms inline sep) l
       else
         fprintf fmt "%a %s@\n%a" print_atom a sep (print_atoms inline sep) l

  let print fmt n = 
    fprintf fmt "\\item $";
    let l = variables n in
    (match l with
     | [] -> ()
     | [_] -> fprintf fmt "\\forall %a.~ " Variable.print_vars l
     | x::y::[] -> fprintf fmt "\\forall %a.~ %a \\neq %a \\implies "
                           Variable.print_vars l Variable.print x Variable.print y
     | _ -> fprintf fmt "\\forall %a.~ " Variable.print_vars l
    );
    let natoms = List.rev (SAtom.elements (litterals n)) in
    (match natoms with
     | [] -> ()
     | [a] -> print_atom fmt (Atom.neg a)
     | last :: r ->
        let lr = List.rev r in
        fprintf fmt "(%a) \\implies %a" (print_atoms true " \\land ") lr
                print_atom (Atom.neg last)
    );
    fprintf fmt "$"

end

(* let print = Latex.print *)

let print_history fmt n =
  let last = List.fold_left 
    (fun last (tr, args, a) ->
      if dmcmt then 
	fprintf fmt "[%a%a]" Hstring.print tr.tr_name Variable.print_vars args
      else 
	fprintf fmt "%a(%a) ->@ " Hstring.print tr.tr_name
                Variable.print_vars args;
      a
    ) n n.from in
  if dmcmt then fprintf fmt "[0]  "
  else
    if last.kind = Approx then 
      fprintf fmt "@{<fg_blue>approx[%d]@}" last.tag
    else 
      fprintf fmt "@{<fg_magenta>unsafe[%d]@}" last.tag

let find_atoms t term =
  SAtom.filter (fun a ->
      match a with
        | Atom.Comp (t1, _, _) -> Term.equal term t1
        | _ -> false
    ) t.cube.Cube.litterals
    (*         match !atom with *)
    (* | Some a -> a *)
    (* | _ -> Format.eprintf "The term %a isn't bind in the node %a@." *)
    (*          Term.print term print t; *)
    (*        exit 1 *)
