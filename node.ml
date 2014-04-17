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
open Options
open Ast
open Util

type kind = Node | Approx | Inv

type t =
    { 
      cube : Cube.t;
      alpha : Variable.t list * Atom.Array.t;
      tag : int;
      kind : kind;
      mutable deleted : bool;
      from : (transition * Variable.t list * node) list;
    }

let variables {cube = {Cube.vars = vars }} = vars 

let array n = n.cube.Cube.array

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


let create ?(kind=Node) ?(from=None) cube =
  { 
    cube = cube;
    alpha = Atom.Array.alpha cube.array cube.vars;
    tag = new_tag ~kind;
    deleted = false;
    from = match from with
           | None -> []
           | Some (tr, args, n) as f -> f :: n.from
  }

let has_deleted_ancestor n =
  let rec has acc = function
    | [] -> false, acc
    | (_, _, a) :: r ->
       if a.t_deleted then true, acc
       else has (a :: acc) r
  in
  let del, children = has [] n.from in
  if del then List.iter (fun a -> a.deleted <- true) children;
  del
    
let has_deleted_ancestor n =
  List.exists (fun (_, _, a) -> a.deleted) n.from


let rec add_and_resolve n visited =
  let visited =
    Cubetrie.fold (fun visited nv ->
      match Cube.resolve_two n.cube nv.cube with
        | None -> visited
        | Some cube_res -> add_and_resolve (create cube_res) visited
    ) visited visited in
  Cubetrie.add_array s.t_arru s visited

       
let print fmt n = Cube.print fmt n.cube


let print_history fmt n =
  let last = List.fold_left 
    (fun last (tr, args, a) ->
      if dmcmt then 
	fprintf fmt "[%s%a]" Hstring.print tr.tr_name Variable.print_vars args
      else 
	fprintf fmt "%s(%a) ->@ " Hstring.print tr.tr_name
                Variable.print_vars args;
      a
    ) n n.from in
  if dmcmt then fprintf fmt "[0]  "
  else
    if last.kind = Approx then 
      fprintf fmt "@{<fg_blue>approx[%d]@}" last.tag
    else 
      fprintf fmt "@{<fg_magenta>unsafe[%d]@}" last.tag
