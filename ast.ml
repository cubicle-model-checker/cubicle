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

type op_comp = Eq | Lt | Le| Neq
type op_arith = Plus | Minus

type term = 
  | Const of int
  | Elem of string 
  | Access of string * string 
  | Arith of string * op_arith * int

type acc_eq = { a : string; i: string; e: term }

module rec Atom : sig
  type t =
    | True
    | False
    | Comp of term * op_comp * term
    | Ite of SAtom.t * t * t

  val compare : t -> t -> int
end = struct
  
  type t =
    | True
    | False
    | Comp of term * op_comp * term
    | Ite of SAtom.t * t * t

  let rec compare_term t1 t2 = 
    match t1, t2 with
      | Const i1, Const i2 -> Pervasives.compare i1 i2
      | Const _, _ -> -1 | _, Const _ -> 1
      | Elem s1, Elem s2 -> Pervasives.compare s1 s2
      | Elem _, _ -> -1 | _, Elem _ -> 1
      | Access (a1, i1), Access (a2, i2) ->
	  let c = Pervasives.compare a1 a2 in
	  if c<>0 then c else Pervasives.compare i1 i2
      | Access _, _ -> -1 | _, Access _ -> 1 
      | Arith (t1, op1, u1), Arith (t2, op2, u2) ->
	  let c = Pervasives.compare op1 op2 in
	  if c <> 0 then c else
	    let c = Pervasives.compare t1 t2 in
	    if c<>0 then c else Pervasives.compare u1 u2

  let rec compare a1 a2 = 
    match a1, a2 with
      | True, True -> 0
      | True, _ -> -1 | _, True -> 1
      | False, False -> 0
      | False, _ -> -1 | _, False -> 1
      | Comp (x1, op1, y1), Comp (x2, op2, y2) ->
	  let c = Pervasives.compare op1 op2 in
	  let c1 = compare_term x1 x2 in
	  let c2 = compare_term y1 y2 in
	  if c <> 0  then c else if c1 <> 0 then c1  else c2
      | Comp _, _ -> -1 | _, Comp _ -> 1
      | Ite (sa1, a1, b1), Ite (sa2, a2, b2) ->
	  let c = SAtom.compare sa1 sa2 in
	  if c<>0 then c else 
	    let c = compare a1 a2 in
	    if c<>0 then c else compare b1 b2

end
and SAtom : Set.S with type elt = Atom.t = Set.Make(Atom)

let add a s = 
  match a with
    | Atom.True -> s
    | Atom.False -> SAtom.singleton Atom.False
    | _ -> if SAtom.mem Atom.False s then s else SAtom.add a s

  (* Substitute an indice variable j by i in a set of atoms *)

let svar j i k = if k = j then i else k
    
let subst_term sigma t = 
  match t with
    | Elem x -> (try Elem (List.assoc x sigma) with Not_found -> t)
    | Access (a, z) -> 
	(try Access (a, List.assoc z sigma) with Not_found -> t)
    | _ -> t
	
open Atom

let rec subst_atoms sigma sa = 
  SAtom.fold (fun a -> add (subst_atom sigma a)) sa SAtom.empty
and subst_atom sigma a = 
  match a with
    | Ite (sa, a1, a2) -> 
	Ite(subst_atoms sigma sa, subst_atom sigma a1, subst_atom sigma a2)
    | Comp (x, op, y) -> 
	let sx = subst_term sigma x in
	let sy = subst_term sigma y in
	Comp(sx, op, sy)
    | _ -> a

type update = {
  up_arr : string;
  up_arg : string;
  up_swts : (SAtom.t * term) list * term;
}

type transition = {
  tr_name : string;
  tr_args : string list;
  tr_reqs : SAtom.t;
  tr_ureq : (string * SAtom.t) option;
  tr_assigns : (string * term) list;
  tr_upds : update list;
  tr_nondets : string list;
}

type elem = string * (string list)

type system = {
  globals : (string * string) list;
  arrays : (string * (string * string)) list;
  elems : elem list;
  init : string option * SAtom.t;
  invs : (string list * SAtom.t) list;
  unsafe : string list * SAtom.t;
  trans : transition list
}

(* Types AST *)

type t_elem = { 
  telem_name:  string;
  telem_ty : AltErgo.Ty.t; 
  telem_consts : (string * AltErgo.Term.t) list;
}

type sort = Glob | Arr | Constr | Var

type t_system = {
  t_from : (string * SAtom.t) list;
  t_env : (string, (sort * AltErgo.Ty.t * AltErgo.Term.t)) Hashtbl.t;
  t_init : string option * SAtom.t;
  t_invs : (string list * SAtom.t) list;
  t_unsafe : string list * SAtom.t;
  t_trans : transition list
}



