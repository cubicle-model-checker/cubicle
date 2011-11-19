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
  | Elem of Hstring.t
  | Access of Hstring.t * Hstring.t
  | Arith of Hstring.t * op_arith * int

let rec compare_term t1 t2 = 
  match t1, t2 with
    | Const i1, Const i2 -> Pervasives.compare i1 i2
    | Const _, _ -> -1 | _, Const _ -> 1
    | Elem s1, Elem s2 -> Hstring.compare s1 s2
    | Elem _, _ -> -1 | _, Elem _ -> 1
    | Access (a1, i1), Access (a2, i2) ->
      let c = Hstring.compare a1 a2 in
      if c<>0 then c else Hstring.compare i1 i2
    | Access _, _ -> -1 | _, Access _ -> 1 
    | Arith (t1, op1, u1), Arith (t2, op2, u2) ->
      let c = Pervasives.compare op1 op2 in
      if c <> 0 then c else
	let c = Hstring.compare t1 t2 in
	if c<>0 then c else Pervasives.compare u1 u2

type acc_eq = { a : Hstring.t; i: Hstring.t; e: term }

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


let alpha_args = 
  [ Hstring.make "$1";
    Hstring.make "$2";
    Hstring.make "$3";
    Hstring.make "$4";
    Hstring.make "$5";
    Hstring.make "$6";
    Hstring.make "$7";
    Hstring.make "$8";
    Hstring.make "$9" ]

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


let build_subst args a_args =
  let rec a_subst acc args a_args =
    match args, a_args with
      | [], _ -> acc
      | x::args, ax::a_args ->
	a_subst ((x, ax)::acc) args a_args
      | _ -> assert false
  in
  a_subst [] args a_args


module TimerSubset = Timer.Make (struct end)

module TimerApply = Timer.Make (struct end)

module ArrayAtom = struct

  type t = Atom.t array

  let equal a1 a2 =
    let n = Array.length a1 in
    let n2 = Array.length a2 in
    if n <> n2 then false
    else
      let res = ref true in
      let i = ref 0 in 
      while !res && !i < n  do
	res := (Atom.compare a1.(!i) a2.(!i) = 0);
	incr i
      done;
      !res

  let subset a1 a2 =
    TimerSubset.start ();
    let n1 = Array.length a1 in
    let n2 = Array.length a2 in
    let s = 
      if n1 > n2 then false
      else
	let i1 = ref 0 in 
	let i2 = ref 0 in
	while !i1 < n1 && !i2 < n2 do
	  let c = Atom.compare a1.(!i1) a2.(!i2) in
	  if c = 0 then (incr i1; incr i2)
	  else if c < 0 then i2 := n2
	  else incr i2
	done;
	!i1 = n1
    in
    TimerSubset.pause ();
    s

  let of_satom s =
    Array.of_list (SAtom.elements s)

  let union = Array.append

  let apply_subst sigma a =
    TimerApply.start ();
    let a' = Array.init (Array.length a) (fun i -> subst_atom sigma a.(i)) in
    Array.fast_sort Atom.compare a';
    TimerApply.pause ();
    a'

  let nb_diff a1 a2 =
    let cpt = ref 0 in
    let n1 = Array.length a1 in
    let n2 = Array.length a2 in
    let i1 = ref 0 in 
    let i2 = ref 0 in
    while !i1 < n1 && !i2 < n2 do
      let c = Atom.compare a1.(!i1) a2.(!i2) in
      if c = 0 then (incr i1; incr i2)
      else if c < 0 then (incr cpt; incr i1)
      else incr i2
    done;
    !cpt + (n1 - !i1)

  let alpha atoms args =
    let subst = build_subst args alpha_args in
    List.map snd subst, apply_subst subst atoms

end


type update = {
  up_arr : Hstring.t;
  up_arg : Hstring.t;
  up_swts : (SAtom.t * term) list * term;
}

type transition = {
  tr_name : Hstring.t;
  tr_args : Hstring.t list;
  tr_reqs : SAtom.t;
  tr_ureq : (Hstring.t * SAtom.t) option;
  tr_assigns : (Hstring.t * term) list;
  tr_upds : update list;
  tr_nondets : Hstring.t list;
}

type elem = Hstring.t * (Hstring.t list)

type system = {
  globals : (Hstring.t * Hstring.t) list;
  arrays : (Hstring.t * (Hstring.t * Hstring.t)) list;
  elems : elem list;
  init : Hstring.t option * SAtom.t;
  invs : (Hstring.t list * SAtom.t) list;
  unsafe : Hstring.t list * SAtom.t;
  trans : transition list
}

(* Types AST *)

type t_elem = { 
  telem_name:  Hstring.t;
  telem_ty : AltErgo.Ty.t; 
  telem_consts : (Hstring.t * AltErgo.Term.t) list;
}

type sort = Glob | Arr | Constr | Var

let sort_of env x = 
  try 
    let s, _, _ = Hstring.H.find env x in 
    s 
  with Not_found -> Var

type t_system = {
  t_from : (Hstring.t * t_system) list;
  t_env : (sort * AltErgo.Ty.t * AltErgo.Term.t) Hstring.H.t;
  t_init : Hstring.t option * SAtom.t;
  t_invs : (Hstring.t list * SAtom.t) list;
  t_unsafe : Hstring.t list * SAtom.t;
  t_arru : ArrayAtom.t;
  t_alpha : Hstring.t list * ArrayAtom.t;
  t_trans : transition list;
  mutable t_deleted : bool
}



