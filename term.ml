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

open Options

type op_comp = Eq | Lt | Le | Neq
type op_arith = Plus | Minus

type sort = Glob | Constr | Var

type subst_sort = (sort * sort) list

let subst_sort sigma_sort s = try List.assoc s sigma_sort with Not_found -> s

type const = ConstInt of Num.num | ConstReal of Num.num | ConstName of Hstring.t

let compare_const c1 c2 = match c1, c2 with
  | (ConstInt n1 | ConstReal n1), (ConstInt n2 | ConstReal n2) ->
      Num.compare_num n1 n2
  | (ConstInt _ | ConstReal _), _ -> -1
  | _, (ConstInt _ | ConstReal _) -> 1
  | ConstName h1, ConstName h2 -> Hstring.compare h1 h2

module MConst = struct 
  module M = Map.Make (struct type t = const let compare = compare_const end)
  include M

  exception Choose of const * int
  let choose m =
    try
      M.iter (fun c i -> raise (Choose (c, i))) m;
      raise Not_found
    with Choose (c, i) -> c, i

  let is_num m =
    if M.cardinal m = 1 then
      match choose m with
      | (ConstInt n | ConstReal n), i -> Some (Num.mult_num (Num.Int i) n)
      | _ -> None
    else None
			       
end

let compare_constants = MConst.compare Pervasives.compare 

type t = 
  | Const of int MConst.t
  | Var of Variable.t
  | Constr of Hstring.t
  | Glob of Hstring.t
  | Access of Hstring.t * Variable.t list
  | Arith of t * int MConst.t

(* TODO ^ type has changed *)

let rec compare t1 t2 = 
  match t1, t2 with
    | Const c1, Const c2 -> compare_constants c1 c2
    | Const _, _ -> -1 | _, Const _ -> 1
    | Elem (_, (Constr | Var)), Elem (_, (Glob | Arr)) -> -1
    | Elem (_, (Glob | Arr)), Elem (_, (Constr | Var)) -> 1
    | Elem (s1, _), Elem (s2, _) -> Hstring.compare s1 s2
    | Elem _, _ -> -1 | _, Elem _ -> 1
    | Access (a1, l1), Access (a2, l2) ->
	let c = Hstring.compare a1 a2 in
	if c<>0 then c else Hstring.compare_list l1 l2
    | Access _, _ -> -1 | _, Access _ -> 1 
    | Arith (t1, cs1), Arith (t2, cs2) ->
	let c = compare t1 t2 in
	if c<>0 then c else compare_constants cs1 cs2

let hash = Hashtbl.hash_param 50 50

let htrue = Hstring.make "True"
let hfalse = Hstring.make "False"

type acc_eq = { a : Hstring.t; i: Hstring.t; e: t }


let rec subst sigma ?(sigma_sort=[]) t = 
  match t with
    | Elem (x, s) -> 
	(try Elem (svar sigma x, ssort sigma_sort s) with Not_found -> t)
    | Access (a, lz) -> 
	Access (a, List.map
          (fun z ->
            try svar sigma z with Not_found -> z) lz)
    | Arith (x, c) -> Arith (subst sigma ~sigma_sort x, c)
    | _ -> t
