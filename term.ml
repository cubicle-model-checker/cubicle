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
module HSet = Hstring.HSet

module Type = struct
  type op_comp = Eq | Lt | Le | Neq
  type op_arith = Plus | Minus

  type sort = Glob | Constr | Var

  type subst_sort = (sort * sort) list

  type const = ConstInt of Num.num | ConstReal of Num.num | ConstName of Hstring.t

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

  type t = 
    | Const of int MConst.t
    | Elem of Hstring.t * sort
    | Access of Hstring.t * Variable.t list
    | Arith of t * int MConst.t
end

include Type

let subst_sort sigma_sort s = try List.assoc s sigma_sort with Not_found -> s

let compare_const c1 c2 = match c1, c2 with
  | (ConstInt n1 | ConstReal n1), (ConstInt n2 | ConstReal n2) ->
     Num.compare_num n1 n2
  | (ConstInt _ | ConstReal _), _ -> -1
  | _, (ConstInt _ | ConstReal _) -> 1
  | ConstName h1, ConstName h2 -> Hstring.compare h1 h2

let compare_constants = MConst.compare Pervasives.compare 


let num_of_const = function
  | ConstInt n | ConstReal n -> n
  | _ -> assert false

let add_constnum c i num =
  match c, num with
    | ConstInt n, ConstInt m -> 
	ConstInt (Num.add_num (Num.mult_num (Num.Int i) n) m)
    | (ConstInt n | ConstReal n), (ConstInt m | ConstReal m) ->
	ConstReal (Num.add_num (Num.mult_num (Num.Int i) n) m)
    | _ -> assert false

let split_num_consts cs =
  MConst.fold
    (fun c i (cs, num) -> match c, num with
       | ConstName _, _ -> MConst.add c i cs, num
       | _ -> cs, add_constnum c i num)
    cs (MConst.empty, ConstInt (Num.Int 0))

let add_constant c i cs =
  match c with
    | ConstInt _ | ConstReal _ ->
	let cs, num = split_num_consts cs in
	let num = add_constnum c i num in
	if Num.compare_num (num_of_const num) (Num.Int 0) = 0 then cs
	else MConst.add num 1 cs
    | _ ->
	let i' = try MConst.find c cs with Not_found -> 0 in
	let i = i + i' in
	if i = 0 then MConst.remove c cs
	else MConst.add c i cs

let add_constants cs1 cs2 =
  let m = MConst.fold add_constant cs2 cs1 in
  if MConst.is_empty m then 
    let c0 = 
      if is_int_const (fst (MConst.choose cs1)) then 
	ConstInt (Num.Int 0) 
      else ConstReal (Num.Int 0)
    in
    MConst.add c0 1 m
  else m

let mult_const a =
  MConst.map (fun i -> i * a)


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

module STerm = PSet.Make (struct type t = t let compare = compare end)
module Set = STerm

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


let rec variables acc = function
  | Elem (x, Var) -> Variable.Set.add x acc
  | Access (_, lx) ->
     List.fold_left (fun acc x -> Variable.Set.add x acc) acc lx
  | Arith (t, _) -> variables acc t
  | _ -> acc

let is_int_const = function
  | ConstInt _ -> true
  | ConstReal _ -> false
  | ConstName n -> 
    Hstring.equal (snd (Smt.Symbol.type_of n)) Smt.Type.type_int

let rec type_of = function
  | Const cs ->
      if is_int_const (fst (MConst.choose cs)) then
        Smt.Type.type_int
      else Smt.Type.type_real
  | Elem (x, Var) -> Smt.Type.type_proc
  | Elem (x, _) | Access (x, _) -> snd (Smt.Symbol.type_of x)
  | Arith(t, _) -> type_of t
