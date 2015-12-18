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
open Types
open Types.Term
open Types.Atom

exception Unsafe of Node.t

(*************************************************)
(* Safety check : n /\ init must be inconsistent *)
(*************************************************)

let cdnf_asafe ua =
  List.exists (
    List.for_all (fun a ->
      Cube.inconsistent_2arrays ua a))


(* fast check for inconsistence *)
let obviously_safe { t_init_instances = init_inst; } n =
  let nb_procs = Node.dim n in
  let _, cdnf_ai = Hashtbl.find init_inst nb_procs in
  cdnf_asafe (Node.array n) cdnf_ai
 
let check s n =
  (*Debug.unsafe s;*)
  try
    if not (obviously_safe s n) then
      begin
	Prover.unsafe s n;
	if not quiet then eprintf "\nUnsafe trace: @[%a@]@."
	  Node.print_history n;
        raise (Unsafe n)
      end
  with
    | Smt.Unsat _ -> ()


let obviously_safe_good { t_good_instances = good_inst; } n =
  let nb_procs = Node.dim n in
  let _, cdnf_ai = Hashtbl.find good_inst nb_procs in
  cdnf_asafe (Node.array n) cdnf_ai
 

let rec compare_terms_naive t1 t2 =
  match t1, t2 with
    | Const c1, Const c2 -> 0
    | Const _, _ -> -1 | _, Const _ -> 1
    | Elem (_, (Constr | Var)), Elem (_, Glob) -> -1
    | Elem (_, Glob), Elem (_, (Constr | Var)) -> 1
    | Elem (s1, _), Elem (s2, _) -> Hstring.compare s1 s2
    | Elem _, _ -> -1 | _, Elem _ -> 1
    | Access (a1, _), Access (a2, _) -> Hstring.compare a1 a2
    | Access _, _ -> -1 | _, Access _ -> 1 
    | Arith (t1, cs1), Arith (t2, cs2) -> compare_terms_naive t1 t2

let rec compare_atoms_naive a1 a2 =
  match a1, a2 with
    | True, True -> 0
    | True, _ -> -1 | _, True -> 1
    | False, False -> 0
    | False, _ -> -1 | _, False -> 1
    | Comp (x1, op1, y1), Comp (x2, op2, y2) ->
      let c1 = compare_terms_naive x1 x2 in
      if c1 <> 0 then c1 
      else compare_terms_naive y1 y2
    | Comp _, _ -> -1 | _, Comp _ -> 1
    | Ite (sa1, a1, b1), Ite (sa2, a2, b2) ->
      let c = SAtom.compare sa1 sa2 in
      if c<>0 then c else 
	let c = compare a1 a2 in
	if c<>0 then c else compare b1 b2
          


let litt_in_list n sal =
  let sa1 = n.cube.Cube.litterals in
  Types.SAtom.exists (
    fun a1 -> 
      List.exists (
        fun sa2 -> 
          Types.SAtom.exists (
            fun a2 -> compare_atoms_naive a1 a2 <> 0
          ) sa2
      ) sal
  ) sa1


let check_good s n =
  (*Debug.unsafe s;*)
  try
    if not (obviously_safe_good s n) then
      begin
        if litt_in_list n (snd s.t_good) then 
          begin
	    Prover.unsafe_good s n;
	    if not quiet then eprintf "\nGood trace: @[%a@]@."
	      Node.print_history n;
            Format.eprintf "\n----------Refused----------@.";
            raise (Unsafe n)
          end
      end
  with
    | Smt.Unsat _ -> ()

