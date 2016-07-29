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
  let { init_cdnf_a } = Hashtbl.find init_inst nb_procs in
  cdnf_asafe (Node.array n) init_cdnf_a
 
let check s n =
  (*Debug.unsafe s;*)
  try
    if not (obviously_safe s n) then
      begin
	Prover.unsafe s n;
	if not quiet then printf "\nUnsafe trace: @[%a@]@."
	  Node.print_history n;
        raise (Unsafe n)
      end
  with
    | Smt.Unsat _ -> ()

