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
open Util
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
  TimeSafety.start ();
(**)if debug then eprintf ">>> [safety check]";
  begin try
    if not (obviously_safe s n) then
      begin
(**)if debug then eprintf " asking smt\n";
	Prover.unsafe s n;
	if not quiet then eprintf "\nUnsafe trace: @[%a@]@."
				  Node.print_history n;
        TimeSafety.pause ();
        raise (Unsafe n)
      end
(* (\**\)else if debug then eprintf " obviously safe\n"; *)
  with
    | Smt.Unsat _ -> (**)if debug then eprintf " safe\n"; ()
  end;
  TimeSafety.pause ()
