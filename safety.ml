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

let has_unsat_recv n =
  let _, _, _, _, evts = Chanevent.extract_events_set n.cube.Cube.litterals in
  let urevts = Chanevent.unsat_recv_events evts in
  not (Channels.HMap.is_empty urevts)

let check s n =
  (*Debug.unsafe s;*)
  TimeSafety.start ();
  begin try
    if not (obviously_safe s n || has_unsat_recv n) then
      begin
        let n = { n with cube = Cube.(create
          n.cube.vars (Chanrel.filter_rels_set n.cube.litterals)) } in
	Prover.unsafe s n;
	if not quiet then eprintf "\nUnsafe trace: @[%a@]@."
				  Node.print_history n;
        raise (Unsafe n)
      end
  with
    | Smt.Unsat _ -> ()
  end;
  TimeSafety.pause ();
