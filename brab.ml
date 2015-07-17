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
open Types
open Ast

module BWD = Bwd.Selected
module Oracle = Approx.SelectedOracle


(* FIXME Bug when search is parallel *)
let rec search_and_backtrack tainted invariants candidates saved_candidates system mod_system =
  let res = BWD.search ~invariants ~candidates mod_system in
  match res with
  | Bwd.Safe (_, candidates) ->
    if tainted then (
      Stats.restart ();
      eprintf "ICICICICI!!!!!!@.";
      (* Restarting *)
      search_and_backtrack false [] saved_candidates [] system system
    )
    else
      res
  | Bwd.Unsafe (faulty, candidates, visited) ->
    let candidates, queued = List.partition (fun n -> n.kind = Approx) candidates in
     let o = Node.origin faulty in
     if o.kind = Orig then res
     else
       (* Bad candidate, we backtrack while keeping interresting candidates *)
       begin
         assert (o.kind = Approx);
         if not quiet then eprintf "The candidate %d = %a is BAD\n@."
                                   o.tag Node.print o;
         Stats.restart ();
         let candidates =
           Approx.remove_bad_candidates system faulty candidates
         in

         (* Continue anyway *)
         search_and_backtrack true (faulty :: visited) [] candidates
           system { system with t_unsafe = queued }

         (* (\* Restarting *\) *)
         (* search_and_backtrack invariants candidates system *)

       end

(**************************************************************)
(* Backward reachability with approximations and backtracking *)
(**************************************************************)
    
let brab system =
  Oracle.init system;
  if only_forward then exit 0;
  search_and_backtrack false [] [] [] system system
