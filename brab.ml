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
open Types
open Ast

module BWD = Bwd.Selected
module Oracle = Approx.SelectedOracle


(* FIXME Bug when search is parallel *)
let rec search_and_backtrack candidates system =
  let res = BWD.search ~candidates system in
  match res with
  | Bwd.Safe _ -> res
  | Bwd.Unsafe (faulty, candidates) ->
     let o = Node.origin faulty in
     if o.kind <> Approx then res
     else
       (* Bad candidate, we backtrack while keeping interresting candidates *)
       begin
         if not quiet then eprintf "The candidate %d = %a is BAD\n@."
                                   o.tag Node.print o;
         Stats.restart ();
         let candidates =
           Approx.remove_bad_candidates system faulty candidates
         in
         (* Restarting *)
         search_and_backtrack candidates system
       end

(**************************************************************)
(* Backward reachability with approximations and backtracking *)
(**************************************************************)
    
let brab system =
  Oracle.init system;
  if only_forward then exit 0;
  search_and_backtrack [] system
