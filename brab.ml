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
let rec search_and_backtrack candidates system =
  let res = BWD.search ~candidates system in
  match res with
  | Bwd.Safe _ -> res
  | Bwd.Unsafe (faulty, candidates) ->
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
         (* Restarting *)
         search_and_backtrack candidates system
       end

(** intercepts SIGINT [Ctrl-C] to display progress before exit *)
let reinstall_sigint () = 
  Sys.set_signal Sys.sigint 
    (Sys.Signal_handle 
       (fun _ ->
          eprintf "@{<n>@}@."; (* Remove colors *)
          Stats.print_report ~safe:false [] [];
          eprintf "\n\n@{<b>@{<fg_red>ABORT !@}@} Received SIGINT@.";
          exit 1)) 

(**************************************************************)
(* Backward reachability with approximations and backtracking *)
(**************************************************************)

let brab system =
  Oracle.init system;
  if only_forward then exit 0;
  reinstall_sigint ();
  search_and_backtrack [] system
