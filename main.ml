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

open Lexing
open Format
open Options
open Ast

(** Entry point of Cubicle *)



(** intercepts SIGINT [Ctrl-C] to display progress before exit *)
let () = 
  Sys.set_signal Sys.sigint 
    (Sys.Signal_handle 
       (fun _ ->
        eprintf "@{<n>@}@."; (* Remove colors *)
        Stats.print_report ~safe:false [] [];
        eprintf "\n\n@{<b>@{<fg_red>ABORT !@}@} Received SIGINT@.";
        exit 1)) 

let () = 
  Sys.set_signal Sys.sigterm
    (Sys.Signal_handle 
       (fun _ ->
        eprintf "@{<n>@}@."; (* Remove colors *)
        Stats.print_report ~safe:false [] [];
        eprintf "\n\n@{<b>@{<fg_red>ABORT !@}@} Received SIGTERM@.";
        exit 1)) 

(** intercepts SIGUSR1 to display progress *)
let () =
  try
    Sys.set_signal Sys.sigusr1 
      (Sys.Signal_handle 
         (fun _ ->
            eprintf "@{<n>@}@."; (* Remove colors *)
            Stats.print_report ~safe:false [] []))
  with Invalid_argument _ -> () (* doesn't exist on windows *)

let _ = 
  let lb = from_channel cin in 
  try
    let s = Parser.system Lexer.token lb in
    let system = Typing.system s in
    if type_only then exit 0;
    if refine_universal then
      printf "@{<b>@{<fg_yellow>Warning@} !@}\nUniversal guards refinement \
              is an experimental feature. Use at your own risks.\n@.";
    let close_dot = Dot.open_dot () in 
    let oc = 
      if res_output 
      then open_out_gen [Open_wronly; Open_append; Open_creat] 0o644 res_file
      else stdout in
    begin 
      if far then
	match Far.search system with
	  | Far.FSafe -> 
	    printf "\n\nThe system is @{<b>@{<fg_green>SAFE@}@}\n@.";
	    if (not quiet || profiling) then
              Stats.print_report ~safe:true [] [];
          | Far.FUnsafe -> 
	    printf "\n\n@{<b>@{<bg_red>UNSAFE@} !@}\n@.";
            if (not quiet || profiling) then
              Stats.print_report ~safe:false [] [];
            exit 1
      else 
        match Brab.brab system with
          | Bwd.Safe (visited, candidates) ->
            if (not quiet || profiling) then
              Stats.print_report ~safe:true visited candidates;
            if res_output then
              Stats.output_report oc ~safe:true visited candidates;
            
            printf "\n\nThe system is @{<b>@{<fg_green>SAFE@}@}\n@.";
            Trace.Selected.certificate system visited;
            close_dot ();
	    exit 0

          | Bwd.Unsafe (faulty, candidates) ->
            if (not quiet || profiling) then
              Stats.print_report ~safe:false [] candidates;
            if res_output then
              Stats.output_report oc ~safe:false [] candidates;
            if not quiet then Stats.error_trace system faulty;
            printf "\n\n@{<b>@{<bg_red>UNSAFE@} !@}\n@.";
            close_dot ();
            exit 1
    end
  with
  | Lexer.Lexical_error s -> 
     Util.report_loc err_formatter (lexeme_start_p lb, lexeme_end_p lb);
     eprintf "lexical error: %s@." s;
     exit 2

  | Parsing.Parse_error ->
     let loc = (lexeme_start_p lb, lexeme_end_p lb) in
     Util.report_loc err_formatter loc;
     eprintf "syntax error@.";
     exit 2

  | Typing.Error (e,loc) ->
     Util.report_loc err_formatter loc;
     eprintf "typing error: %a@." Typing.report e;
     exit 2

  | Stats.ReachedLimit ->
     if (not quiet || profiling) then Stats.print_report ~safe:false [] [];
     eprintf "\n@{<b>@{<fg_yellow>Reached Limit@} !@}\n";
     eprintf "It is likely that the search diverges, increase \
              the limit to explore further.@.";
     exit 1

  | Failure str ->
    
    let backtrace = Printexc.get_backtrace () in
    eprintf "\n@{<u>Internal failure:@}%s@." str;
    if verbose > 0 then eprintf "Backtrace:@\n%s@." backtrace;

    exit 1

  | Smt.Error e ->

    let backtrace = Printexc.get_backtrace () in
    eprintf "\n@{<u>Solver error:@}%a@." Smt.report e;
    if verbose > 0 then eprintf "Backtrace:@\n%s@." backtrace;

    exit 1

  | e ->

    let backtrace = Printexc.get_backtrace () in
    eprintf "Fatal error: %s@." (Printexc.to_string e);
    if verbose > 0 then eprintf "Backtrace:@\n%s@." backtrace
