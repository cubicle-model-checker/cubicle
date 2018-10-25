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


(** Print backtrace even in native mode *)
let () =
  if verbose > 0 then Printexc.record_backtrace true


let _ =
  let lb = from_channel cin in
  try
    let s = Parser.system Lexer.token lb in
    let system = Typing.system s in
    if type_only then exit 0;
    let close_dot = Dot.open_dot () in
    if towhy3 then begin
      let out =
        if Options.why3_out_file then
          let dir = Filename.("examples" ^ dir_sep ^ "why3" ^ dir_sep) in
          let nf = Filename.((remove_extension @@ basename file) ^ "test.mlw") in
          let cout = open_out (dir ^ nf) in
          Format.formatter_of_out_channel cout
        else
          Format.std_formatter
      in
      let invs =
        begin
          match Brab.brab system with
            | Bwd.TimeOut (visited, _) | Bwd.Safe (visited, _) ->
              List.fold_left (fun acc n ->
                if n.approximated || n.deleted then acc else n :: acc
              ) [] visited
            | Bwd.Unsafe (faulty, candidates) ->
              close_dot ();
              exit 1
        end
      in
      Format.fprintf out "%a" (Why3.cub_to_whyml s invs) Options.file
    end;
    if refine_universal then
      printf "@{<b>@{<fg_yellow>Warning@} !@}\nUniversal guards refinement \
              is an experimental feature. Use at your own risks.\n@.";
    begin
      match Brab.brab system with
        | Bwd.TimeOut (visited, candidates) ->
          if (not quiet || profiling) then
            Stats.print_report ~safe:true visited candidates;
          printf "\n\nThe system reached a @{<b>@{<fg_blue>TIMEOUT@}@}\n@.";
          Trace.Selected.certificate system visited;
          close_dot ();
          exit 0

        | Bwd.Safe (visited, candidates) ->
          if (not quiet || profiling) then
            Stats.print_report ~safe:true visited candidates;
          printf "\n\nThe system is @{<b>@{<fg_green>SAFE@}@}\n@.";
          Trace.Selected.certificate system visited;
          close_dot ();
          exit 0

        | Bwd.Unsafe (faulty, candidates) ->
          if (not quiet || profiling) then
            Stats.print_report ~safe:false [] candidates;
          begin try
              if not quiet then Stats.error_trace system faulty;
              printf "\n\n@{<b>@{<bg_red>UNSAFE@} !@}\n@.";
            with Exit -> ()
          end;
          close_dot ();
          exit 1
    end
  with
    | Lexer.Lexical_error s ->
      Util.report_loc err_formatter (lexeme_start_p lb, lexeme_end_p lb);
      eprintf "lexical error: %s@." s;
      exit 2

    | Parser.Error ->
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
      if verbose > 0 then eprintf "Backtrace:@\n%s@." backtrace;

      exit 1
