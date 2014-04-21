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

let report (b,e) =
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  printf "File \"%s\", line %d, characters %d-%d:" file l fc lc


let () = 
  Sys.set_signal Sys.sigint 
    (Sys.Signal_handle 
       (fun _ ->
        Stats.print_report ~safe:false [] [];
        eprintf "\n\n@{<b>@{<fg_red>ABORT !@}@} Received SIGINT@.";
        exit 1)) 

let () = 
  Sys.set_signal Sys.sigusr1 
    (Sys.Signal_handle 
       (fun _ -> Stats.print_report ~safe:false [] [])) 


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
    begin 
      match Brab.brab system with
      | Bwd.Safe (visited, candidates) ->
         if not quiet then Stats.print_report ~safe:true visited candidates;
         printf "\n\nThe system is @{<b>@{<fg_green>SAFE@}@}\n@.";
         Trace.Selected.certificate system visited;
         close_dot ();

      | Bwd.Unsafe (faulty, candidates) ->
         if not quiet then Stats.print_report ~safe:false [] candidates;
         if not quiet then Stats.error_trace system faulty;
         printf "\n\n@{<b>@{<bg_red>UNSAFE@} !@}\n@.";
         close_dot ();
         exit 1
    end
  with
  | Lexer.Lexical_error s -> 
     report (lexeme_start_p lb, lexeme_end_p lb);
     printf "lexical error: %s\n@." s;
     exit 2

  | Parsing.Parse_error ->
     let  loc = (lexeme_start_p lb, lexeme_end_p lb) in
     report loc;
     printf "\nsyntax error\n@.";
     exit 2

  | Typing.Error e -> 
     printf "typing error: %a\n@." Typing.report e;
     exit 2

  | Stats.ReachedLimit ->
     if not quiet then Stats.print_report ~safe:false [] [];
     eprintf "\n@{<b>@{<fg_yellow>Reached Limit@} !@}\n";
     eprintf "It is likely that the search diverges, increase \
              the limit to explore further.@.";
     exit 1

  | Failure str ->
     eprintf "\n@{<u>Internal failure:@}%s@." str;
     exit 1
