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
open Js_helper

(* Tell cubicle that we are executing the javascript version *)
set_js_mode true


let main _ =

  debug_str := "";

  let textarea = get_textarea_by_id "input" in
  let input_str = Js.to_string textarea##value in
  (*  let s = text_of_html (get_by_id "input") in *)
  (*  Printf.printf "INPUT[%s]\n" s; *)
  (* add_debug ("File "^Options.file); *)
  add_debug ("INPUT\n-----\n"^input_str);
  let lb = from_string input_str in
  add_debug "Lexing OK";
   
  try
    let s = Parser.system Lexer.token lb in
    add_debug "Parsing OK";
    let system = Typing.system s in
    add_debug "Typing OK";
    if type_only then exit 0;

    if refine_universal then
      printf "@{<b>@{<fg_yellow>Warning@} !@}\nUniversal guards refinement \
              is an experimental feature. Use at your own risks.\n@.";
    let close_dot = Dot.open_dot () in
    begin
      match Brab.brab system with
      | Bwd.Safe (visited, candidates) ->
         if (not quiet || profiling) then
           Stats.print_report ~safe:true visited candidates;
         printf "\n\nThe system is @{<b>@{<fg_green>SAFE@}@}\n@.";
         Trace.Selected.certificate system visited;
         close_dot ();

      | Bwd.Unsafe (faulty, candidates) ->
         if (not quiet || profiling) then
           Stats.print_report ~safe:false [] candidates;
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

  (* | Stats.ReachedLimit -> *)
  (*    if (not quiet || profiling) then Stats.print_report ~safe:false [] []; *)
  (*    eprintf "\n@{<b>@{<fg_yellow>Reached Limit@} !@}\n"; *)
  (*    eprintf "It is likely that the search diverges, increase \ *)
  (*             the limit to explore further.@."; *)
  (*    exit 1 *)

  | Failure str ->
     eprintf "\n@{<u>Internal failure:@}%s@." str;
     exit 1

(* TODO web workers, see http://toss.sourceforge.net/ocaml.html *)

let _ =
  
  let textarea = get_textarea_by_id "input" in  
  set_by_id "version" Version.version;
  
  add_debug ("Executation");

  set_action_by_id "run-cubicle"
                   (fun () ->
                    set_by_id "output" "";
                    main ();
                   );

  set_action_by_id "clearbtn"
                   (fun _ ->
                    textarea##value <- Js.string "";
                    (* set_by_id "filename" ""; *)
                    set_by_id "output" "";
                    (* set_by_id "statistics-content-dynamic" ""; *)
                    set_by_id "debug-content-dynamic" "";
                   );
