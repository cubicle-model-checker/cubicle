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


(* Tell cubicle that we are executing the javascript version *)
set_js_mode true

let doc = Dom_html.document
let window = Dom_html.window
let button_type = Js.string "button"

let text_button txt action =
  let b = Dom_html.createDiv doc in
  let id = "button"^txt in
  b##innerHTML <- Js.string txt;
  b##id <- Js.string id;
  b##className <- Js.string "btn";
  b##onclick <- Dom_html.handler (fun _ -> action (); Js._true);
  b

let get_element_by_id id =
  Js.Opt.get (doc##getElementById (Js.string id))
    (fun () -> assert false)

let set_by_id id s =
  let container = get_element_by_id id in
  container##innerHTML <- Js.string s

let set_container_by_id id s =
  try
    set_by_id id s
  with _ -> ()


let set_action_by_id id action =
  let b = get_element_by_id id in
  b##onclick <- Dom_html.handler (fun _ -> action (); Js._true)


let append_children id list =
  let ele = get_element_by_id id in
  List.iter (fun w -> Dom.appendChild ele w) list


let extract_escaped_and_kill html i =
  let len = String.length html in
  let rec iter html i len =
    if i = len then i else
      match html.[i] with
        ';' -> i+1
      | _ -> iter html (i+1) len
  in
  let end_pos = iter html (i+1) len in
  let s = String.sub html i (end_pos - i) in
  for j = i to end_pos - 1 do
    html.[j] <- '\000'
  done;
  s

let text_of_html html =
  let b = Buffer.create (String.length html) in
  for i = 0 to String.length html - 1 do
    match html.[i] with
      '&' ->
        begin
          match extract_escaped_and_kill html i with
          | "&gt;" -> Buffer.add_char b '>'
          | "&lt;" -> Buffer.add_char b '<'
          | "&amp;" -> Buffer.add_char b '&'
          | _ -> ()
        end
    | '\000' -> ()
    | c -> Buffer.add_char b c
  done;
  Buffer.contents b

exception TimeOut

let get_by_id id =
  let container = get_element_by_id id in
  Js.to_string container##innerHTML

let get_textarea_by_id name =
  Js.Opt.get (Dom_html.CoerceTo.textarea (get_element_by_id name))
             (fun _ -> assert false)

let js_verbose = ref true
let debug_str = ref ""


let add_debug str =
  if !js_verbose then
    debug_str := sprintf "%s\n<div>%s</div>" !debug_str str;
  if !js_verbose then set_by_id "debug-content-dynamic" !debug_str



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
