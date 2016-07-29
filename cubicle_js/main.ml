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
open Lwt

let open_window = ref None 

let main input_str display =
  let lb = Lexing.from_string (Js.to_string (input_str)) in
  (try
    (match !open_window with 
       |None -> ()
       |Some w -> w##close ());
     if display then 
       ignore (Dom_html.window##setTimeout (Js.wrap_callback ( fun _ -> 
         let wnd = Dom_html.window##open_ (Js.string "trace.html", Js.string "Cubicle Trace View", Js.null) in
         open_window := Some wnd
        ), 1000.));
     let s = Parserc.system Lexerc.token lb in
     let system = Typing.system s in
    (* add_debug "Typing OK"; *)
     if type_only then exit 0;
    if refine_universal then
      printf "@{<b>@{<fg_yellow>Warning@} !@}\nUniversal guards refinement \
              is an experimental feature. Use at your own risks.\n@.";
    let close_dot = Dot.open_dot () in
    Firebug.console##log (Js.string "avant cub");
    Brab.brab system;
    let rec loop () = 
      if (not !Bwd.loop_done) then 
        (ignore (Dom_html.window##setTimeout (Js.wrap_callback (loop), 0.));
         Firebug.console##log (Js.string "not done"))
    else 
        begin
          Firebug.console##log (Js.string "done");
          match !Bwd.loop_res with 
            |None -> Firebug.console##log (Js.string ("none"));
          |Some s -> 
            match s with 
              |Bwd.Safe (visited, candidates) -> 
                Stats.print_report ~safe:true visited candidates;
              |Bwd.Unsafe (faulty, candidates) -> 
                Stats.print_report ~safe:false [] candidates;
                Stats.error_trace system faulty;

        end  
    in 
    loop ()     
  with
  | Lexer.Lexical_error s ->
    Util.report_loc err_formatter (lexeme_start_p lb, lexeme_end_p lb);
     eprintf "lexical error: %s@." s

  | Parsing.Parse_error ->
     let loc = (lexeme_start_p lb, lexeme_end_p lb) in
     Util.report_loc err_formatter loc;
     eprintf "syntax error@."

  | Typing.Error (e,loc) ->
     Util.report_loc err_formatter loc;
     eprintf "typing error: %a@." Typing.report e

  | Stats.ReachedLimit ->
     if (not quiet || profiling) then Stats.print_report ~safe:false [] [];
     eprintf "\n@{<b>@{<fg_yellow>Reached Limit@} !@}\n";
     eprintf "It is likely that the search diverges, increase \
              the limit to explore further.@."

  | Failure str ->
    eprintf "\n@{<u>Internal failure:@}%s@." str)



       
let get_storage () =
  match Js.Optdef.to_option Dom_html.window##localStorage with
    | None -> raise Not_found
    | Some t -> t
      
(* let _ = *)

(*   (\* Dom_html.window##onload <- Dom_html.handler *\) *)
(*   (\*   ( fun ev -> *\) *)
(*       let e = Js.Unsafe.variable "editor2" in *)
(*       let input_str = e##getValue() in *)
(*       let textareaE = Dom_html.getElementById "input" in *)
(*       main input_str false  *)
(*       let buttonE = Dom_html.getElementById "display-trace" in *)
(*       let button = *)
(*         match Js.Opt.to_option (Dom_html.CoerceTo.button buttonE) with *)
(*           |None -> failwith "button display trace not found" *)
(*           |Some b -> b in *)
(*       button##onclick <- Dom.handler (fun _ -> main input_str true  ; Js._false); *)
(*     let buttonE = Dom_html.getElementById "run-cubicle" in *)
(*       let button = *)
(*         match Js.Opt.to_option (Dom_html.CoerceTo.button buttonE) with *)
(*           |None -> failwith "button display trace not found" *)
(*           |Some b -> b in *)
(*       button##onclick <- Dom.handler (fun _ -> main input_str false  ; Js._false); *)
(*        (\* Js._false); *\) *)
