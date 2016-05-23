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
  let s = Parser.system Lexer.token lb in
  print_string (Astprinter.print_ast s);
  Guiwindow.open_window s
