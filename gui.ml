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


let _ = 
  let lb = from_channel cin in 
  try 
    let s = Parser.system Lexer.token lb in
    Guiwindow.open_window s
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
