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

let () =
  if verbose > 0 then Printexc.record_backtrace true

let _ = 
  let lb = from_channel cin in 
  let s = Parser.system Lexer.token lb in
  Guiwindow.open_window s
  (* print_string (Psystem_printer.psystem_to_string s )  *)
