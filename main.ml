(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2013                          *)
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

let set_gc_control =
  let gc_c = Gc.get() in
  let gc_c =
    { gc_c with
        (* Gc.verbose = 0x3FF; *)
        Gc.minor_heap_size = 64000000; (* default 32000*)
        (* major_heap_increment = 3200000;    (\* default 124000*\) *)
        space_overhead = 80; (* default 80% des donnes vivantes *)
    }
  in
  Gc.set gc_c

let report (b,e) =
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  printf "File \"%s\", line %d, characters %d-%d:" file l fc lc

let _ = 
  let lb = from_channel cin in 
  try
    let s = Parser.system Lexer.token lb in
    let _ = Typing.system s in
    let _ = Scheduler.scheduler s in ();
    (*if bitsolver then Bitsolver.init_env (List.hd ts) max_proc;
    if type_only then exit 0;
    Bwreach.system ts;
    if dot then eprintf "\n\nThe system is @{<b>@{<fg_green>SAFE@}@}\n@."
    else printf "\n\nThe system is @{<b>@{<fg_green>SAFE@}@}\n@.";
    if refine_universal then
      printf "@{<b>@{<fg_yellow>Warning@} !@}\nUniversal guards refinement is an experimental feature. Use at your own risks.\n@."*)
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
    | ReachBound ->
	printf "reach bound\n@.";
	exit 1
    | Search.Unsafe s ->
        if refine_universal && Forward.spurious_error_trace s then
          printf "\n\n@{<b>@{<fg_yellow>Spurious trace@} !@}\n@."
	else printf "\n\n@{<b>@{<bg_red>UNSAFE@} !@}\n@.";
	exit 1

