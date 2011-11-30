(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon, Universite Paris-Sud 11              *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
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

let _ = 
  let lb = from_channel cin in 
  try
    let s = Parser.system Lexer.token lb in
    let ts = Typing.system s in
    if !type_only then exit 0;
    Bwreach.system ts;
    printf "\n\nThe system is SAFE\n@."
  with
    | Lexer.Lexical_error s -> 
	report (lexeme_start_p lb, lexeme_end_p lb);
	printf "lexical error: %s\n@." s;
	exit 2
    | Parsing.Parse_error ->
	let  loc = (lexeme_start_p lb, lexeme_end_p lb) in
	report loc;
        printf "syntax error\n@.";
	exit 2
    | Typing.Error e -> 
	printf "typing error: %a\n@." Typing.report e;
	exit 2
    | Search.ReachBound ->
	printf "reach bound\n@.";
	exit 1
    | Search.Unsafe ->
	printf "\n\nUNSAFE !\n@.";
	exit 1

