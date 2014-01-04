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
        Gc.minor_heap_size = 32000000; (* default 32000*)
        (*major_heap_increment = 0;    (* default 124000*)*)
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
  begin
    try
      let s = Parser.system Lexer.token lb in
      let ts = Typing.system s in
      let ts = List.map Bwreach.init_parameters ts in
      Global.global_system := List.hd ts;
      Global.info := s;
      Translation.set_decl_map s;
      (* Fol__FOL.init_declarations s; *)
      if type_only then exit 0;

      let procs = Forward.procs_from_nb enumerative in
      eprintf "STATEFULL ENUMERATIVE FORWARD :\n-------------\n@.";
      Enumerative.search procs !Global.global_system;
      eprintf "-------------\n@.";
    
      let theta = match ts with 
	| [] -> assert false
	| _ -> Fol__FOL.cubes_to_fol ts 
      in
      let init = Fol__FOL.init_to_fol !Global.global_system in
      match Cubicle_brab_map__Cubicle_BRAB.brab init theta with
      | Cubicle_brab_map__Cubicle_BRAB.Safe ->
	 printf "\n\nThe system is @{<b>@{<fg_green>SAFE@}@}\n@.";
	 printf "timer: %f s@." (Prover.TimeF.get ());
      | Cubicle_brab_map__Cubicle_BRAB.Unsafe ->
	 printf "\n\n@{<b>@{<bg_red>UNSAFE@} !@}\n@."; exit 1
							     
							     
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
  end;
