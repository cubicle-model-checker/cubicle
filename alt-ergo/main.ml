(**************************************************************************)
(*                                                                        *)
(*     The Alt-ergo theorem prover                                        *)
(*     Copyright (C) 2006-2010                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
(*     Alain Mebsout                                                      *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

open Why_ptree
open Frontend

open Lexing
open Format
open Options

let _ = 
  Sys.set_signal Sys.sigint 
    (Sys.Signal_handle 
       (fun _ -> print_endline "User wants me to stop."; exit 1))	  



let print_status d s steps =
  let satmode = !smtfile or !smt2file or !satmode in 
  match s with
    | Unsat dep -> 
	if not satmode then Loc.report d.st_loc;
	if satmode then printf "@{<C.F_Red>unsat@}@." 
	else printf "@{<C.F_Green>Valid@} (%2.4f) (%Ld)@." (Time.get()) steps;
	if proof && not debug_proof then 
          printf "Proof:\n%a@." Explanation.print_proof dep
	  
    | Inconsistent ->
	if not satmode then 
	  (Loc.report d.st_loc; 
	   fprintf fmt "Inconsistent assumption@.")
	else printf "unsat@."
	  
    | Unknown ->
	if not satmode then
	  (Loc.report d.st_loc; printf "I don't know.@.")
	else printf "unknown@."
	  
    | Sat  -> 
	if not satmode then Loc.report d.st_loc;
	if satmode then printf "unknown (sat)@." 
	else printf "I don't know@."



let main _ = 
  let lb = from_channel cin in 
  try 
    let d, status = open_file !file lb in 
    processing print_status d
  with
    | Why_lexer.Lexical_error s -> 
	Loc.report (lexeme_start_p lb, lexeme_end_p lb);
	printf "lexical error: %s\n@." s;
	exit 1
    | Parsing.Parse_error ->
	let  loc = (lexeme_start_p lb, lexeme_end_p lb) in
	Loc.report loc;
        printf "syntax error\n@.";
	exit 1
    | Common.Error(e,l) -> 
	Loc.report l; 
	printf "typing error: %a\n@." Common.report e;
	exit 1

let _ = main ();

