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

{
  (* This program is free software.  See LICENSE for more information *)
  open Lexing
  open Smt_parser
    
  exception Lexical_error of string

  let attribute = 
    let h = Hashtbl.create 17 in
    List.iter (fun (s,k) -> Hashtbl.add h s k)
      [	"assumption", ASSUMPTION_ATRB;
	"axioms", AXIOMS_ATRB;
	"definition", DEFINITION_ATRB;
	"extensions", EXTENSIONS_ATRB;
	"formula", FORMULA_ATRB;
	"funs", FUNS_ATRB;
	"extrafuns", EXTRAFUNS_ATRB;
	"extrasorts", EXTRASORTS_ATRB;
	"extrapreds", EXTRAPREDS_ATRB;
	"language", LANGUAGE_ATRB;
	"logic", LOGIC_ATRB;
	"notes", NOTES_ATRB;
	"preds", PREDS_ATRB;
	"sorts", SORTS_ATRB;
	"status", STATUS_ATRB;
	"theory" , THEORY_ATRB
      ];
    fun s -> 
      try Hashtbl.find h s with Not_found -> ATTRIBUTE s


  let id_or_keyword = 
    let h = Hashtbl.create 17 in
    List.iter (fun (s,k) -> Hashtbl.add h s k)
      [ "true", TRUE;
	"false", FALSE;
	"ite",  ITE;
	"not", NOT;
	"implies", IMPLIES;
	"if_then_else",  IFTHENELSE;
	"and", AND;
	"or",  OR;
	"xor", XOR;
	"iff", IFF;
	"exists", EXISTS;
	"forall", FORALL;
	"let", LET;
	"flet", FLET;
	"sat", SAT ;
	"unsat", UNSAT;
	"unknown", UNKNOWN;
	"benchmark", BENCHMARK;
	"theory", THEORY;
	"logic", LOGIC;
	"distinct", DISTINCT
      ];
    fun s -> 
      try Hashtbl.find h s with Not_found -> ID s

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- 
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum; 
        pos_cnum=0 }

}

let alpha = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let identifier = alpha (alpha | digit | '.' | '\'' | '_')*
let numeral = digit+
let rational = numeral '.' numeral
let ar_symb = ['=' '<' '>' '&' '@' '#' '+' '-' '*' '/' '%' '|' '~']+ 

rule token = parse
    '\n' 
      { newline lexbuf ; token lexbuf }
  | [' ' '\t' '\r'] 
      { token lexbuf }
  | '"' 
      { string (Buffer.create 1024) lexbuf }
  | '{' 
      { user_value (Buffer.create 1024) lexbuf }
  | '(' 
      { LP }
  | ')' 
      { RP }
  | "=" 
      { EQUALS }
  | ';' ' '* "rewriting rule" [^'\n']*  "\n" [' ' '\t' '\r']* ":assumption"
      { newline lexbuf; REWRITING_ATRB }
  | ';' [^'\n']* "\n" 
      { newline lexbuf; token lexbuf }  
  | ar_symb
      { ARSYMB(Lexing.lexeme lexbuf) }
  | identifier
      { id_or_keyword (Lexing.lexeme lexbuf) }
  | numeral
      { NUMERAL(Lexing.lexeme lexbuf) }
  | (numeral as e) '.' (numeral as d)
      { let s = "1"^(String.make (String.length d) '0') in
	(* RATIONAL(e^d^"/"^s) } *)
      NUMERAL(e^d^"/"^s) }
(*  | rational
      { RATIONAL(Lexing.lexeme lexbuf) }*)
  | '?' identifier
      { VAR(Lexing.lexeme lexbuf) }
  | '$' identifier 
      { FVAR(Lexing.lexeme lexbuf) }
  | ':' ( identifier as id)
      { attribute id }
  | eof   
      { EOF }
  | _ 
      { raise (Lexical_error ("illegal character: " ^ lexeme lexbuf)) }

and user_value buf = parse
| '\n'   { newline lexbuf; Buffer.add_char buf '\n' ; user_value buf lexbuf}
| '}'    { USER_VALUE (Buffer.contents buf) }
| _ as c { Buffer.add_char buf c; user_value buf lexbuf }
| eof    { raise (Lexical_error ("unterminated annotation")) }

and string buf = parse
| '"'    { STRING (Buffer.contents buf) }
| '\n'   { newline lexbuf; Buffer.add_char buf '\n' ; string buf lexbuf}
| "\\\"" { Buffer.add_char buf '"'; string buf lexbuf }
| _ as c { Buffer.add_char buf c; string buf lexbuf }
| eof    { raise (Lexical_error ("unterminated string")) }
