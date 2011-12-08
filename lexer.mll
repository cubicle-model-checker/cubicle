(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                  Universite Paris-Sud 11                               *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

{
  open Lexing
  open Parser

  let keywords = Hashtbl.create 97
  let () = 
    List.iter 
      (fun (x,y) -> Hashtbl.add keywords x y)
      [ "type", TYPE;
	"init", INIT;
	"transition", TRANSITION;
	"invariant", INVARIANT;
	"require", REQUIRE;
	"uguard", UGUARD;
	"assign", ASSIGN;
        "arrays", ARRAYS;
        "globals", GLOBALS;
        "nondet", NONDET;
        "unsafe", UNSAFE;
      ]
	       
  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- 
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  let string_buf = Buffer.create 1024

  exception Lexical_error of string


}

let newline = '\n'
let space = [' ' '\t' '\r']
let integer = ['0' - '9'] ['0' - '9']*
let mident = ['A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']*
let lident = ['a'-'z']['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule token = parse
  | newline 
      { newline lexbuf; token lexbuf }
  | space+  
      { token lexbuf }
  | lident as id
      { try Hashtbl.find keywords id
	with Not_found -> LIDENT id }
  | mident as id { MIDENT id }
  | integer as i { INT (int_of_string i) }
  | "("
      { LEFTPAR }
  | ")"
      { RIGHTPAR }
  | "."
      { DOT }
  | "+"
      { PLUS }
  | "-"
      { MINUS }
  | ":"
      { COLON }
  | "="
      { EQ }
  | ":="
      { AFFECT }
  | "<>"
      { NEQ }
  | "<"
      { LT }
  | "<="
      { LE }
  | "["
      { LEFTSQ }
  | "]"
      { RIGHTSQ }
  | "{"
      { LEFTBR }
  | "}"
      { RIGHTBR }
  | "||"
      { OR }
  | "|"
      { BAR }
  | ","
      { COMMA }
  | ";"
      { PV }
  | '_'
      { UNDERSCORE }
  | "&&"
      { AND }
  | "(*"
      { comment lexbuf; token lexbuf }
  | eof 
      { EOF }
  | _ as c
      { raise (Lexical_error ("illegal character: " ^ String.make 1 c)) }

and comment = parse
  | "*)" 
      { () }
  | "(*" 
      { comment lexbuf; comment lexbuf }
  | eof
      { raise (Lexical_error "unterminated comment") }
  | _ 
      { comment lexbuf }
