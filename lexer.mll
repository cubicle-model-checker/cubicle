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
	"requires", REQUIRE;
        "array", ARRAY;
        "var", VAR;
        "const", CONST;
        "unsafe", UNSAFE;
	"case", CASE;
	"forall_other", FORALL_OTHER;
	"exists_other", EXISTS_OTHER;
	"forall", FORALL;
        "exists", EXISTS;
        "predicate", PREDICATE;
        "if", IF;
        "then", THEN;
        "else", ELSE;
        "not", NOT;
        "true", TRUE;
        "false", FALSE;
	"number_procs", SIZEPROC;
	"let", LET;
	"in", IN;
        "chan", CHAN;
      ]
	       
  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- 
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  let num_of_stringfloat s =
    let sign, s =
      if s.[0] = '-' then -1, String.sub s 1 (String.length s - 1)
      else 1, s in
    let r = ref (Num.Int 0) in
    let code_0 = Char.code '0' in
    let num10 = Num.Int 10 in
    let pos_dot = ref (-1) in
    for i=0 to String.length s - 1 do
      let c = s.[i] in
      if c = '.' then pos_dot := i 
      else
	r := Num.add_num (Num.mult_num num10 !r) 
	  (Num.num_of_int (Char.code s.[i] - code_0))
    done;
    assert (!pos_dot <> -1);
    Num.div_num !r
      (Num.power_num num10 (Num.num_of_int (String.length s - 1 - !pos_dot)))
    |> Num.mult_num (Num.num_of_int sign)

  let string_buf = Buffer.create 1024

  exception Lexical_error of string


}

let newline = '\n'
let space = [' ' '\t' '\r']
let integer = ('-')? ['0' - '9'] ['0' - '9']*
let real = ('-')? ['0' - '9'] ['0' - '9']* '.' ['0' - '9']* 
let mident = ['A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']*
let lident = ['a'-'z']['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule token = parse
  | newline 
      { newline lexbuf; token lexbuf }
  | space+  
      { token lexbuf }
  | lident as id
      { try Hashtbl.find keywords id
	with Not_found ->
	 if id = "bool" then LIDENT "mbool" else LIDENT id }
  | '#'(['1'-'9']['0'-'9']* as n) as id
      { if int_of_string n > !Options.size_proc then raise Parsing.Parse_error;
        CONSTPROC id }
  | mident as id {
		  if id = "True" then MIDENT "@MTrue"
		  else if id = "False" then MIDENT "@MFalse"
		  else MIDENT id }
  | real as r { REAL (num_of_stringfloat r) }
  | integer as i { INT (Num.num_of_string i) }
  | "("
      { LEFTPAR }
  | ")"
      { RIGHTPAR }
  | "."
      { DOT }
  | "?"
      { QMARK }
  | "!"
      { EMARK }
  | "+"
      { PLUS }
  | "-"
      { MINUS }
  | "*"
      { TIMES }
  | ":"
      { COLON }
  | "="
      { EQ }
  | "=>"
      { IMP }
  | "<=>"
      { EQUIV }
  | ":="
      { AFFECT }
  | "<>"
      { NEQ }
  | "<"
      { LT }
  | "<="
      { LE }
  | ">"
      { GT }
  | ">="
      { GE }
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
  | "'"
      { QUOTE }
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
  | newline 
      { newline lexbuf; comment lexbuf }
  | _ 
      { comment lexbuf }
