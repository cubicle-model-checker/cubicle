(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2015                          *)
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
  open Options
  open Lexing
  open Muparser

  let print_mu = ref debug

  let string_buf = Buffer.create 1024

  exception Lexical_error of string

  let rule_trace = ref ""

}

let newline = '\n'
let space = [' ' '\t' '\r']
let integer = ['0' - '9'] ['0' - '9']*
let ident = ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_' '.']*
let str = [^ '"']*
            
let var = ident ('[' (ident | integer) ']')*
          
rule token = parse
  | "State" space* (integer as n) ":" newline
      { Muparser_globals.new_state ();
        Muparser.state state lexbuf;
        STATE (int_of_string n) }
  | "Progress Report:" newline 
      { print_mu := !print_mu || not quiet; token lexbuf }
  | "Invariant \"" (str as s) "\" failed." newline
      { Muparser_globals.new_state ();
        Format.printf "\n@{<fg_red>Error trace@}:@[<hov> ";
        rule_trace := s;
        Muparser.error_trace error lexbuf;
        token lexbuf }
  | eof 
      { EOF }
  | newline
      { if !print_mu then print_newline (); token lexbuf }
  | _ as c
      { if !print_mu then print_char c; token lexbuf }

and state = parse
  | newline space* newline
      { ENDSTATE }
  | space+ | newline
      { state lexbuf }
  | (var as v) ':' (ident | integer as x)
      { AFFECTATION (v, x) }
  (* Less efficient to generate tokens *)
  (* | ident as id *)
  (*     { (\* Format.printf "lexing %s@." id; *\) IDENT id } *)
  (* | integer as n  *)
  (*     { (\* Format.printf "lexing %s@." n; *\) INT n } *)
  (* | '[' { LEFTSQ } *)
  (* | ']' { RIGHTSQ } *)
  (* | ':' { COLON } *)
  | _ as c
      { raise (Lexical_error
                 ("illegal character in murphi state: " ^ String.make 1 c)) }

and error = parse
  | "----------"
      { ENDSTATE }
  | "End of the error trace."
      { ENDTRACE !rule_trace }
  | ident space+ (ident as t)
    ((',' space* ident ':' ident)* as v) space+ "fired." newline
      { STEP (t, v) }
  | (var as v) ':' (ident | integer as x)
      { AFFECTATION (v, x) }
  (* | space+ | newline *)
  (*     { error lexbuf } *)
  | _ (* as c *)
      { error lexbuf }
