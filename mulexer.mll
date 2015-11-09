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

}

let newline = '\n'
let space = [' ' '\t' '\r']
let integer = ['0' - '9'] ['0' - '9']*
let ident = ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_' '.']*


rule token = parse
  | "State" space* (integer as n) ":" newline
      { Muparser_globals.new_state ();
        Muparser.state state lexbuf;
        STATE (int_of_string n) }
  | "Progress Report:" newline 
      { print_mu := !print_mu || not quiet; token lexbuf }
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
  | ident as id
      { (* Format.printf "lexing %s@." id; *) IDENT id }
  | integer as n 
      { (* Format.printf "lexing %s@." n; *) INT n }
  | '[' { LEFTSQ }
  | ']' { RIGHTSQ }
  | ':' { COLON }
  | _ as c
      { raise (Lexical_error ("illegal character: " ^ String.make 1 c)) }


