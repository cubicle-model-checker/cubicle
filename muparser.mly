/**************************************************************************/
/*                                                                        */
/*                              Cubicle                                   */
/*                                                                        */
/*                       Copyright (C) 2011-2015                          */
/*                                                                        */
/*                  Sylvain Conchon and Alain Mebsout                     */
/*                       Universite Paris-Sud 11                          */
/*                                                                        */
/*                                                                        */
/*  This file is distributed under the terms of the Apache Software       */
/*  License version 2.0                                                   */
/*                                                                        */
/**************************************************************************/

%{

  open Parsing
  open Format

  let st = ref 0

  let new_state () = incr st

  let register_state () = printf "  finished %d@." !st

%}

%token ENDSTATE LEFTSQ RIGHTSQ COLON EOF
%token <string> IDENT
%token <int> INT
%token <int> STATE

%type <unit> states
%start states

%type <unit> state
%start state

%%


states:
  | EOF { () }
  | state_list EOF { () }
;
  
state_list:
  | statenb { () }
  | statenb state_list { () }
;

statenb:
  | STATE { printf ">> %d@." $1 }
;
  
state:
  | affectations ENDSTATE { register_state () }
;

/*
begin_state:
  | STATE { printf "Parsing state %d ...@." $1; new_state () }
;
*/

affectations:
  | affectation { () }
  | affectation affectations { () }
;

value:
  | IDENT { $1 }
  | INT { string_of_int $1 }
;

var:
  | IDENT { $1 }
  | IDENT LEFTSQ IDENT RIGHTSQ { $1 ^ "[" ^ $3 ^ "]" }
;

affectation:
  | var COLON value { (* printf "%s -> %s\n" $1 $3 *) () }
;


