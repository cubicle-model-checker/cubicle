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
open Options
open Parsing
open Format
open Muparser_globals

let get_args_of s =
  if String.length s = 0 then []
  else
    let l = ref [] in
    let i = ref 1 in
    let j = ref (String.length s) in
    try
      while true do
        i := String.index_from s !i ':' + 1;
        j := (try String.index_from s !i ' ' with Not_found -> String.length s);
        l := String.sub s !i (!j - !i) :: !l;
        i := !j;
      done;
      assert false
    with Not_found -> List.rev !l

let rename_proc s =
  Scanf.sscanf s "%s@_%d" (fun _ d -> "#" ^ string_of_int d)

let rename_procs l =
  List.fold_left
    (fun acc s -> try rename_proc s :: acc with _ -> acc)
    [] l |> List.rev 

%}

%token ENDSTATE EOF
%token <string * string> AFFECTATION
%token <int> STATE                  
%token <string * string> STEP                  
%token <string> ENDTRACE
/*
%token LEFTSQ RIGHTSQ COLON
%token <string> IDENT
%token <string> INT
*/

%type <unit> states
%start states

%type <unit> state
%start state

%type <unit> error_trace
%start error_trace

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
  | STATE { if max_forward <> -1 && $1 > max_forward then
              Unix.kill (Unix.getpid ()) Sys.sigint
    (* printf "%d@." $1 *) }
;
  
state:
  | affectations ENDSTATE { Enumerative.register_state !env !st
    (* Enumerative.print_last !Muparser_globals.env *) }
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

/*
value:
  | IDENT { $1 }
  | INT { $1 }
;

var:
  | IDENT { $1 }
  | var LEFTSQ INT RIGHTSQ { $1 ^ "[" ^ $3 ^ "]" }
  | var LEFTSQ IDENT RIGHTSQ { $1 ^ "[" ^ $3 ^ "]" }
;
*/

affectation:
  | AFFECTATION
    { try
        let v, x = $1 in
        (* eprintf "%s -> %s@." v x; *)
        let id_var = Hashtbl.find encoding v in
        let id_value = Hashtbl.find encoding x in
        let si = (!st :> int array) in
        si.(id_var) <- id_value
      with Not_found -> ()
    }
  /* less efficient to parse these tokens */
  /*                     
  | var COLON value
    { try
        let id_var = Hashtbl.find encoding $1 in
        let id_value = Hashtbl.find encoding $3 in
        let si = (!st :> int array) in
        si..(id_var) <- id_value
      with Not_found -> ()
    }
  */
;

trace_step:
  | STEP affectations ENDSTATE
    { let name, sargs = $1 in
      let args = get_args_of sargs |> rename_procs in
      let ra = String.concat ", " args in
      printf "@[<hov4>%s(%s) ->" name ra;
      if verbose > 0 then
        printf "@ %a" (Enumerative.print_state !env) !st;
      printf "@ @]@,";
      let si = (!st :> int array) in
      for i = 0 to Array.length si - 1 do si.(i) <- -1 done
    }
;

trace:
  | trace_step { () }
  | trace trace_step { () }
;

error_trace:
  | trace ENDTRACE
    { printf "@,@{<fg_magenta>%s@}@]@." $2;
      printf "\n\n@{<b>@{<bg_red>UNSAFE@} !@}\n@.";
      exit 1 }
;
