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

open Lexing
open Format
open Options
open Ast
open Js_helper
open Lwt

(* Tell cubicle that we are executing the javascript version *)
set_js_mode true

(* set_nocolor true *)

let main _ =

  (* debug_str := ""; *)


  (* let textarea = get_textarea_by_id "input" in *)
  (* let input_str = Js.to_string textarea##value in *)
  (* (\*  let s = text_of_html (get_by_id "input") in *\) *)
  (* (\*  Printf.printf "INPUT[%s]\n" s; *\) *)
  (* (\* add_debug ("File "^Options.file); *\) *)
  (* add_debug ("INPUT\n-----\n"^input_str); *)
(*   let input_str = " *)
(* var Turn : proc *)
(* array Want[proc] : bool *)
(* array Crit[proc] : bool *)

(* init (z) { Want[z] = False && Crit[z] = False } *)

(* unsafe (z1 z2) { Crit[z1] = True && Crit[z2] = True } *)

(* transition req (i) *)
(* requires { Want[i] = False } *)
(* { Want[i] := True } *)

(* transition enter (i) *)
(* requires { Want[i]=True && Crit[i] = False && Turn = i} *)
(* { Crit[i] := True; } *)

(* transition exit (i) *)
(* requires { Crit[i] = True } *)
(* {  *)
(*   Turn := . ; *)
(*   Crit[i] := False;  *)
(*   Want[i] := False *)
(* } *)

(* " *)
(*   in *)
  let input_str =
"type req = Empty | Reqs | Reqe | Inv | Invack
type cstate = Invalid | Shared | Exclusive

var Exgntd : bool
var Curcmd : req
var Curptr : proc

array Cache[proc] : cstate
array Shrset[proc] : bool
array Chan[proc] : req

init (z) { Cache[z] = Invalid && Shrset[z] = False &&
           Exgntd = False && Curcmd = Empty && Chan[z]=Empty }

(*
invariant (z) { Cache[z] = Exclusive && Exgntd  = False }
invariant (z) { Cache[z] = Shared && Shrset[z] = False }
*)

unsafe (z1 z2) { Cache[z1] = Exclusive && Cache[z2] = Shared }

transition send_shared (n)
requires { Chan[n] = Empty && Cache[n] = Invalid }
{ 
  Chan[j] := case 
  	      | j = n : Reqs 
	      | _ : Chan[j] 
}

transition recv_shared (n)
requires { Curcmd = Empty && Chan[n] = Reqs }
{ 
  Curcmd := Reqs; 
  Curptr := n ;
  Chan[j] := case
  	      | j = n : Empty 
	      | _ : Chan[j] 
}
    
transition send_exclusive (n)
requires { Chan[n] = Empty && Cache[n] <> Exclusive }
{ 
  Chan[j] := case 
  	      | j = n : Reqe 
	      | _ : Chan[j] 
}

transition recv_exclusive (n)
requires { Curcmd = Empty && Chan[n] = Reqe }
{ 
  Curcmd := Reqe; 
  Curptr := n ;
  Chan[j] := case 
  	      | j = n : Empty 
	      | _ : Chan[j] 
}
    
transition sendinv_1 (n)
requires { Chan[n] = Empty && Shrset[n]=True  &&  Curcmd = Reqe }
{ 
  Chan[j] := case 
  	      | j = n : Inv 
	      | _ : Chan[j] 
}

transition sendinv_2 (n)
requires { Chan[n] = Empty && Shrset[n]=True  &&
	   Curcmd = Reqs && Exgntd=True }
{ 
  Chan[j] := case 
  	      | j = n : Inv 
	      | _ : Chan[j] 
}

transition recv_inv(n)
requires { Chan[n] = Inv }
{ 
  Chan[j] := case 
  	      | j = n : Invack 
	      | _ : Chan[j] ;
  Cache[j] := case 
  	       | j = n : Invalid 
	       | _ : Cache[j] 
}
    
transition recv_invack(n)
requires { Chan[n] = Invack && Curcmd <> Empty }
{ 
  Exgntd := False;
  Chan[j] := case
  	      | j = n : Empty 
	      | _ : Chan[j] ;
  Shrset[j] := case 
  	        | j = n : False 
		| _ : Shrset[j] 
}

transition gnt_shared (n)
requires { Curptr = n && Curcmd = Reqs && Exgntd = False }
{ 
  Curcmd := Empty;
  Shrset[j] := case 
  	       	| j = n : True 
		| _ : Shrset[j];
  Cache[j] := case 
  	       | j = n : Shared 
	       | _ : Cache[j] 
}

transition gnt_exclusive (n)
requires { Shrset[n] = False && Curcmd = Reqe && Exgntd = False && Curptr = n &&
	   forall_other l. Shrset[l] = False }
{ 
  Curcmd := Empty; 
  Exgntd := True;
  Shrset[j] := case
  	        | j = n : True 
		| _ : Shrset[j];
  Cache[j] := case 
  	       | j = n : Exclusive 
	       | _ : Cache[j] 
}

" in
  let input_st = "
var A : int 
var B : int
var C : int
var D : int
var E : int
var F : int
var G : int

init () { A = 0 && B = 0 && C = 0 && D = 0 && E = 0 &&
          1 <= F && 1 <= G } 

unsafe (z) { A = 0 && B = 0 && D = 0 && E = 0 && F = 0 }
unsafe (z) { B = 0 && D = 0 && E = 0 && F = 0 && G = 0 }

transition t1 ()
requires { 1 <= F}
 { A := A + 1; F := F - 1; } 

transition t2 ()
requires { A = 1 && 1 <= G }
 { A := A - 1; B := B + 1; G := G - 1; }

transition t3 ()
requires { 1 <= B}
 { B := B - 1; C := C + 1; F := F + 1; }

transition t4 ()
requires { 1 <= C && 1 <= F } 
 { C := C - 1; D := D + 1; F := F - 1; }

transition t5 ()
requires { 1 <= D }
 { D := D - 1; E := E + 1; G := G + 1; }

transition t6 ()
requires { 1 <= E }
 { E := E - 1; F := F + 1; }

transition t7 ()
requires { 1 <= A && 1 <= G }
 { A := A - 1; C := C + 1; F := F + 1; G := G - 1; }

transition t8 ()
requires { 1 <= G && 1 <= F }
 { C := C + 1; G := G - 1; }

transition t9 ()
requires { 1 <= C && 1 <= E }
 { C := C - 1; D := D + 1; E := E - 1; }

transition t10 ()
requires { 1 <= C && 1 <= F }
 { C := C - 1; E := E + 1; F := F - 1; G := G + 1 ; }

transition t11 ()
requires { 1 <= C && 1 <= E }
 { C := C - 1; G := G + 1; }

transition t12 ()
requires { 1 <= F && 1 <= G }
 { E := E + 1; F := F - 1; }"
in
  let lb = from_string input_str in
  (* add_debug "Lexing OK"; *)
   
  try
   ignore( Dom_html.window##setTimeout (Js.wrap_callback ( fun _ -> 
    ignore( Dom_html.window##open_ (Js.string "trace.html", Js.string "Cubicle Trace View", Js.null))), 1000.));
    (* let w = Dom_html.window##open_ (Js.string "trace.html", Js.string "Cubicle Trace View", Js.null) in *)
    (* ignore( Dom_html.window##setTimeout (Js.wrap_callback ( fun _ ->  *)
    (*   Dom_html.window##focus()), 0.1)); *)
    let s = Parser.system Lexer.token lb in
    (* add_debug "Parsing OK"; *)
    let system = Typing.system s in
    (* add_debug "Typing OK"; *)
    if type_only then exit 0;

    if refine_universal then
      printf "@{<b>@{<fg_yellow>Warning@} !@}\nUniversal guards refinement \
              is an experimental feature. Use at your own risks.\n@.";
    let close_dot = Dot.open_dot () in
    begin
      match Brab.brab system with
      | Bwd.Safe (visited, candidates) -> ()
         (* if (not quiet || profiling) then *)
         (*   Stats.print_report ~safe:true visited candidates; *)
         (* printf "\n\nThe system is @{<b>@{<fg_green>SAFE@}@}\n@."; *)
         (* Trace.Selected.certificate system visited; *)
         (* close_dot (); *)

      | Bwd.Unsafe (faulty, candidates) ->
         if (not quiet || profiling) then
           Stats.print_report ~safe:false [] candidates;
         if not quiet then Stats.error_trace system faulty;
         printf "\n\n@{<b>@{<bg_red>UNSAFE@} !@}\n@.";
         close_dot ();
         exit 1
    end

  with
  | Lexer.Lexical_error s ->
     Util.report_loc err_formatter (lexeme_start_p lb, lexeme_end_p lb);
     eprintf "lexical error: %s@." s;
     exit 2

  | Parsing.Parse_error ->
     let loc = (lexeme_start_p lb, lexeme_end_p lb) in
     Util.report_loc err_formatter loc;
     eprintf "syntax error@.";
     exit 2

  | Typing.Error (e,loc) ->
     Util.report_loc err_formatter loc;
     eprintf "typing error: %a@." Typing.report e;
     exit 2

  | Stats.ReachedLimit ->
     if (not quiet || profiling) then Stats.print_report ~safe:false [] [];
     eprintf "\n@{<b>@{<fg_yellow>Reached Limit@} !@}\n";
     eprintf "It is likely that the search diverges, increase \
              the limit to explore further.@.";
     exit 1

  | Failure str ->
     eprintf "\n@{<u>Internal failure:@}%s@." str;
     exit 1
       
let get_storage () =
  match Js.Optdef.to_option Dom_html.window##localStorage with
    | None -> raise Not_found
    | Some t -> t
      
let _ =
  Dom_html.window##onload <- Dom_html.handler
    ( fun ev -> 

      let textareaE = Dom_html.getElementById "input" in 
      let textarea = 
        match Js.Opt.to_option (Dom_html.CoerceTo.textarea textareaE) with 
          |None -> failwith "textarea not found"
          |Some t -> t in 
      let input_str = Js.to_string textarea##value in 
      let buttonE = Dom_html.getElementById "run-cubicle" in 
      let button = 
        match Js.Opt.to_option (Dom_html.CoerceTo.button buttonE) with 
          |None -> failwith "textarea not found"
          |Some b -> b in 
      button##onclick <- Dom.handler (fun _ -> main (); Js._false);
      (* Firebug.console##log (Js.string "done"); *)
      (* main (); *)
       Js._false);
 (* let rec loop _ =  *)
 (*   if not !loaded then  *)
 (*   ignore( Dom_html.window##setTimeout ((Js.wrap_callback loop), 0.)) in  *)
 (* loop (); *)

  (* let l = get_storage () in  *)
  (* for i = 1 to l##length do  *)
  (*   let key = Js.string (string_of_int i) in  *)
  (*   let s = l##getItem (key) in  *)
  (*   l##removeItem (key); *)
  (*   let str = Js.Opt.to_option s in *)
  (*   match str with  *)
  (*   |None -> raise Not_found *)
  (*   |Some s -> Firebug.console##log (s) *)
  (* done *)
