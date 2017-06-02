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

open Format
open Lexing

(* Timers for profiling *)
module TotalTime = Timer.Make (Options)
module TimerICands = Timer.Make (Options)
module TimerSubset = Timer.Make (Options)
module TimerApply = Timer.Make (Options)
module TimeFix = Timer.Make (Options)
module TimeRP = Timer.Make (Options)
module TimePre = Timer.Make (Options)
module TimeSort = Timer.Make (Options)
module TimeForward = Timer.Make (Options)
module TimeCheckCand = Timer.Make (Options)
module TimeFormula = Timer.Make (Options)
module TimeSimpl = Timer.Make (Options)
module TimeCertificate = Timer.Make (struct let profiling = true end)
module TimeSubsuming = Timer.Make (Options)
module TimeFindBads = Timer.Make (Options)
module TimeCheckBad = Timer.Make (Options)
module TimeSelect = Timer.Make (Options)

let nb_digits n =
  if n < 10 then 1
  else if n < 100 then 2
  else if n < 1000 then 3
  else if n < 10000 then 4
  else if n < 100000 then 5
  else if n < 1000000 then 6
  else String.length (string_of_int n)

let reset_gc_params =
  let gc_c = Gc.get() in
  fun () -> Gc.set gc_c
  
let set_liberal_gc () =
  Gc.full_major ();
  let gc_c =
    { (Gc.get ()) with
      (* Gc.verbose = 0x3FF; *)
      Gc.minor_heap_size = 64000000; (* default 32000*)
      major_heap_increment = 3200000;    (* default 124000*)
      space_overhead = 100; (* default 80% des donnes vivantes *)
    }
  in
  Gc.set gc_c


(* Captures the output and exit status of a unix command : aux func *)
let syscall cmd =
  let ic, oc = Unix.open_process cmd in
  let buf = Buffer.create 16 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  ignore(Unix.close_process (ic, oc));
  Buffer.contents buf


let syscall_full cmd =
  let inc, outc, errc = Unix.open_process_full cmd (Unix.environment ()) in  
  let buf = Buffer.create 16 in
  let buferr = Buffer.create 16 in
  (try
     while true do
       Buffer.add_channel buf inc 1
     done
   with End_of_file -> ());
  (try
     while true do
       Buffer.add_channel buferr errc 1
     done
   with End_of_file -> ());
  let status = Unix.close_process_full (inc, outc, errc) in
  let s =  Buffer.contents buferr in
  let l = String.length s in
  let serr = if l > 0 then String.sub s 0 ((String.length s) - 1) else s in
  (Buffer.contents buf, serr, status)


let rec remove_trailing_whitespaces_end str =
  if String.length str > 0 && 
    (str.[String.length str - 1] = '\n' 
    || str.[String.length str - 1] = ' '
      || str.[String.length str - 1] = '\t')  then
    remove_trailing_whitespaces_end (String.sub str 0 (String.length str - 1))
  else str


type color =
    { c_red : float;
      c_green : float;
      c_blue : float; }

let hex_color c =
  Format.sprintf "#%02X%02X%02X"
                 (int_of_float c.c_red)
                 (int_of_float c.c_green)
                 (int_of_float c.c_blue)

let red = { c_red = 255.; c_green = 0.; c_blue = 0. }
let green = { c_red = 0.; c_green = 255.; c_blue = 0. }
            (* { c_red = 46.; c_green = 204.; c_blue = 113. } *)
            (* { c_red = 26.; c_green = 188.; c_blue = 156. } *)
let blue = { c_red = 0.; c_green = 0.; c_blue = 255. }
let black = { c_red = 0.; c_green = 0.; c_blue = 0. }
let white = { c_red = 255.; c_green = 255.; c_blue = 255. }
let magenta = { c_red = 255.; c_green = 0.; c_blue = 255. }
              (* { c_red = 231.; c_green = 76.; c_blue = 60. } *)

let incr_ccomp c inc_c =
  let r = c +. !inc_c in
  if r > 255. || r < 0. then c
  else r

let chromatic start stop steps =
  let now = ref start in
  let fstep = float_of_int steps in
  if fstep = 0. then fun () -> black
  else
    let inc_red = ref ((stop.c_red -. start.c_red) /. fstep) in
    let inc_green = ref ((stop.c_green -. start.c_green) /. fstep) in
    let inc_blue = ref ((stop.c_blue -. start.c_blue) /. fstep) in
    fun () ->
    now := {
      c_red = incr_ccomp !now.c_red inc_red;
      c_green = incr_ccomp !now.c_green inc_green;
      c_blue = incr_ccomp !now.c_blue inc_blue;
    };
    !now
    

type loc = Lexing.position * Lexing.position

let report_loc fmt (b,e) =
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  fprintf fmt "File \"%s\", line %d, characters %d-%d:" 
    Options.file l fc lc
