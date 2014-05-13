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

(* Timers for profiling *)
module TimerSubset = Timer.Make (Options)
module TimerApply = Timer.Make (Options)
module TimeFix = Timer.Make (Options)
module TimeEasyFix = Timer.Make (Options)
module TimeHardFix = Timer.Make (Options)
module TimeRP = Timer.Make (Options)
module TimePre = Timer.Make (Options)
module TimeSort = Timer.Make (Options)
module TimeForward = Timer.Make (Options)
module TimeCheckCand = Timer.Make (Options)
module TimeFormula = Timer.Make (Options)
module TimeSimpl = Timer.Make (Options)


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
  let _ = Unix.close_process (ic, oc) in
  (Buffer.contents buf)

let rec remove_trailing_whitespaces_end str =
  if String.length str > 0 && 
    (str.[String.length str - 1] = '\n' 
    || str.[String.length str - 1] = ' '
      || str.[String.length str - 1] = '\t')  then
    remove_trailing_whitespaces_end (String.sub str 0 (String.length str - 1))
  else str
