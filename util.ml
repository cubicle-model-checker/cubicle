(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2013                          *)
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
module TimeCustom = Timer.Make (Options)


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
