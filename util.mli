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

module TimerSubset : Timer.S
module TimerApply  : Timer.S
module TimeFix : Timer.S
module TimeEasyFix : Timer.S
module TimeHardFix : Timer.S
module TimeRP : Timer.S
module TimePre : Timer.S
module TimeSort : Timer.S
module TimeForward : Timer.S
module TimeCustom : Timer.S


val reset_gc_params : unit -> unit
val set_liberal_gc : unit -> unit
