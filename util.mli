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
module TimeFormula : Timer.S


val nb_digits : int -> int
(** Returns the number of digits of a positive integer *)

val set_liberal_gc : unit -> unit
(** Changes garbage collector parameters limit its effect *)

val reset_gc_params : unit -> unit
(** Reset the parameters of the GC to its default values. Call after
    {!set_liberal_gc}. *)

val syscall : string -> string
(** Captures the output and exit status of a unix command *)

val remove_trailing_whitespaces_end : string -> string
