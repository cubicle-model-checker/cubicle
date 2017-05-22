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

(** Utilitaries *)

(** {2 Timers } *)

module TimerSubset : Timer.S
module TimerApply  : Timer.S
module TimeFix : Timer.S
module TimeEasyFix : Timer.S
module TimeHardFix : Timer.S
module TimeRP : Timer.S
module TimePre : Timer.S
module TimeSort : Timer.S
module TimeForward : Timer.S
module TimeCheckCand : Timer.S
module TimeFormula : Timer.S
module TimeSimpl : Timer.S
module TimeCertificate : Timer.S
module TimeSafety : Timer.S
module TimeGhb : Timer.S
module TimePESubst : Timer.S
module TimeCSubst : Timer.S
module TimeASubst : Timer.S
module TimeSatRead : Timer.S
module TimeBuildRW : Timer.S
module TimeFilterRW : Timer.S


(** {2 Misc } *)

val nb_digits : int -> int
(** Returns the number of digits of a positive integer *)

val set_liberal_gc : unit -> unit
(** Changes garbage collector parameters limit its effect *)

val reset_gc_params : unit -> unit
(** Reset the parameters of the GC to its default values. Call after
    {!set_liberal_gc}. *)

val syscall : string -> string
(** Captures the output of a unix command *)

val syscall_full : string -> string * string * Unix.process_status
(** Captures the standard and error output of a unix command with its exit
    status *)

val remove_trailing_whitespaces_end : string -> string



type color =
    { c_red : float;
      c_green : float;
      c_blue : float; }

val red : color
val green : color
val blue : color
val black : color
val white : color
val magenta : color

val hex_color : color -> string

val chromatic : color -> color -> int -> unit -> color 


type loc = Lexing.position * Lexing.position
(** Location in file *)

val report_loc : Format.formatter -> loc -> unit
(** Report location on formatter *)
