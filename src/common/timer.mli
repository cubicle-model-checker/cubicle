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

(** Imperative timers for profiling *)

(** The interface of timers *)
module type S = sig

  (** Start (or restart) recording {e user time} when this function is
      called. *)
  val start : unit -> unit

  (** Pause the time, i.e. accumulates time elapsed since last (re-)start *)
  val pause : unit -> unit

  (** Returns the time in seconds accumulated in the timer. *)
  val get : unit -> float    
end

(** Functor to create a new timer. If [profiling] is false in the parameter
    module, the timer will be inactive. *)
module Make (X : sig val profiling : bool end) : S
