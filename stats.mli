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

module Make (Options : sig
                         val profiling : bool
                         val verbose : int
                         val quiet : bool
                       end) : sig

  val new_node : Node.t -> unit

  val fixpoint : Node.t -> int list option -> unit

  val restart : unit -> unit

  val remaining : int -> unit

  val candidate : Node.t -> unit

end
