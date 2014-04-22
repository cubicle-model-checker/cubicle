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


(** Dummy replacement for Functory library
  
    This module is renamed to [Functory] if the library Functory was not
    found by configure. This provides a way to compile cubicle even if 
    Functory is missing.
 *)

module Cores : sig

  val set_number_of_cores : int -> unit
  val compute : 
    worker:('a -> 'b) -> 
    master:('a * 'c -> 'b -> ('a * 'c) list) -> ('a * 'c) list -> unit

end
