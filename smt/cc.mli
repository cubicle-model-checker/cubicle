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

val cc_active : bool ref

module type S = sig
  type t
  type r 

  module TimerCC : Timer.S

  val empty : unit -> t
  val assume : cs:bool -> 
    Literal.LT.t -> Explanation.t -> t -> t * Term.Set.t * int * (r * r) list
  val query : Literal.LT.t -> t -> Sig.answer
  val class_of : t -> Term.t -> Term.t list
  val extract_term : r -> Term.t option
  val print_r : Format.formatter -> r -> unit
end

module Make (X:Sig.X) : S
