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

open Options
open Format
open Ast


module type PriorityNodeQueue = sig

    type t

    val create : unit -> t
    val pop : t -> Node.t
    val push : Node.t -> t -> unit
    val push_list : Node.t list -> t -> unit
    val clear : t -> unit
    val length : t -> int
    val is_empty : t -> bool
end


type result =
  | Safe of Node.t list * Node.t list
  (** The system is safe and we return the set of visited nodes and the
      inferred invariants *)
  | Unsafe of Node.t * Node.t list
  (** The system is unsafe and we return the faulty node and the full list of
      candidate invariants that were considered *)


exception ReachedLimit


(** {2 Strategies } *)

module type Strategy = sig
  
  val search : ?invariants:Node.t list -> ?candidates:Node.t list ->
               t_system -> result

end


module Make ( Q : PriorityNodeQueue ) : Strategy
(** Functor for creating a strategy given a priority queue  *)


(** {3 Predefined Strategies } *)

module BFS : Strategy
module DFS : Strategy
module BFSH : Strategy
module DFSH : Strategy

module Selected : Strategy
(** Strategy selected by the options of the command line *)
