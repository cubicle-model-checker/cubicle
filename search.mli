(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon, Universite Paris-Sud 11              *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

(* Backward reachability search strategies *)

exception ReachBound

module type I = sig
  type t

  val size : t -> int
  val maxrounds : int
  val maxnodes : int
  val invariants : t -> t list
  val gen_inv :
    (invariants : t list -> visited : t list -> t -> unit) -> 
    invariants : t list -> t list -> t -> t list * t list

  val delete_nodes : t -> t list ref -> unit

  val safety : t -> unit
  val fixpoint : invariants : t list -> visited : t list -> t -> bool
  val pre : t -> t list * t list
  val print : Format.formatter -> t -> unit
  val sort : t list -> t list

end

module TimeFix : Timer.S

module TimeRP  : Timer.S

module TimePre : Timer.S


module type S = sig 
  type t

  val search : invariants : t list -> visited : t list -> t -> unit

end

(* Dfs search where fixpoint nodes are only looked on the current
   branch *)

module DFS ( X : I ) : S with type t = X.t

(* Dfs search which extends the previous one with fixpoint nodes
   looked in the all tree on the left. *)

module DFSL ( X : I ) : S  with type t = X.t


(* Dfs search where nodes with less than 2 process variables are
   visited first: fixpoint nodes are just looked on the current
   branch *)

module DFSH ( X : I ) : S  with type t = X.t


(* Dfs search which extends the previous one with fixpoint nodes
   looked in the all tree on the left. *)

module DFSHL ( X : I ) : S  with type t = X.t


(* Bfs search where fixpoint nodes are the visited nodes. *)

module BFS  ( X : I ) : S  with type t = X.t 
