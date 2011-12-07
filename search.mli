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
exception Unsafe

module type I = sig
  type t

  val size : t -> int
  val maxrounds : int
  val maxnodes : int
  val invariants : t -> t list
  val gen_inv :
    (invariants : t list -> visited : t list -> t -> unit) -> 
    invariants : t list -> t list -> t -> t list * t list
  val gen_inv_proc : 
    (invariants : t list -> visited : t list -> t -> unit) ->
    t list -> t list -> t -> t list * t list
  val init_thread : 
    (invariants : t list -> visited : t list -> t -> unit) ->
    t list ref -> t list ref -> t list ref -> t list ref -> 
    t Queue.t -> Thread.t

  val extract_candidates : t -> t list -> t list
  val is_inv :
    (invariants : t list -> visited : t list -> t -> unit) ->
    t -> t list -> bool

  val delete_nodes : t -> t list ref -> int ref -> bool -> unit
  val delete_nodes_inv : t list -> t list ref -> unit
  val delete_node : t -> unit

  val safety : t -> unit
  val fixpoint : invariants : t list -> visited : t list -> t -> bool
  val easy_fixpoint : t -> t list -> bool
  val hard_fixpoint : t -> t list -> bool

  val pre : t -> t list * t list
  val has_deleted_ancestor : t -> bool
  val print : Format.formatter -> t -> unit
  val sort : t list -> t list
  val nb_father : t -> int

end

module TimeFix : Timer.S

module TimeRP  : Timer.S

module TimePre : Timer.S

module TimeSort : Timer.S


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


(* Concurrent Bfs search *)

module BFS_dist  ( X : I ) : S  with type t = X.t 

(* Bfs search with concurent invariant generation *)

module BFSinvp  ( X : I ) : S  with type t = X.t 
