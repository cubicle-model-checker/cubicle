(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                  Universite Paris-Sud 11                               *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

(* Backward reachability search strategies *)

exception Unsafe of Ast.t_system

module type I = sig
  type t = Ast.t_system

  type fsearch = 
    invariants : t list -> 
    visited : t list -> 
    forward_nodes : t list -> 
    candidates : t list ref ->
    t list -> unit

  val size : t -> int
  val card : t -> int
  val maxrounds : int
  val maxnodes : int
  val invariants : t -> t list
  val gen_inv : 
    fsearch -> invariants : t list -> t list -> t -> t list * t list
  val gen_inv_with_forward :
    fsearch -> invariants : t list -> forward_nodes : t list -> 
    t list -> t -> t list * t list
  val gen_inv_proc : 
    fsearch -> t list -> t list -> t -> t list * t list
  val init_thread : 
    fsearch ->
    t list ref -> t list ref -> t list ref -> t list ref -> 
    t Queue.t -> Thread.t

  val extract_candidates : t -> t list -> t list
  val is_inv : fsearch -> t -> t list -> bool

  val delete_nodes : t -> t list ref -> int ref -> bool -> unit
  val delete_nodes_trie : t -> t Cubetrie.t ref -> int ref -> bool -> unit
  val delete_nodes_inv : t list -> t list ref -> unit
  val delete_node : t -> unit
  val is_deleted : t -> bool

  val safety : t -> unit
    
  (* None = not a fixpoint ; Some l = fixpoint by l *)
  val fixpoint :
    invariants : t list -> visited : t list -> t -> (int list) option

  val easy_fixpoint : t -> t list -> (int list) option
  val hard_fixpoint : t -> t list -> (int list) option

  val fixpoint_trie : t -> Ast.Atom.t list -> t Cubetrie.t ref ->
    t Cubetrie.t ref -> t list ref -> (int list) option

  val fixpoint_trie2 : t Cubetrie.t -> t -> (int list) option

  val pre : t -> t list * t list
  val post : t -> t list

  val add_and_resolve : t -> t Cubetrie.t -> t Cubetrie.t

  val has_deleted_ancestor : t -> bool
  val print : Format.formatter -> t -> unit
  val print_bad : Format.formatter -> t -> unit
  val print_dead : Format.formatter -> (t * int list) -> unit
  val print_cand : Format.formatter -> (t * int list) -> unit
  val print_system : Format.formatter -> t -> unit
  val sort : t list -> t list
  val nb_father : t -> int

  val system : t -> Ast.t_system

  val subsuming_candidate : Ast.t_system -> Ast.t_system list

end


module type S = sig 
  type t

  val search : 
    invariants : t list -> 
    visited : t list -> 
    forward_nodes : t list -> 
    candidates : t list ref ->
    t list -> unit
end



module TimeFix : Timer.S
module TimeEasyFix : Timer.S
module TimeHardFix : Timer.S

module TimeRP  : Timer.S

module TimePre : Timer.S

module TimeSort : Timer.S

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

(* Prototype for Amit and Sava's algorithm *)
module Inductification ( X : I ) : S with type t = X.t


(* Bfs search with trie data structures *)

module BFS_trie  ( X : I ) : S  with type t = X.t 
