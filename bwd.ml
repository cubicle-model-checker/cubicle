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


type result = Safe of Node.t list | Unsafe of Node.t * Node.t list

exception ReachedLimit


module type Strategy = sig
  
  val search : ?invariants:Node.t list -> ?candidates:Node.t list ->
               t_system -> result

end


module Make ( Q : PriorityNodeQueue ) : Strategy = struct

  module Fixpoint = Fixpoint.FixpointTrie
  module Approx = Approx.Selected

  let search ?(invariants=[]) ?(candidates=[]) system =
    
    let visited = ref Cubetrie.empty in
    let candidates = ref candidates in
    let q = Q.create () in
    let postponed = ref [] in

    (* Initialization *)
    Q.push_list !candidates q;
    Q.push_list system.t_unsafe q;
    List.iter (fun inv -> visited := Cubetrie.add_node inv !visited)
              (invariants @ system.t_invs);

    try
      let cpt = ref 0 in
      while not (Q.is_empty q) do
        let n = Q.pop q in
        Safety.check system n;
        begin
          incr cpt;
          match Fixpoint.check n !visited with
          | Some db ->
             Stats.fixpoint n db
          | None ->
             Stats.new_node n;
             let n = begin
                 match Approx.good n with
                 | None -> n
                 | Some c ->
                    candidates := c :: !candidates;
                    Stats.candidate c;
                    c
               end
             in
             let ls, post = Pre.pre_image system.t_trans n in
             if delete then visited := Cubetrie.delete_subsumed n !visited;
	     postponed := List.rev_append post !postponed;
             visited := Cubetrie.add_node n !visited;
             Q.push_list ls q;
             Stats.remaining (Q.length q);
        end;
        
        if Q.is_empty q then
          begin
            Q.push_list !postponed q;
            postponed := []
          end
      done;
      Safe (Cubetrie.all_vals !visited)
    with Safety.Unsafe faulty ->
      Unsafe (faulty, !candidates)

end



module BreadthOrder = struct

  type t = Node.t

  let compare s1 s2 =
    let c = Pervasives.compare s2.kind s1.kind in
    if c <> 0 then c else
      
    let v1 = Node.size s1 in
    let v2 = Node.size s2 in
    let c = Pervasives.compare v1 v2 in
    if c <> 0 then c else
      let c1 = Node.card s1 in
      let c2 = Node.card s2 in
      let c = Pervasives.compare c1 c2 in
      if c <> 0 then c else
        Pervasives.compare s1.depth s2.depth
end


module DepthOrder = struct

  type t = Node.t

  let compare s1 s2 =
    let v1 = Node.size s1 in
    let v2 = Node.size s2 in
    let c = Pervasives.compare v1 v2 in
    if c <> 0 then c else
      let c1 = Node.card s1 in
      let c2 = Node.card s2 in
      let c = Pervasives.compare c1 c2 in
      if c <> 0 then c else
        Pervasives.compare s2.depth s1.depth
end

module NodeHeap (X : Set.OrderedType with type t = Node.t) : PriorityNodeQueue = struct

  module H = Heap.Make(X)

  type t = H.t ref

  let create () = ref H.empty

  let pop h =
    let e, nh = H.pop !h in
    h := nh;
    e

  let push_list l h = h:= H.add !h l

  let push e h = push_list [e] h

  let clear h = h := H.empty

  let length h = H.length !h
                          
  let is_empty h = !h = H.empty

end


module type StdQ = sig
    type 'a t

    val create : unit -> 'a t
    val pop : 'a t -> 'a
    val push : 'a -> 'a t -> unit
    val clear : 'a t -> unit
    val length : 'a t -> int
    val is_empty : 'a t -> bool
end

module NodeQ (Q : StdQ) : PriorityNodeQueue = struct

  type t = Node.t Q.t

  let create = Q.create
  let pop = Q.pop
  let push = Q.push
  let clear = Q.clear
  let length = Q.length
  let is_empty = Q.is_empty
  let push_list l q = List.iter (fun e -> push e q) l

end

module BFS : Strategy = Make (NodeQ (Queue))
module DFS : Strategy = Make (NodeQ (Stack))
module BFSH : Strategy = Make (NodeHeap (BreadthOrder))
module DFSH : Strategy = Make (NodeHeap (DepthOrder))


let select_search =
  match mode with
  | Bfs -> (module BFS : Strategy)
  | Dfs -> (module DFS)
  | BfsH -> (module BFSH)
  | DfsH -> (module DFSH)
  | _ -> failwith "This strategy is not yet implemented."

module Selected : Strategy = (val (select_search)) 
