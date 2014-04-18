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


type result = Safe of Node.t list | Unsafe of Node.t

exception ReachedLimit


module Make ( Q : PriorityNodeQueue ) = struct

  module Fix = Fixpoint.FixpointTrie


  let search ?(invariants=[]) ?(candidates=[]) system =
    
    let visited = ref Cubetrie.empty in
    let candidates = ref candidates in
    let q = Q.create () in
    let postponed = ref [] in

    (* Initialization *)
    Q.add_list !candidates q;
    Q.add_list system.t_unsafe q;
    List.iter (fun inv -> visited := Cubetrie.add_node inv !visited)
              (invariants @ system.t_invs);

    try
      while not (Q.is_empty q) do
        let n = Q.pop q in
        Safety.check system n;
        begin
          match Fix.fixpoint n !visited with
          | Some db ->
             Stats.fixpoint n db
          | None db ->
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
             Q.add_list ls q;
             Stats.remaining ();
        end;
        
        if Q.is_empty then Q.add_list !postponed q
      done;
      Safe (Cubetrie.all_vals !visited)
    with Safety.Unsafe faulty ->
      Unsafe faulty

end



module BreadthOrder = struct

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
        Pervasives.compare s1.Node.depth s2.Node.depth
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
        Pervasives.compare s2.Node.depth s1.Node.depth s1
end

module NodeHeap (X : OrderedType) : PriorityNodeQueue = struct

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


module NodeQueue : PriorityNodeQueue = struct
  include Queue              
  type t = Node.t Queue.t

  let push_list l q = List.iter (fun e -> push e q) l
end


module NodeStack : PriorityNodeQueue = struct
  include Stack
  type t = Node.t Stack.t

  let push_list l s = List.iter (fun e -> push e s) l
end


module BFS = Make (NodeQueue)
module DFS = Make (NodeStack)
module BFSH = Make (NodeHeap (BreadthOrder))
module DFSH = Make (NodeHeap (DepthOrder))
