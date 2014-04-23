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


type result = Safe of Node.t list * Node.t list | Unsafe of Node.t * Node.t list


module type Strategy = sig
  
  val search : ?invariants:Node.t list -> ?candidates:Node.t list ->
               t_system -> result

end


module Make ( Q : PriorityNodeQueue ) : Strategy = struct

  module Fixpoint = Fixpoint.FixpointTrie
  module Approx = Approx.Selected

  let nb_remaining q post () = Q.length q, List.length !post

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
      while not (Q.is_empty q) do
        let n = Q.pop q in
        Safety.check system n;
        begin
          match Fixpoint.check n !visited with
          | Some db ->
             Stats.fixpoint n db
          | None ->
             Stats.check_limit n;
             Stats.new_node n;
             let n = begin
                 match Approx.good n with
                 | None -> n
                 | Some c ->
                    try
                      (* Replace node with its approximation *)
                      Safety.check system c;
                      candidates := c :: !candidates;
                      Stats.candidate n c;
                      c
                    with Safety.Unsafe _ -> n 
                         (* If the candidate is directly reachable, no need to
                            backtrack, just forget it. *)
               end
             in
             let ls, post = Pre.pre_image system.t_trans n in
             if delete then
               visited := 
                 Cubetrie.delete_subsumed ~cpt:Stats.cpt_delete n !visited;
	     postponed := List.rev_append post !postponed;
             visited := Cubetrie.add_node n !visited;
             Q.push_list ls q;
             Stats.remaining (nb_remaining q postponed);
        end;
        
        if Q.is_empty q then
          (* When the queue is empty, pour back postponed nodes in it *)
          begin
            Q.push_list !postponed q;
            postponed := []
          end
      done;
      Safe (Cubetrie.all_vals !visited, !candidates)
    with Safety.Unsafe faulty ->
      if dot then Dot.error_trace faulty;
      Unsafe (faulty, !candidates)

end


             
let compare_kind s1 s2 =
  match s1.kind, s2.kind with
  | Approx, Approx -> 0
  | Approx, _ -> -1
  | _, Approx -> 1
  | k1, k2 -> Pervasives.compare k1 k2


module BreadthOrder = struct

  type t = Node.t
 
  let compare s1 s2 =
    let v1 = Node.dim s1 in
    let v2 = Node.dim s2 in
    let c = Pervasives.compare v1 v2 in
    if c <> 0 then c else
      let c1 = Node.size s1 in
      let c2 = Node.size s2 in
      let c = Pervasives.compare c1 c2 in
      if c <> 0 then c else
        let c =  compare_kind s1 s2 in
        if c <> 0 then c else
          let c = Pervasives.compare s1.depth s2.depth in 
          if c <> 0 then c else
            Pervasives.compare (abs s1.tag) (abs s2.tag)
end


module DepthOrder = struct

  type t = Node.t
 
  let compare s1 s2 =
    let v1 = Node.dim s1 in
    let v2 = Node.dim s2 in
    let c = Pervasives.compare v1 v2 in
    if c <> 0 then c else
      let c1 = Node.size s1 in
      let c2 = Node.size s2 in
      let c = Pervasives.compare c1 c2 in
      if c <> 0 then c else
        let c =  compare_kind s1 s2 in
        if c <> 0 then c else
          let c = Pervasives.compare s2.depth s1.depth in 
          if c <> 0 then c else
            Pervasives.compare (abs s1.tag) (abs s2.tag)
end


module NodeHeap (X : Set.OrderedType with type t = Node.t) : PriorityNodeQueue =
struct

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

  let create () = Q.create ()
  let pop q = Q.pop q
  let push e q = Q.push e q
  let clear q = Q.clear q
  let length q = Q.length q
  let is_empty q = Q.is_empty q
  let push_list l q = List.iter (fun e -> push e q) l

end


module ApproxQ (Q : PriorityNodeQueue) = struct
  
  type t = Q.t * Q.t

  let create () = Q.create (), Q.create ()

  let pop (aq, nq) = 
    if not (Q.is_empty aq) then Q.pop aq
    else Q.pop nq

  let push n (aq, nq) =
    match n.kind with
    | Approx -> Q.push n aq
    | _ -> Q.push n nq

  let clear (aq, nq) = Q.clear aq; Q.clear nq

  let length (aq, nq) = Q.length aq + Q.length nq

  let is_empty (aq, nq) = Q.is_empty aq && Q.is_empty nq

  let push_list l q = List.iter (fun e -> push e q) l

end


module BFS : Strategy = Make (NodeQ (Queue))
module DFS : Strategy = Make (NodeQ (Stack))

module BFSH : Strategy = Make (NodeHeap (BreadthOrder))
module DFSH : Strategy = Make (NodeHeap (DepthOrder))

module BFSA : Strategy = Make (ApproxQ (NodeQ (Queue)))
module DFSA : Strategy = Make (ApproxQ (NodeQ (Stack)))

let select_search =
  match mode with
  | "bfs" -> (module BFS : Strategy)
  | "dfs" -> (module DFS)
  | "bfsh" -> (module BFSH)
  | "dfsh" -> (module DFSH)
  | "bfsa" -> (module BFSA)
  | "dfsa" -> (module DFSA)
  | _ -> failwith ("The strategy "^mode^" is not implemented.")

module Selected : Strategy = (val (select_search)) 
