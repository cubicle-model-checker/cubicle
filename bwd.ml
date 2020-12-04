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
    assert (List.length invariants = 0);
    assert (List.length !candidates = 0);
    List.iter (fun inv -> visited := Cubetrie.add_node inv !visited)
      (invariants @ system.t_invs);
    let cpt_pre = ref 0 in 
    try
      while not (Q.is_empty q) do
        let n = Q.pop q in
	(*Format.eprintf "n: %d@." n.tag;*)
        Safety.check system n;
        begin
          match Fixpoint.check n !visited with
          | Some db ->
            Stats.fixpoint n db
	    (*Format.eprintf "Begin cubetrie@.";
	    List.iter (fun x -> Format.eprintf "db: %d@." x) db;
	    Cubetrie.iter (fun x -> Format.eprintf "cubetrie: %a@." Node.print x) !visited;
	    Format.eprintf "Fixpoint %a - done@." Node.print n;
	    Format.eprintf "End cubetrie@.";*)

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
	     (*let ls = List.filter (fun n ->  Fixpoint.check n Cubetrie.empty = None) ls in
	     let post = List.filter (fun n ->  Fixpoint.check n Cubetrie.empty = None) post in*)
	     cpt_pre := !cpt_pre + (List.length ls) + (List.length post);
	     (*Format.eprintf "Begin: %d %d @." (List.length ls) (List.length post);
	     List.iter (fun x -> Format.eprintf "%a@." Node.print x) ls;
	     Format.eprintf "End@.";*)
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
      Format.eprintf "Pre counter %d@." !cpt_pre; 
      Safe (Cubetrie.all_vals !visited, !candidates)
    with Safety.Unsafe faulty ->
      if dot then Dot.error_trace faulty;
      Unsafe (faulty, !candidates)

end



module MakeParall ( Q : PriorityNodeQueue ) : Strategy = struct

  module Fixpoint = Fixpoint.FixpointTrie
  module Approx = Approx.Selected

  let nb_remaining q post () = Q.length q, List.length !post

  type task = Task_node of Node.t * Node.t Cubetrie.t

  type worker_return =
    | WR_Fixpoint of int list
    | WR_PreNormal of (Node.t list * Node.t list)
    | WR_PreCandidate of (Node.t * (Node.t list * Node.t list))
    | WR_Unsafe of Node.t
    | WR_ReachLimit
    | WR_NoFixpoint
  
  let () =
    (* Functory.Control.set_debug true; *)
    Functory.Cores.set_number_of_cores cores

  let do_sync_barrier = true

  let gentasks nodes visited =
    let tasks, _ = 
      List.fold_left
        (fun (tasks, visited) n ->
         (Task_node (n, visited), ()) :: tasks,
         Cubetrie.add_node n visited
        ) ([], visited) nodes
    in
    List.rev tasks

  let gentasks_hard system nodes visited =
    let tasks, _ = 
      List.fold_left
        (fun (tasks, visited) n ->
         Safety.check system n;
         if Fixpoint.peasy_fixpoint n visited <> None then tasks, visited
         else
           (Task_node (n, visited), ()) :: tasks,
         Cubetrie.add_node n visited
        ) ([], visited) nodes
    in
    (* List.rev *) tasks

  let worker system = function
    | Task_node (n, visited) ->
       try
         Safety.check system n;
         match Fixpoint.check n visited with
         | Some db -> WR_Fixpoint db
         | None ->
            Stats.check_limit n;
            match Approx.good n with
            | None ->
               WR_PreNormal (Pre.pre_image system.t_trans n)
            | Some c ->
               try
                 (* Replace node with its approximation *)
                 Safety.check system c;
                 WR_PreCandidate (c, (Pre.pre_image system.t_trans n))
               with Safety.Unsafe _ ->
                 WR_PreNormal (Pre.pre_image system.t_trans n)
       with
       | Safety.Unsafe faulty  ->
          WR_Unsafe faulty
       | Stats.ReachedLimit ->
          WR_ReachLimit

  let print_smt_error = function
    | Smt.DuplicateTypeName h ->
       eprintf "Duplicate type name %a@." Hstring.print h
    | Smt.DuplicateSymb h ->
      eprintf "Duplicate symbol %a@." Hstring.print h
    | Smt.DuplicateLabel h ->
      eprintf "Duplicate record field name %a@." Hstring.print h
    | Smt.UnknownType h ->
       eprintf "Unknown type %a@." Hstring.print h
    | Smt.UnknownSymb h ->
       eprintf "Unknown symbol %a@." Hstring.print h


  let worker_fix system = function
    | Task_node (n, visited) ->
       try
         match Fixpoint.hard_fixpoint n visited with
         | Some db -> WR_Fixpoint db
         | None -> WR_NoFixpoint
       with
       | Safety.Unsafe faulty  ->
          WR_Unsafe faulty
       | Stats.ReachedLimit ->
          WR_ReachLimit
       | Smt.Error e -> print_smt_error e; assert false


  let populate_pre q postponed visited n ls post =
    if delete then
      visited :=
        Cubetrie.delete_subsumed ~cpt:Stats.cpt_delete n !visited;
    postponed := List.rev_append post !postponed;
    visited := Cubetrie.add_node n !visited;
    Q.push_list ls q;
    Stats.remaining (nb_remaining q postponed)

  let empty_queue q =
    let rec qux acc =
      if Q.is_empty q then List.rev acc 
      else qux (Q.pop q :: acc)
    in
    qux []

  let master_fetch system q postponed visited candidates task res =
    begin
      match res, task with
      | WR_Unsafe faulty, _ ->
         raise (Safety.Unsafe faulty)
      | WR_ReachLimit, _ -> raise Stats.ReachedLimit
      | WR_Fixpoint db, (Task_node (n, _), ()) ->
         if not quiet && debug then eprintf "\nRECIEVED FIX\n@."; 
         Stats.fixpoint n db
      | WR_PreNormal (ls, post), (Task_node (n, _), ()) ->
         Stats.new_node n;
         populate_pre q postponed visited n ls post
      | WR_PreCandidate (c, (ls, post)), (Task_node (n, _), ()) ->
         Stats.new_node n;
         candidates := c :: !candidates;
         Stats.candidate n c;
         populate_pre q postponed visited c ls post
      | WR_NoFixpoint, (Task_node (n, _), ()) ->
         begin
         if not quiet && debug then eprintf "\nRECIEVED NO_FIX\n@."; 
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
         end
         
    end;
    if do_sync_barrier then []
    else gentasks_hard system (empty_queue q) !visited


   
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
        (* let compute = if Q.length q > 5000 then *)
        (*     Functory.Cores.compute *)
        (*   else Functory.Sequential.compute *)
        (* in *)
        let tasks = gentasks_hard system (empty_queue q) !visited in
        Functory.Cores.compute
          ~worker:(worker_fix system)
          ~master:(master_fetch system q postponed visited candidates)
          tasks;
        
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




module BreadthOrder = struct

  type t = Node.t
 
  let compare = Node.compare_by_breadth

end


module DepthOrder = struct

  type t = Node.t
 
  let compare = Node.compare_by_depth

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

module type Maker = functor (Q : PriorityNodeQueue) -> Strategy

let make_functor =
  if cores > 1 then 
    (module MakeParall : Maker)
  else
    (module Make)

module Maker = (val make_functor)

module BFS : Strategy = Maker (NodeQ (Queue))
module DFS : Strategy = Maker (NodeQ (Stack))

module BFSH : Strategy = Maker (NodeHeap (BreadthOrder))
module DFSH : Strategy = Maker (NodeHeap (DepthOrder))

module BFSA : Strategy = Maker (ApproxQ (NodeQ (Queue)))
module DFSA : Strategy = Maker (ApproxQ (NodeQ (Stack)))

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
