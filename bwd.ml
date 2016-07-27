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
    ?forward:bool -> t_system -> result

end

let longest xs ys = if List.length xs > List.length ys then xs else ys

let lcs xs' ys' =
  let xs = Array.of_list xs'
  and ys = Array.of_list ys' in
  let n = Array.length xs
  and m = Array.length ys in
  let a = Array.make_matrix (n+1) (m+1) [] in
  for i = n-1 downto 0 do
    for j = m-1 downto 0 do
      a.(i).(j) <- 
        let (t1, _), (t2, _) = xs.(i), ys.(j) in
        if Hstring.equal t1 t2 then
          t1 :: a.(i+1).(j+1)
        else
          longest a.(i).(j+1) a.(i+1).(j)
    done
  done;
  a.(0).(0)

let update_heur n = 
  (* if n.heuristic = -1 then *)
    let h = List.map (fun (ti, vl, _) -> ti.tr_name, vl) n.from in
    let histories = Enumerative.get_histories () in
    let heur = 
      if List.exists (List.exists (Enumerative.is_sublist h))
        histories then 100
      else 
        let lth, sub, hist = 
          List.fold_left (
            List.fold_left (
              fun ((lth, sub, hist) as acc) hist' -> 
                let sub' = lcs h hist' in
                let lth' = List.length sub' in
                if lth' > lth then (lth', sub', hist') else acc
            ))
            (0, [], []) histories in
        lth * 100 / (List.length h)
    in
    n.heuristic <- heur

module Make ( Q : PriorityNodeQueue ) : Strategy = struct

  module Fixpoint = Fixpoint.FixpointTrie
  module Approx = Approx.Selected

  let nb_remaining q post () = Q.length q, List.length !post

  let search ?(invariants=[]) ?(candidates=[]) ?(forward=false) system =
    
    let visited = ref Cubetrie.empty in
    let candidates = ref candidates in
    let q = Q.create () in
    let postponed = ref [] in

    (* Initialization *)
    Q.push_list !candidates q;
    Q.push_list system.t_unsafe q;
    List.iter (fun u -> 
      try Safety.check system u 
      with Safety.Unsafe _ -> 
        Format.eprintf "THIS UNSAFE WAS SEEN BY FORWARD@.%a@." Node.print u;
        
        exit 1
    ) system.t_unsafe;
    List.iter (fun inv -> visited := Cubetrie.add_node inv !visited)
      (invariants @ system.t_invs);

    try
      while not (Q.is_empty q) do
        let n = Q.pop q in
        Safety.check system n;
        begin
          if debug_smt && verbose > 2 then Format.eprintf "[Fix] check %a @." Node.print n;

          match Fixpoint.check n !visited with
          | Some db ->
            if debug_smt then Format.eprintf "[Fix] fixpoint@.";
            Stats.fixpoint n db
          | None ->
            if debug_smt then Format.eprintf "[Fix] no fixpoint@.";
            Stats.check_limit n;
            let n = if not forward then begin
              Stats.new_node n;
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
              else n
            in
            let ls, post = 
              if not forward || n.depth < bwd_fwd then
                Pre.pre_image system.t_trans n
              else [], [] in
            if delete then
              visited :=
                Cubetrie.delete_subsumed ~cpt:Stats.cpt_delete n !visited;
	    postponed := List.rev_append post !postponed;
            visited := Cubetrie.add_node n !visited;

            Q.push_list ls q;
            if not forward then Stats.remaining (nb_remaining q postponed);
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


   
  let search ?(invariants=[]) ?(candidates=[]) ?(forward=false) system =
    
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

module HistoryOrder = struct

  type t = Node.t
 
  let compare = Node.compare_by_history

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

  let push_list l h = 
    if approx_history then List.iter update_heur l;
    h:= H.add !h l

  let push e h = push_list [e] h

  let clear h = h := H.empty

  let length h = H.length !h
                          
  let is_empty h = !h = H.empty

end

module NodeHeur (X : Set.OrderedType with type t = Node.t) : PriorityNodeQueue =
struct

  module H = Heap.Make(X)
   
  type t = H.t ref

  let create () = ref H.empty

  let pop h =
    let e, nh = H.pop !h in
    h := nh;
    e

  let push_list l h = 
    List.iter update_heur l;
    h:= H.add !h l

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
  let push e q = 
    if approx_history then update_heur e;
    Q.push e q
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
    if approx_history then update_heur n;
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

module BFSHH : Strategy = Maker (NodeHeur (HistoryOrder))

module BFSA : Strategy = Maker (ApproxQ (NodeQ (Queue)))
module DFSA : Strategy = Maker (ApproxQ (NodeQ (Stack)))

let select_search =
  match mode with
  | "bfs" -> (module BFS : Strategy)
  | "dfs" -> (module DFS)
  | "bfsh" -> (module BFSH)
  | "bfshh" -> (module BFSHH)
  | "dfsh" -> (module DFSH)
  | "bfsa" -> (module BFSA)
  | "dfsa" -> (module DFSA)
  | _ -> failwith ("The strategy "^mode^" is not implemented.")

module Selected : Strategy = (val (select_search)) 
