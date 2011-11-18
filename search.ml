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

open Options
open Format

exception ReachBound

module AE = AltErgo

module TimeFix = Timer.Make (struct end)

module TimeRP = Timer.Make (struct end)

module TimePre = Timer.Make (struct end)

module Profiling = struct
  
  let round = 
    if not profiling then fun _ -> () 
    else fun cpt -> eprintf "@.-- Round %d@." cpt

  let cpt_fix = ref 0

  let cpt_process = ref 0

  let update_nb_proc s =
    cpt_process := max !cpt_process s
    
  let print_visited = 
    if not profiling then fun _ -> ()
    else fun nb -> eprintf "Number of visited nodes : %d@." nb

  let print_states st pr = 
    if not profiling then ()
    else List.iter
      (eprintf "%a@." pr) st

  let print = 
    if not profiling then fun _ _ _ -> ()
    else fun str d size -> 
      eprintf "[%s %d] Number of processes : %d@." str d size

  let print_time_fix () =
    let sec = TimeFix.get () in
    let minu = floor (sec /. 60.) in
    let extrasec = sec -. (minu *. 60.) in
    eprintf "Time for fixpoint                : %dm%2.3fs@."
      (int_of_float minu) extrasec

  let print_time_rp () =
    let sec = TimeRP.get () in
    let minu = floor (sec /. 60.) in
    let extrasec = sec -. (minu *. 60.) in
    eprintf "├─Time for relevant permutations : %dm%2.3fs@."
      (int_of_float minu) extrasec

  let print_time_prover () =
    let sec = Prover.TimeAE.get () in
    let minu = floor (sec /. 60.) in
    let extrasec = sec -. (minu *. 60.) in
    eprintf "└─Time in solver                 : %dm%2.3fs@."
      (int_of_float minu) extrasec
      
  let print_time_pre () =
    let sec = TimePre.get () in
    let minu = floor (sec /. 60.) in
    let extrasec = sec -. (minu *. 60.) in
    eprintf "Time for pre-image computation   : %dm%2.3fs@."
      (int_of_float minu) extrasec

  let print_time_hs () =
    let sec = Hstring.TimeHS.get () in
    let minu = floor (sec /. 60.) in
    let extrasec = sec -. (minu *. 60.) in
    eprintf "Hstring.make                     : %dm%2.3fs@."
      (int_of_float minu) extrasec

  let print_report nb =
    eprintf "\n----------------------------------------------@.";
    eprintf "Number of visited nodes          : %d@." nb;
    eprintf "Fixpoints                        : %d@." !cpt_fix;
    eprintf "Number of solver calls           : %d@." (Prover.nb_calls ());
    eprintf "Max Number of processes          : %d@." !cpt_process;
    eprintf "----------------------------------------------@.";
    print_time_fix ();
    print_time_rp ();
    print_time_prover ();
    eprintf "----------------------------------------------@."

end


module type I = sig
  type t

  val size : t -> int
  val maxrounds : int
  val maxnodes : int
  val invariants : t -> t list
  val gen_inv : 
    (invariants : t list -> visited : t list -> t -> unit) ->
    invariants : t list -> t list -> t -> t list * t list

  val delete_nodes : t -> t list -> t list

  val safety : t -> unit
  val fixpoint : invariants : t list -> visited : t list -> t -> bool
  val pre : t -> t list * t list  
  val print : formatter -> t -> unit
  val sort : t list -> t list
end

module type S = sig 
  type t
  val search : invariants : t list -> visited : t list -> t -> unit
end


module DFS ( X : I ) = struct

  type t = X.t

  let search ~invariants ~visited s =
    let nb_nodes = ref 0 in
    let rec search_rec cpt visited s =
      if cpt = X.maxrounds || !nb_nodes > X.maxnodes then
	raise ReachBound;
      incr nb_nodes;
      Profiling.print "DFS" !nb_nodes (X.size s);
      X.safety s;
      if not (X.fixpoint ~invariants:invariants ~visited:visited s) then
	let ls, post = X.pre s in
	List.iter (search_rec (cpt+1) (s::visited)) (ls@post)
    in
    search_rec 0 [] s

end

module DFSL ( X : I ) = struct

  type t = X.t
  
  let search ~invariants ~visited s =
    let visited = ref visited in
    let nb_nodes = ref 0 in
    let rec search_rec cpt s =
      if cpt = X.maxrounds || !nb_nodes > X.maxnodes then
	raise ReachBound;
      incr nb_nodes;
      Profiling.print "DFSL" !nb_nodes (X.size s);
      X.safety s;
      if not (X.fixpoint ~invariants:invariants ~visited:!visited s) then
	begin
	  let ls, post = X.pre s in
	  visited := s :: !visited;
	  List.iter (search_rec (cpt+1)) (ls@post)
	end
    in
    search_rec 0 s;
    eprintf "[DFSL]";
    Profiling.print_report !nb_nodes

end



module DFSH ( X : I ) = struct
  
  type t = X.t

  module S = struct
    type g = t
    type t = int * g * g list

    let compare (l1, s1, _) (l2, s2, _) =
      let v1 = X.size s1 in
      let v2 = X.size s2 in
      if v1 <= 2 && v2 <= 2 then
	let c = Pervasives.compare l2 l1 in
	if c<>0 then c else Pervasives.compare v1 v2
      else
	let c = Pervasives.compare v1 v2 in
	if c <> 0 then c else Pervasives.compare l2 l1
  end

  module H = Heap.Make(S)

  let search ~invariants ~visited s =
    let nb_nodes = ref 0 in
    let rec search_rec h =
      let (cpt, s, visited), h = H.pop h in
      incr nb_nodes;
      Profiling.print "DFSH" !nb_nodes (X.size s);
      if cpt = X.maxrounds || !nb_nodes > X.maxnodes then
	raise ReachBound;
      X.safety s;
      let  h =
	if X.fixpoint ~invariants:invariants ~visited:visited s
	then h 
	else
	  let ls, post = X.pre s in
	  let l = List.map (fun s' -> cpt+1, s', s::visited) (ls@post) in
	  (H.add h l)
      in
      search_rec h
    in
    begin
      try search_rec (H.add H.empty [0, s, visited])
      with Heap.EmptyHeap -> ()
    end;
    Profiling.print_report !nb_nodes

end


module BFS_base ( X : I ) = struct

  type t = X.t 

  let search inv_search invgen ~invariants ~visited s = 
    let nb_nodes = ref 0 in
    let visited = ref visited in
    let postponed = ref [] in
    let invariants = ref invariants in
    let not_invariants = ref [] in
    let q = Queue.create () in
    let rec search_rec_aux () =
      let cpt, s = Queue.take q in
      if cpt = X.maxrounds || !nb_nodes > X.maxnodes then
	raise ReachBound;
      X.safety s;
      if not (X.fixpoint ~invariants:!invariants ~visited:!visited s) 
      then
	begin
	  incr nb_nodes;
	  Profiling.print "BFS" !nb_nodes (X.size s);
	  eprintf " node %d= %a@." !nb_nodes 
	    (if debug then fun _ _ -> () else X.print) s;
	  let ls, post = X.pre s in
	  let ls = List.rev ls in
	  let post = List.rev post in
	  (* Uncomment for pure bfs search *)
	  (* let ls,post= List.rev_append ls post, [] in *)
	  Profiling.update_nb_proc (X.size s);

	  (* invariant search *)
	  let inv, not_invs =
	    if invgen && gen_inv && post <> [] then 
	      begin
		eprintf "On cherche un invariant@.";
		X.gen_inv inv_search ~invariants:!invariants 
		  !not_invariants s
	      end
	    else [], !not_invariants
	  in
	  invariants := List.rev_append inv !invariants;
	  not_invariants := not_invs;

	  visited := s :: !visited;
	  postponed := List.rev_append post !postponed;
	  List.iter (fun s -> Queue.add (cpt+1, s) q) ls
	end else incr Profiling.cpt_fix;
      search_rec_aux ()
    in
    let rec search_rec () =
      try search_rec_aux ()	    
      with Queue.Empty -> 
	if !postponed = [] then ()
	else 
	  begin
	    Profiling.print "Postpones" (List.length !postponed) 0;
	    (* postponed := X.sort !postponed; *)
	    List.iter (fun s -> Queue.add (0, s) q) !postponed;
	    postponed := [];
	    search_rec ()
	  end
    in
    Queue.add (0, s) q; search_rec ();
    Profiling.print_report !nb_nodes

end



module BFSnoINV ( X : I ) = struct

  include BFS_base(X)

  let search = search (fun ~invariants:_ ~visited:_ _ -> ()) false

end


module BFS ( X : I ) = struct

  include BFS_base(X)

  module Search = BFSnoINV (struct 
    include X let maxnodes = 100
  end)
    
  let search = search Search.search true

end



module DFSHL ( X : I ) = struct

  type t = X.t

  module S = struct
    type g = t
    type t = int * g

    let compare (l1, s1) (l2, s2) =
      let v1 = X.size s1 in
      let v2 = X.size s2 in
      if v1 <= 2 && v2 <= 2 then
    	let c = Pervasives.compare l2 l1 in
    	if c<>0 then c else Pervasives.compare v1 v2
      else
    	let c = Pervasives.compare v1 v2 in
    	if c <> 0 then c else Pervasives.compare l2 l1
      
  end

  module Search = BFSnoINV (struct include X let maxnodes = 100 end)

  module H = Heap.Make(S)

  let search ~invariants ~visited s =
    let nb_nodes = ref 0 in
    let visited = ref visited in
    let postponed = ref [] in
    let invariants = ref invariants in
    let not_invariants = ref [] in
    let rec search_rec_aux h =
	let (cpt, s), h = H.pop h in
	if cpt = X.maxrounds || !nb_nodes > X.maxnodes then
	  raise ReachBound;
	X.safety s;
	let h  =
	  if X.fixpoint ~invariants:!invariants 
	    ~visited:!visited (* (List.rev_append !visited !postponed) *) s
	  then (incr Profiling.cpt_fix; h)
	  else
	    begin
	      incr nb_nodes;
	      Profiling.print "DFSHL" !nb_nodes (X.size s);
	      eprintf " node %d= %a@." !nb_nodes 
		(if debug then fun _ _ -> () else X.print) s;
	      let ls, post = X.pre s in
	      let post = List.rev post in
	      let inv, not_invs =
		if gen_inv && post <> [] then
		  begin
		    eprintf "On cherche un invariant@.";
		    X.gen_inv Search.search ~invariants:!invariants
		      !not_invariants s
		  end
		else [], !not_invariants
	      in
	      invariants :=  List.rev_append inv !invariants;
	      not_invariants :=  not_invs;
	      Profiling.update_nb_proc (X.size s);
	      visited := s :: !visited;
	      postponed := List.rev_append post !postponed;
	      if inv = [] then
		let ls = List.rev (List.rev_map (fun s' -> cpt+1, s') ls) in
		(H.add h ls)
	      else
		h
	    end
	in
	search_rec_aux h
    in
    let rec search_rec h =
      try search_rec_aux h
      with Heap.EmptyHeap ->
	if !postponed = [] then ()
	else
	  begin
	    Profiling.print "Postpones" (List.length !postponed) 0;
	    let l = List.rev (List.rev_map (fun s -> 0, s) !postponed) in
	    postponed := [];
	    search_rec (H.add H.empty l)
	  end
    in
    let h = H.add H.empty [0, s] in
    search_rec h;
    Profiling.print_report !nb_nodes      

end

