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

open Options
open Format
open Ast

exception Unsafe

module TimeFix = Timer.Make (struct end)

module TimeRP = Timer.Make (struct end)

module TimePre = Timer.Make (struct end)

module TimeSort = Timer.Make (struct end)

module Profiling = struct
  
  let round = 
    if not (profiling  && !verbose > 0) then fun _ -> () 
    else fun cpt -> eprintf "@.-- Round %d@." cpt

  let cpt_fix = ref 0

  let cpt_process = ref 0

  let update_nb_proc s =
    cpt_process := max !cpt_process s
    
  let print_visited = 
    if not (profiling && !verbose > 0) then fun _ -> ()
    else fun nb -> eprintf "Number of visited nodes : %d@." nb

  let print_states st pr = 
    if not profiling then ()
    else List.iter
      (eprintf "%a@." pr) st

  let print = 
    if not (profiling  && !verbose > 0) then fun _ _ _ -> ()
    else fun str d size -> 
      eprintf "[%s %d] Number of processes : %d@." str d size

  let print2 str d size =
      eprintf "[%s %d] Number of processes : %d@." str d size

  let print_time_fix () =
    let sec = TimeFix.get () in
    let minu = floor (sec /. 60.) in
    let extrasec = sec -. (minu *. 60.) in
    printf "Time for fixpoint                : %dm%2.3fs@."
      (int_of_float minu) extrasec

  let print_time_rp () =
    let sec = TimeRP.get () in
    let minu = floor (sec /. 60.) in
    let extrasec = sec -. (minu *. 60.) in
    printf "├─Time for relevant permutations : %dm%2.3fs@."
      (int_of_float minu) extrasec

  let print_time_prover () =
    let sec = Smt.get_time () in
    let minu = floor (sec /. 60.) in
    let extrasec = sec -. (minu *. 60.) in
    printf "└─Time in solver                 : %dm%2.3fs@."
      (int_of_float minu) extrasec
      
  let print_time_pre () =
    let sec = TimePre.get () in
    let minu = floor (sec /. 60.) in
    let extrasec = sec -. (minu *. 60.) in
    printf "Time for pre-image computation   : %dm%2.3fs@."
      (int_of_float minu) extrasec

  let print_time_hs () =
    let sec = Hstring.TimeHS.get () in
    let minu = floor (sec /. 60.) in
    let extrasec = sec -. (minu *. 60.) in
    printf "Hstring.find                     : %dm%2.3fs@."
      (int_of_float minu) extrasec

  let print_time_subset () =
    let sec = Ast.TimerSubset.get () in
    let minu = floor (sec /. 60.) in
    let extrasec = sec -. (minu *. 60.) in
    printf "├─Subset tests                   : %dm%2.3fs@."
      (int_of_float minu) extrasec

  let print_time_apply () =
    let sec = Ast.TimerApply.get () in
    let minu = floor (sec /. 60.) in
    let extrasec = sec -. (minu *. 60.) in
    printf "├─Apply substitutions            : %dm%2.3fs@."
      (int_of_float minu) extrasec

  let print_time_sort () =
    let sec = TimeSort.get () in
    let minu = floor (sec /. 60.) in
    let extrasec = sec -. (minu *. 60.) in
    printf "├─Nodes sorting                  : %dm%2.3fs@."
      (int_of_float minu) extrasec

  let print_report nb inv del =
    printf "\n----------------------------------------------@.";
    printf "Number of visited nodes          : %d@." nb;
    printf "Fixpoints                        : %d@." !cpt_fix;
    printf "Number of solver calls           : %d@." (Smt.get_calls ());
    printf "Max Number of processes          : %d@." !cpt_process;
    if delete then 
      printf "Number of deleted nodes          : %d@." del;
    if gen_inv then 
      printf "Number of invariants             : %d@." (List.length inv);  
    printf "----------------------------------------------@.";
    if profiling then begin
      print_time_pre ();
      print_time_fix ();
      print_time_rp ();
      print_time_subset ();
      print_time_apply ();
      print_time_sort ();
      print_time_prover ();
      printf "----------------------------------------------@."
    end

end


module type I = sig
  type t

  val size : t -> int
  val card : t -> int
  val maxrounds : int
  val maxnodes : int
  val invariants : t -> t list
  val gen_inv : 
    (invariants : t list -> visited : t list -> t list -> unit) ->
    invariants : t list -> t list -> t -> t list * t list
  val gen_inv_proc : 
    (invariants : t list -> visited : t list -> t list -> unit) ->
    t list -> t list -> t -> t list * t list
  val init_thread : 
    (invariants : t list -> visited : t list -> t list -> unit) ->
    t list ref -> t list ref -> t list ref -> t list ref -> 
    t Queue.t -> Thread.t

  val extract_candidates : t -> t list -> t list
  val is_inv :
    (invariants : t list -> visited : t list -> t list -> unit) ->
    t -> t list -> bool

  val delete_nodes : t -> t list ref -> int ref -> bool -> unit
  val delete_nodes_inv : t list -> t list ref -> unit
  val delete_node : t -> unit
  val is_deleted : t -> bool

  val safety : t -> unit
  val fixpoint : invariants : t list -> visited : t list -> t -> bool
  val easy_fixpoint : t -> t list -> bool
  val hard_fixpoint : t -> t list -> bool

  val pre : t -> t list * t list
  val has_deleted_ancestor : t -> bool
  val print : formatter -> t -> unit
  val sort : t list -> t list
  val nb_father : t -> int
end

module type S = sig 
  type t
  val search : invariants : t list -> visited : t list -> t list -> unit
end


module DFS ( X : I ) = struct

  type t = X.t

  let search ~invariants ~visited uns =
    let nb_nodes = ref 0 in
    let rec search_rec cpt visited s =
      if cpt = X.maxrounds || !nb_nodes > X.maxnodes then
	raise ReachBound;
      incr nb_nodes;
      if not quiet then Profiling.print "DFS" !nb_nodes (X.size s);
      X.safety s;
      if not (X.fixpoint ~invariants:invariants ~visited:visited s) then
	let ls, post = X.pre s in
	List.iter (search_rec (cpt+1) (s::visited)) (ls@post)
    in
    List.iter (search_rec 0 []) uns

end

module DFSL ( X : I ) = struct

  type t = X.t
  
  let search ~invariants ~visited uns =
    let visited = ref visited in
    let nb_nodes = ref (if dmcmt then -1 else 0) in
    let rec search_rec cpt s =
      if cpt = X.maxrounds || !nb_nodes > X.maxnodes then
	raise ReachBound;
      incr nb_nodes;
      if not quiet then Profiling.print "DFSL" !nb_nodes (X.size s);
      X.safety s;
      if not (X.fixpoint ~invariants:invariants ~visited:!visited s) then
	begin
	  let ls, post = X.pre s in
	  visited := s :: !visited;
	  List.iter (search_rec (cpt+1)) (ls@post)
	end
    in
    List.iter (search_rec 0) uns;
    eprintf "[DFSL]";
    Profiling.print_report !nb_nodes [] 0

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

  let search ~invariants ~visited uns =
    let nb_nodes = ref (if dmcmt then -1 else 0) in
    let rec search_rec h =
      let (cpt, s, visited), h = H.pop h in
      incr nb_nodes;
      if not quiet then Profiling.print "DFSH" !nb_nodes (X.size s);
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
      try
	search_rec (H.add H.empty (List.map (fun s -> 0, s, visited) uns))
      with Heap.EmptyHeap -> ()
    end;
    Profiling.print_report !nb_nodes [] 0

end

module BFS_base ( X : I ) = struct

  type t = X.t 

  let search inv_search invgen ~invariants ~visited uns = 
    let nb_nodes = ref (if dmcmt then -1 else 0) in
    let nb_deleted = ref 0 in
    let visited = ref visited in
    let postponed = ref [] in
    let invariants = ref invariants in
    let not_invariants = ref [] in
    let q = Queue.create () in
    let rec search_rec_aux () =
      let cpt, s = Queue.take q in
      if cpt = X.maxrounds || !nb_nodes > X.maxnodes then
	(Profiling.print_report !nb_nodes !invariants !nb_deleted;
	 raise ReachBound);
      X.safety s;
      if not (X.fixpoint ~invariants:!invariants ~visited:!visited s) 
      then
	begin
	  incr nb_nodes;
	  if not quiet then begin
	    Profiling.print "BFS" !nb_nodes (X.size s);
	    let prefpr = 
	      if (not invgen) && gen_inv then "     inv gen " else " " in
	    printf "%snode %d= @[%a@]@." prefpr !nb_nodes 
	      (if debug then fun _ _ -> () else X.print) s
	  end;
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
		X.gen_inv inv_search ~invariants:!invariants 
		  !not_invariants s
	      end
	    else [], !not_invariants
	  in
	  invariants := List.rev_append inv !invariants;
	  not_invariants := not_invs;
	  if delete then X.delete_nodes s visited nb_deleted false;
	  if delete && invgen && gen_inv then X.delete_nodes_inv inv visited;
	  visited := s :: !visited;
	  postponed := List.rev_append post !postponed;
	  if delete then X.delete_nodes s postponed nb_deleted true;
	  if delete && invgen && gen_inv then X.delete_nodes_inv inv postponed;

	  if inv = [] then List.iter (fun s -> Queue.add (cpt+1, s) q) ls
	end else incr Profiling.cpt_fix;
      search_rec_aux ()
    in
    let rec search_rec () =
      try search_rec_aux ()	    
      with Queue.Empty -> 
	if !postponed = [] then ()
	else 
	  begin
	    if not quiet then
	      Profiling.print "Postpones" (List.length !postponed) 0;
	    (* postponed := X.sort !postponed; *)
	    List.iter (fun s -> Queue.add (0, s) q) !postponed;
	    postponed := [];
	    search_rec ()
	  end
    in
    List.iter (fun s -> Queue.add (0, s) q) uns;
    search_rec ();
    if invgen || not gen_inv then 
      Profiling.print_report !nb_nodes !invariants !nb_deleted

end

module BFSinvp_base ( X : I ) = struct

  type t = X.t

  let () = Functory.Cores.set_number_of_cores cores

  let search inv_search ~invariants ~visited uns = 
    let nb_nodes = ref (if dmcmt then -1 else 0) in
    let nb_deleted = ref 0 in
    let visited = ref visited in
    let postponed = ref [] in
    let invariants = ref invariants in
    let not_invariants = ref [] in
    let q = Queue.create () in
    let candidates = Queue.create () in
    
    ignore( 
      X.init_thread inv_search invariants not_invariants 
	visited postponed candidates
    );
    
    let rec search_rec_aux () =
      let cpt, s = Queue.take q in
      if cpt = X.maxrounds || !nb_nodes > X.maxnodes then
	raise ReachBound;
      X.safety s;
      if not (X.fixpoint ~invariants:!invariants ~visited:!visited s) 
      then
	begin
	  incr nb_nodes;
	  if not quiet then Profiling.print "BFSinvp" !nb_nodes (X.size s);
	  if not quiet then printf " node %d= @[%a@]@." !nb_nodes 
	    (if debug then fun _ _ -> () else X.print) s;
	  let ls, post = X.pre s in
	  let ls = List.rev ls in
	  let post = List.rev post in
	  (* Uncomment for pure bfs search *)
	  (* let ls,post= List.rev_append ls post, [] in *)
	  Profiling.update_nb_proc (X.size s);

	  (* invariant search *)
	  if post <> [] then
	    (if debug then eprintf "Send candidate ...@.";
	     Queue.push s candidates
	    (* ignore (Event.poll (Event.send candidates_channel s)) *));
	  Thread.yield ();

	  if delete then X.delete_nodes s visited nb_deleted false;
	  visited := s :: !visited;
	  postponed := List.rev_append post !postponed;
	  if delete then X.delete_nodes s postponed nb_deleted true;

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
	    if not quiet then
	      Profiling.print "Postpones" (List.length !postponed) 0;
	    (* postponed := X.sort !postponed; *)
	    List.iter (fun s -> Queue.add (0, s) q) !postponed;
	    postponed := [];
	    search_rec ()
	  end
    in
    List.iter (fun s -> Queue.add (0, s) q) uns;
    search_rec ();
    Profiling.print_report !nb_nodes !invariants !nb_deleted;

end


module BFS_dist_base ( X : I ) = struct

  type t = X.t 

  type task = 
    | Fixcheck of t * int * t list
    | Geninv of t * t list * t list
    | Tryinv of t * t list

  type worker_return = 
    | Fix | NotFix | Unsafe_res | ReachBound_res
    | InvRes of t list * t list
    | Inv | NotInv
  
  let () = Functory.Cores.set_number_of_cores cores
      
  exception Killgeninv

  let gentasks snodes invariants visited =
    let _, tasks = 
      List.fold_left (fun (nodes, acc) (cpt, s) ->
	if cpt = X.maxrounds then raise ReachBound;
	if X.easy_fixpoint s nodes then nodes, acc
	else 
	  s::nodes,
	  (Fixcheck (s, cpt, nodes), ())::acc) 
	(List.rev_append invariants visited, []) snodes
    in 
    List.rev tasks

  let worker inv_search = function
    | Fixcheck (s, cpt, nodes) ->
      begin
	try
	  X.safety s;
	  if X.hard_fixpoint s nodes then Fix
	  else NotFix
	with
	  | Unsafe -> Unsafe_res
	  | ReachBound -> ReachBound_res
      end
    | Geninv (s, invariants, not_invariants) ->
      let invs, not_invs = 
	X.gen_inv_proc inv_search invariants not_invariants s in
      InvRes (invs, not_invs)
    | Tryinv (s, invariants) ->
      if X.is_inv inv_search s invariants then Inv else NotInv
	

  let search inv_search invgen ~invariants ~visited uns = 
    let nb_nodes = ref (if dmcmt then -1 else 0) in
    let nb_deleted = ref 0 in
    let visited = ref visited in 
    let postponed = ref [] in
    let invariants = ref invariants in
    let not_invariants = ref [] in
    let new_nodes = ref (List.map (fun s -> 0, s) uns) in
    
    let nb_inv_search = ref 0 in
    let remaining_tasks = ref 1 in

    let master (task, ()) res =
      begin
	match res, task with
	  | Unsafe_res, _ -> raise Unsafe
	  | ReachBound_res, _ -> raise ReachBound
	  | Fix, _ ->
	      decr remaining_tasks;
	      if debug then eprintf "remaining tasks = %d@." !remaining_tasks;
	      (* if invgen && gen_inv && !remaining_tasks = 0 then raise Killgeninv; *)
	      incr Profiling.cpt_fix; []

	  | NotFix, Fixcheck (s, _, _) when X.is_deleted s ->
	      decr remaining_tasks;
	      if debug then eprintf "remaining tasks = %d@." !remaining_tasks;
	      []

	  | NotFix, Fixcheck (s, cpt, _) ->
	      new_nodes := (cpt, s) :: !new_nodes;
	      decr remaining_tasks;
	      if debug then eprintf "remaining tasks = %d@." !remaining_tasks;
	      (* if delete then X.delete_nodes s visited nb_deleted false; *)
	      (* if delete then X.delete_nodes s postponed nb_deleted true; *)
	      if invgen && gen_inv (* && !nb_inv_search < 2 *) then
		begin
	    	    (* if !remaining_tasks = 0 then raise Killgeninv; *)
	    	  incr nb_inv_search;
	    	  [Geninv (s, !invariants, !not_invariants), ()]
		end
	        (* Inefficient alternative : *)
	        (* if invgen && gen_inv then *)
	        (*   begin *)
		(* 	if !remaining_tasks = 0 then raise Killgeninv; *)
		(* 	let candidates = X.extract_candidates s !not_invariants in *)
		(* 	List.map (fun p -> Tryinv (s, !invariants), ()) candidates *)
		(*   end *)
	      else []
	  | InvRes (invs, not_invs), Geninv (s, _, _) ->
	      decr nb_inv_search;
	      if delete && invs <> [] then X.delete_node s;
	      if delete then X.delete_nodes_inv invs visited;
	      if delete then X.delete_nodes_inv invs postponed;
	      invariants := List.rev_append invs !invariants;
	      not_invariants := List.rev_append not_invs !not_invariants;
	      []
	  (* | Inv, Tryinv (p, _) -> *)
	  (*     invariants := p :: !invariants; *)
	  (*     [] *)
	  (* | NotInv, Tryinv (p, _) -> *)
	  (*     not_invariants := p :: !not_invariants; *)
	  (*     [] *)
	  | _ -> assert false
      end
    in

    let rec search_rec ~post =

      if !new_nodes <> [] || !postponed <> [] then
	
	let snodes = List.stable_sort (fun (_, n1) (_, n2) ->
	  if post then
	    Pervasives.compare (X.nb_father n2) (X.nb_father n1)
	  else 
	    Pervasives.compare (X.nb_father n1) (X.nb_father n2)
	) (List.rev !new_nodes) in

	new_nodes := [];
	
	(* compute pre and etc... *)
	let pres =
	  List.fold_left (fun acc (cpt, s) ->
	    if not (X.is_deleted s) then begin
	      incr nb_nodes;
	      if !nb_nodes > X.maxnodes then raise ReachBound;
	      if not quiet then begin 
		Profiling.print "BFS" !nb_nodes (X.size s);
		let prefpr = 
		  if (not invgen) && gen_inv then "     inv gen " else " " in
		printf "%snode %d= @[%a@]@." prefpr !nb_nodes 
		  (if debug then fun _ _ -> () else X.print) s
	      end;
	      let ls, post = X.pre s in
	      let ls = List.rev ls in
	      let post = List.rev post in
	     (* Uncomment for pure bfs search *)
	     (* let ls,post= List.rev_append ls post, [] in *)
	      Profiling.update_nb_proc (X.size s);
	      
	     (* sequential invariant search *)
	     (* let inv, not_invs = *)
	     (*   if invgen && gen_inv && post <> [] then *)
	     (*     begin *)
	     (* 	X.gen_inv inv_search ~invariants:!invariants *)
	     (* 	  !not_invariants s *)
	     (*     end *)
	     (*   else [], !not_invariants *)
	     (* in *)
	     (* invariants := List.rev_append inv !invariants; *)
	     (* not_invariants := not_invs; *)
	      if delete then X.delete_nodes s visited nb_deleted false;
	      visited := s :: !visited;
	      postponed := List.rev_append post !postponed;
	      if delete then X.delete_nodes s postponed nb_deleted true;
	      List.fold_left (fun acc s -> (cpt+1, s) :: acc) acc ls
	    end
	    else acc
	  ) [] snodes
	in
	
	let pres = List.rev pres in
	
	let tasks, post =
	  if pres = [] then
	    let l = List.rev (List.rev_map (fun s -> (0, s)) !postponed) in
	    if not quiet then 
	      Profiling.print "Postpones" (List.length !postponed) 0;
	    postponed := [];
	    gentasks l !invariants !visited, true
	  else
	    gentasks pres !invariants !visited, false
	in

	remaining_tasks := List.length tasks;
	if debug then eprintf "tasks = %d@." !remaining_tasks;
	(try
	   Functory.Cores.compute ~worker:(worker inv_search) ~master tasks
	 with Killgeninv -> eprintf "Killed remaining gen inv searches @.");
	search_rec ~post
    in

    search_rec ~post:false ;
    if invgen || not gen_inv then 
      Profiling.print_report !nb_nodes !invariants !nb_deleted
    

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

module BFS_dist ( X : I ) = struct

  include BFS_dist_base(X)

  module Search = BFSnoINV (struct
    include X let maxnodes = 100
  end)
    
  let search = search Search.search true

end

module BFSinvp ( X : I ) = struct

  include BFSinvp_base(X)

  module Search = BFSnoINV (struct
    include X let maxnodes = 100
  end)
    
  let search = search Search.search

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

    (* efficient bfs *)
    (* let compare (l1, s1) (l2, s2) = *)
    (*   let v1 = X.size s1 in *)
    (*   let v2 = X.size s2 in       *)
    (*   let c = Pervasives.compare v1 v2 in *)
    (*   if c <> 0 then c else *)
    (*     let c1 = X.card s1 in *)
    (*     let c2 = X.card s2 in *)
    (*     let c = Pervasives.compare c1 c2 in *)
    (*     if c <> 0 then c else *)
    (*       Pervasives.compare l1 l2 *)
      
  end

  module Search = BFSnoINV (struct include X let maxnodes = 100 end)

  module H = Heap.Make(S)

  let search ~invariants ~visited uns =
    let nb_nodes = ref (if dmcmt then -1 else 0) in
    let nb_deleted = ref 0 in
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
	      if not quiet then Profiling.print "DFSHL" !nb_nodes (X.size s);
	      if not quiet then printf " node %d= @[%a@]@." !nb_nodes 
		(if debug then fun _ _ -> () else X.print) s;
	      let ls, post = X.pre s in
	      let post = List.rev post in
	      let inv, not_invs =
		if gen_inv && post <> [] then
		  begin
		    X.gen_inv Search.search ~invariants:!invariants
		      !not_invariants s
		  end
		else [], !not_invariants
	      in
	      invariants :=  List.rev_append inv !invariants;
	      not_invariants :=  not_invs;
	      Profiling.update_nb_proc (X.size s);
	      if delete then X.delete_nodes s visited nb_deleted false;
	      visited := s :: !visited;
	      postponed := List.rev_append post !postponed;
	      if delete then X.delete_nodes s postponed nb_deleted true;
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
	    if not quiet then 
	      Profiling.print "Postpones" (List.length !postponed) 0;
	    let l = List.rev (List.rev_map (fun s -> 0, s) !postponed) in
	    postponed := [];
	    search_rec (H.add H.empty l)
	  end
    in
    let h = H.add H.empty (List.map (fun s -> 0, s) uns) in
    search_rec h;
    Profiling.print_report !nb_nodes !invariants !nb_deleted

end

