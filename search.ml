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

module Profiling = struct
  
  let round = 
    if not profiling then fun _ -> () 
    else fun cpt -> eprintf "@.-- Round %d@." cpt

  let cpt_visited = ref 0

  let reset () = 
    cpt_visited := 0

  let incr_visited = 
    if not profiling then fun () -> () else fun () -> incr cpt_visited
      
  let print_visited = 
    if not profiling then fun () -> ()
    else fun () -> eprintf "Number of visited nodes : %d@." !cpt_visited

  let print = 
    if not profiling then fun _ -> ()
    else fun s -> eprintf "%s@." s
end


module type I = sig
  type t

  val size : t -> int

  val maxrounds : int

  val safety : t -> unit
  val pre : 
    invariants:(t list) -> visited: t list -> t -> t list * t list
  val gen_inv : ( t -> unit) -> t -> t list
end

module type S = sig 
  type t
  val search : t -> unit
end


module DFS ( X : I ) = struct

  type t = X.t

  let search s =
    let rec search_rec cpt visited s =
      if cpt = X.maxrounds then raise ReachBound;
      Profiling.incr_visited ();
      Profiling.print (sprintf "[DFS]Number of processes : %d" (X.size s));
      X.safety s;
      let ls, post = X.pre ~invariants:[] ~visited:visited s in
      List.iter (search_rec (cpt+1) (s::visited)) (ls@post)
    in 
    search_rec 0 [] s

end

module DFSL ( X : I ) = struct

  type t = X.t
  
  let search s =
    let visited = ref [] in
    let rec search_rec cpt s = 
      if cpt = X.maxrounds then raise ReachBound;
      Profiling.incr_visited ();
      Profiling.print (sprintf "Number of processes : %d" (X.size s));
      X.safety s;
      let ls, post = X.pre ~invariants:[] ~visited:!visited s in
      visited := s :: !visited;
      List.iter (search_rec (cpt+1)) (ls@post)
    in
    search_rec 0 s;
    eprintf "[DFSL]"; 
    Profiling.print_visited ()

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
	let c = Pervasives.compare l1 l2 in
	if c<>0 then c else Pervasives.compare v2 v1
      else 
	let c = Pervasives.compare v2 v1 in
	if c <> 0 then c else Pervasives.compare l2 l1
  end

  module H = Heap.Make(S)

  let search s =
    let rec search_rec h =
      try 
	let (cpt, s, visited), h = H.pop h in
	Profiling.incr_visited ();
	Profiling.print 
	  (sprintf "(%d) Number of processes : %d" cpt (X.size s));
	if cpt = maxrounds then raise ReachBound;
	X.safety s;
	let ls, post = X.pre ~invariants:[] ~visited:visited s in
	let l = List.map (fun s' -> cpt+1, s', s::visited) (ls@post) in
	search_rec (H.add h l)
      with Heap.EmptyHeap -> ()
    in
    search_rec (H.add H.empty [0, s, []]);
    Profiling.print_visited ()

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
	let c = Pervasives.compare l1 l2 in
	if c<>0 then c else Pervasives.compare v2 v1
      else 
	let c = Pervasives.compare v2 v1 in
	if c <> 0 then c else Pervasives.compare l2 l1
  end

  module Search = DFSL (X)

  module H = Heap.Make(S)

  let search s =
    let visited = ref [] in
    let postpones = ref [] in
    let invariants = ref [] in
    let rec search_rec h =
      try 
	let (cpt, s), h = H.pop h in
	Profiling.incr_visited ();
	Profiling.print 
	  (sprintf "(%d) Number of processes : %d" cpt (X.size s));
	if cpt = maxrounds then raise ReachBound;
	X.safety s;
	let ls, post = X.pre ~invariants:!invariants ~visited:!visited s in
	if gen_inv && X.size s < 3 && ls <> [] then 
	  invariants := (X.gen_inv Search.search s) @ !invariants;
	if ls <> [] then visited := s::!visited;
	postpones := post @ !postpones;
	let ls = List.map (fun s' -> cpt+1, s') ls in
	search_rec (H.add h ls)
      with Heap.EmptyHeap -> 
	if !postpones = [] then ()
	else 
	  begin
	    Profiling.print 
	      (sprintf "Postpones : %d@." (List.length !postpones));
	    let l = List.map (fun s -> 0,s) !postpones in
	    postpones := [];
	    search_rec (H.add H.empty l)
	  end
    in
    let h = H.add H.empty [0, s] in 
    search_rec h;
    Profiling.print_visited ()

end

module BFS ( X : I ) = struct

  type t = X.t

  let search s = 
    let visited = ref [] in
    let postpones = ref [] in
    let q = Queue.create () in
    let rec search_rec () =
      try 
	let s = Queue.take q in
	Profiling.incr_visited ();
	Profiling.print (sprintf "Number of processes : %d" (X.size s));
	X.safety s;
	let ls, post = X.pre ~invariants:[] ~visited:!visited s in
	visited := s :: !visited;
	postpones := post @ !postpones;
	List.iter (fun s -> Queue.add s q) ls;
	search_rec ()
      with Queue.Empty -> 
	if !postpones = [] then ()
	else 
	  begin
	    Profiling.print 
	      (sprintf "Postpones : %d@." (List.length !postpones));
	    List.iter (fun s -> Queue.add s q) !postpones;
	    postpones := [];
	    search_rec ()
	  end

    in
    Queue.add s q; search_rec ();
    Profiling.print_visited ()

end
