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

exception Unsafe of t_system

type fsearch = 
    invariants : t_system list -> 
    visited : t_system list -> 
    forward_nodes : t_system list -> 
    candidates : t_system list ref ->
    t_system list -> t_system list

module type I = sig
  type t = Ast.t_system

  val size : t -> int
  val card : t -> int
  val maxrounds : int
  val maxnodes : int
  val invariants : t -> t list
  val gen_inv : 
    fsearch -> invariants : t list -> t list -> t -> t list * t list
  val gen_inv_proc : 
    fsearch -> t list -> t list -> t -> t list * t list
  val init_thread : 
    fsearch ->
    t list ref -> t list ref -> t list ref -> t list ref -> 
    t Queue.t -> Thread.t

  val is_inv : fsearch -> t -> t list -> bool

  val delete_nodes : t -> t list ref -> int ref -> bool -> unit
  val delete_nodes_trie : t -> t Cubetrie.t ref -> int ref -> bool -> unit
  val delete_nodes_inv : t list -> t list ref -> unit
  val delete_node : t -> unit
  val is_deleted : t -> bool

  val safety : t -> unit
    
  val fixpoint :
    invariants : t list -> visited : t list -> t -> (int list) option

  val easy_fixpoint : t -> t list -> (int list) option
  val hard_fixpoint : t -> t list -> (int list) option

  val fixpoint_trie2 : t Cubetrie.t -> t -> (int list) option

  val pre : t -> t list * t list
  val post : t -> t list

  val has_deleted_ancestor : t -> bool
  val print : Format.formatter -> t -> unit
  val print_unsafe : Format.formatter -> t -> unit
  val print_bad : Format.formatter -> t -> unit
  val print_dead : Format.formatter -> (t * int list) -> unit
  val print_cand : Format.formatter -> (t * int list) -> unit
  val print_system : Format.formatter -> t -> unit
  val sort : t list -> t list
  val nb_father : t -> int
  val spurious : t -> bool
  val spurious_error_trace : t -> bool

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
    t list -> t list
end

module TimeFix = Timer.Make (struct end)
module TimeEasyFix = Timer.Make (struct end)
module TimeHardFix = Timer.Make (struct end)
module TimeRP = Timer.Make (struct end)
module TimePre = Timer.Make (struct end)
module TimeSort = Timer.Make (struct end)
module TimeForward = Timer.Make (struct end)
module TimeCustom = Timer.Make (struct end)
module TimerScheduler = Timer.Make (struct end)
module TimerSearch = Timer.Make (struct end)
module TimerRC = Timer.Make (struct end)  

module Profiling = struct
  
  let round = 
    if not (profiling  && verbose > 0) then fun _ -> () 
    else fun cpt -> eprintf "@.-- Round %d@." cpt

  let cpt_fix = ref 0

  let cpt_process = ref 0

  let cpt_restart = ref (-1)

  let update_nb_proc s =
    cpt_process := max !cpt_process s
    
  let print_visited = 
    if not (profiling && verbose > 0) then fun _ -> ()
    else fun nb -> eprintf "Number of visited nodes : %d@." nb

  let print_states st pr = 
    if not profiling then ()
    else List.iter
      (eprintf "%a@." pr) st

  let print = 
    if not (profiling  && verbose > 0) then fun _ _ _ -> ()
    else fun str d size -> 
      eprintf "[%s %d] Number of processes : %d@." str d size

  let print2 str d size =
      eprintf "[%s %d] Number of processes : %d@." str d size

  let print_time fmt sec =
    let minu = floor (sec /. 60.) in
    let extrasec = sec -. (minu *. 60.) in
    fprintf fmt "%dm%2.3fs" (int_of_float minu) extrasec
    

  let print_time_fix () =
    printf "Time for fixpoint                : %a@." print_time (TimeFix.get ())

  let print_time_rp () =
    printf "├─Time for relevant permutations : %a@." print_time (TimeRP.get ())

  let print_time_formulas () =
    printf "├─Time in formulas               : %a@." print_time (Prover.TimeF.get ())

  let print_time_prover () =
    let sec = if enumsolver then Prover.ESMT.get_time () else Prover.SMT.get_time () in
    printf "└─Time in solver                 : %a@." print_time sec
      
  let print_time_pre () =
    printf "Time for pre-image computation   : %a@." print_time (TimePre.get ())

  let print_time_subset () =
    printf "├─Subset tests                   : %a@." print_time (Ast.TimerSubset.get ())

  let print_time_apply () =
    printf "├─Apply substitutions            : %a@." print_time (Ast.TimerApply.get ())

  let print_time_sort () =
    printf "├─Nodes sorting                  : %a@." print_time (TimeSort.get ())

  let print_time_custom () =
    printf "Custom timer                     : %a@." print_time (TimeCustom.get ())

  let print_time_forward () =
    let f = if schedule then TimerScheduler.get () else TimeForward.get () in
    printf "Forward exploration              : %a@." print_time f

  let print_time_search () =
    printf "Search time                      : %a@." print_time (TimerSearch.get ())

  let print_time_rc () = 
    printf "Add time rc                      : %a@." print_time (TimerRC.get ())

  let print_report nb inv del used_cands print_system =
    if used_cands <> [] then begin
      printf "\n---------------------\n";
      printf "@{<b>Inferred invariants :@}\n";
      printf "---------------------@.";
      List.iter (fun i -> printf "\n%a@." print_system i) used_cands
    end;
    printf "\n----------------------------------------------@.";
    printf "Number of visited nodes          : %d@." nb;
    printf "Fixpoints                        : %d@." !cpt_fix;
    printf "Number of solver calls           : %d@." (if enumsolver then Prover.ESMT.get_calls () else Prover.SMT.get_calls ());
    printf "Max Number of processes          : %d@." !cpt_process;
    if delete then 
      printf "Number of deleted nodes          : %d@." del;
    if gen_inv then 
      printf "Number of invariants             : %d@." (List.length inv); 
    printf "Number of invariants             : %d@." (List.length used_cands);  
    printf "Restarts                         : %d@." !cpt_restart;
    printf "----------------------------------------------@.";
    if profiling then begin
      print_time_pre ();
      print_time_fix ();
      print_time_rp ();
      print_time_subset ();
      print_time_apply ();
      print_time_sort ();
      print_time_formulas ();
      print_time_prover ();
      print_time_forward ();
      print_time_custom ();
      print_time_search ();
      print_time_rc ();
      printf "----------------------------------------------@."
    end;
    

end




module DFS ( X : I ) = struct

  type t = X.t

  let search ~invariants ~visited ~forward_nodes ~candidates uns =
    let nb_nodes = ref 0 in
    let rec search_rec cpt visited s =
      if cpt = X.maxrounds || !nb_nodes > X.maxnodes then
	raise ReachBound;
      incr nb_nodes;
      if not quiet then Profiling.print "DFS" !nb_nodes (X.size s);
      X.safety s;
      if X.fixpoint ~invariants:invariants ~visited:visited s = None then
	let ls, post = X.pre s in
	List.fold_left (search_rec (cpt+1)) (s::visited) (ls@post)
      else visited
    in
    List.fold_left (search_rec 0) visited uns

end

module DFSL ( X : I ) = struct

  type t = X.t
  
  let search ~invariants ~visited ~forward_nodes ~candidates uns =
    let visited = ref visited in
    let nb_nodes = ref (if dmcmt then -1 else 0) in
    let rec search_rec cpt s =
      if cpt = X.maxrounds || !nb_nodes > X.maxnodes then
	raise ReachBound;
      incr nb_nodes;
      if not quiet then Profiling.print "DFSL" !nb_nodes (X.size s);
      X.safety s;
      if X.fixpoint ~invariants:invariants ~visited:!visited s = None then
	begin
	  let ls, post = X.pre s in
	  visited := s :: !visited;
	  List.iter (search_rec (cpt+1)) (ls@post)
	end
    in
    List.iter (search_rec 0) uns;
    eprintf "[DFSL]";
    Profiling.print_report !nb_nodes [] 0 [] X.print_system;
    !visited

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

  let search ~invariants ~visited ~forward_nodes ~candidates uns =
    assert false
    (* let nb_nodes = ref (if dmcmt then -1 else 0) in *)
    (* let rec search_rec h = *)
    (*   let (cpt, s, visited), h = H.pop h in *)
    (*   incr nb_nodes; *)
    (*   if not quiet then Profiling.print "DFSH" !nb_nodes (X.size s); *)
    (*   if cpt = X.maxrounds || !nb_nodes > X.maxnodes then *)
    (* 	raise ReachBound; *)
    (*   X.safety s; *)
    (*   let  h = *)
    (* 	if X.fixpoint ~invariants:invariants ~visited:visited s = None *)
    (* 	then *)
    (* 	  let ls, post = X.pre s in *)
    (* 	  let l = List.map (fun s' -> cpt+1, s', s::visited) (ls@post) in *)
    (* 	  (H.add h l) *)
    (* 	else *)
    (* 	  h  *)
    (*   in *)
    (*   search_rec h *)
    (* in *)
    (* begin *)
    (*   try *)
    (* 	search_rec (H.add H.empty (List.map (fun s -> 0, s, visited) uns)) *)
    (*   with Heap.EmptyHeap -> () *)
    (* end; *)
    (* Profiling.print_report !nb_nodes [] 0 [] X.print_system *)

end

module BFS_base ( X : I ) = struct

  type t = X.t 

  let cpt_nodes = ref 0
  let cpt_dot = ref 0
  let cpt_cands = ref 0

  let nb_digits n =
    if n < 10 then 1
    else if n < 100 then 2
    else if n < 1000 then 3
    else if n < 10000 then 4
    else if n < 100000 then 5
    else if n < 1000000 then 6
    else String.length (string_of_int n)

  let extract_candidates db candidates = 
    let l = List.filter (fun n -> n <0) db in
    let rec mem l c = 
      match l with
      | [] -> false | x :: l-> x = c.t_nb || mem l c in
    List.partition (fun c -> mem l (X.system c)) candidates

  let fmt, close_dot = Pretty.dot_config file cpt_dot
    
  let fixpoint_test = X.fixpoint_trie2

  let safety_test s =
    try X.safety s with 
    | Unsafe s ->
       if refine && X.spurious_error_trace s then
	 eprintf "\nSpurious trace: @[%a@]@." Pretty.print_verbose_node s
       else
	 begin
	   if dot then fprintf fmt "@[%a@]@." X.print_bad s;
	   close_dot ();
	   raise (Unsafe s)
	 end


  let search 
      inv_search invgen ~invariants ~visited ~forward_nodes ~candidates uns =

    incr Profiling.cpt_restart;
    let uns = if lazyinv then uns else !candidates@uns in

    let discharging_allowed = 
      if lazyinv then invariants @ visited @ !candidates
      else invariants @ visited in

    let trie_visited = List.fold_left (fun acc s ->
      Cubetrie.add_array s.t_arru s acc
    ) Cubetrie.empty discharging_allowed
    in
    let visited = ref trie_visited in

    let nb_nodes = ref (if dmcmt then -1 else 0) in
    let nb_deleted = ref 0 in
    let postponed = ref [] in
    let invariants = ref invariants in
    let used_candidates = if lazyinv then ref [] else ref !candidates in
    (* let candidates = ref candidates in *)
    let not_invariants = ref [] in
    let q = Queue.create () in

    let rec search_rec_aux () =
      let cpt, s = Queue.take q in
      incr cpt_nodes;
      if cpt = X.maxrounds || !nb_nodes > X.maxnodes then
	(Profiling.print_report !nb_nodes !invariants !nb_deleted
	   !used_candidates X.print_system;
	 raise ReachBound);
      safety_test s;
      (let visited_invs =
          List.fold_left (fun visited s ->
            Cubetrie.add_array s.t_arru s visited) !visited !invariants in
        match fixpoint_test visited_invs s with
	 | Some db ->
	     if dot then fprintf fmt "@[%a@]@." X.print_dead (s, db);
	     incr Profiling.cpt_fix;
	     if lazyinv then begin
	       let ss = (X.system s).t_nb in
	       let db' = List.filter (fun x -> x <> ss) db in
	       let post, cands = extract_candidates db' !candidates in
	       cpt_cands := !cpt_cands + (List.length post);
	       if post <> [] then begin
	       	 if not quiet then 
                   eprintf "\n>>> Adding %d candidates (total %d) :@."
		     (List.length post) !cpt_cands;
                 let q' = Queue.create () in
                 Queue.transfer q q';
		 List.iter (fun s ->
		   (* eprintf "\n (\* %d *\) unsafe (z1 z2) = { %a }@."  *)
		   (*   !cpt_cands X.print_system s; *)
		   if not quiet then eprintf ">> %a@." X.print_system s;
		   Queue.add (cpt, s) q) post;
                 Queue.transfer q' q;
		 candidates := cands;
                 (* remove used candidates from the trie of visited *)
                 visited := Cubetrie.delete (fun {t_nb =id} -> 
                   List.exists (fun {t_nb = id2 } -> id = id2) post)
                   !visited;
		 used_candidates := !used_candidates @ post;
	       end;
	     end

	 | None ->
	     begin
	       if s.t_nb >= 0 then incr nb_nodes;
	       if not quiet then begin
		 Profiling.print "BFS" !nb_nodes (X.size s);
		 if dot then
		   fprintf fmt "@[%a@]@." X.print s
		 else
		   begin
		     let prefpr = 
		       if (not invgen) && gen_inv then "     inv gen " 
		       else "" in
		     printf "%snode @{<b>%d@}= @[%a@]@." prefpr !nb_nodes
		       (if debug then fun _ _ -> ()
                        else if verbose > 0 then X.print_unsafe 
                        else if verbose > 0 then 
                          fun fmt s -> fprintf fmt "%a@\n%a" X.print s X.print_system s
                        else X.print) s;
		   end
	       end;
	       let (ls, post), candidate_found = 
                 if do_brab && s.t_nb >= 0 then 
		   match X.subsuming_candidate s with 
                     | [] -> X.pre s, false
                     | l ->
                       if not quiet then 
                         List.iter (fun s' ->
		           eprintf "Approximating by @{<fg_blue>[%d]@}: %a@."
                             s'.t_nb X.print_system s';
                         ) l;
                       candidates := l @ !candidates;
                       (l, []), true
                 else X.pre s, false
               in
	       
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
               if inv <> [] then
                 visited := List.fold_left (fun visited s -> 
                   Cubetrie.add_array s.t_arru s visited) !visited inv;
               
               if not candidate_found then begin
	         postponed := List.rev_append post !postponed;
	         if delete then X.delete_nodes_trie s visited nb_deleted true;
	         visited := Cubetrie.add_array s.t_arru s !visited;
	         if delete then X.delete_nodes s postponed nb_deleted true;
	         
	         (* TODO *)
	         (* if not (fixpoint inv s) then *)
	         (*   List.iter (fun s -> Queue.add (cpt+1, s) q) ls *)
               end;

	       if inv = [] then begin
                 if candidate_found then begin
	           if dot then fprintf fmt "@[%a@]@."
                     X.print_cand (s, List.map (fun sc -> sc.t_nb) ls);
                   (* A candidate was added, in this case treat it before *)
                   let q' = Queue.create () in
                   Queue.transfer q q';
                   (* (try *)
                   (*    while true do *)
                   (*      if (snd (Queue.top q')).t_nb < 0 then *)
                   (*        Queue.add (Queue.pop q') q *)
                   (*      else raise Exit *)
                   (*    done *)
                   (*  with Exit | Queue.Empty -> ()); *)
                   List.iter (fun sc -> Queue.add (cpt, sc) q) ls;    
                   (* Queue.add (cpt, sc) q; *)
                   (* Queue.add (cpt, s) q; *)
                   Queue.transfer q' q
                 end
                 else
                   List.iter (fun s -> Queue.add (cpt+1, s) q) ls
	       end;

	       if not quiet then 
                 let r = Queue.length q + List.length !postponed in
                 printf "%s@{<dim>%d remaining@}\n@."
                 (String.make (Pretty.vt_width - 10 - nb_digits r) ' ')
                 r
	       
	     end);
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
    eprintf "nodes : %d@." !cpt_nodes;
    if dot then close_dot ()
    else if invgen || not gen_inv then 
      Profiling.print_report !nb_nodes !invariants !nb_deleted 
        (if lazyinv then !used_candidates else !candidates)
	X.print_system;
    Cubetrie.all_vals !visited

end

module BFSinvp_base ( X : I ) = struct

  type t = X.t

  let () = Functory.Cores.set_number_of_cores cores

  let search inv_search ~invariants ~visited ~forward_nodes ~candidates uns = 
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
      if X.fixpoint ~invariants:!invariants ~visited:!visited s = None
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
    Profiling.print_report !nb_nodes !invariants !nb_deleted [] X.print_system;

end


module BFS_dist_base ( X : I ) = struct

  type t = X.t 

  type task = 
    | Fixcheck of t * int * t list
    | Geninv of t * t list * t list
    | Tryinv of t * t list

  type worker_return = 
    | Fix | NotFix | Unsafe_res of t_system | ReachBound_res
    | InvRes of t list * t list
    | Inv | NotInv
  
  let () = Functory.Cores.set_number_of_cores cores
      
  exception Killgeninv

  let gentasks snodes invariants visited =
    let _, tasks = 
      List.fold_left (fun (nodes, acc) (cpt, s) ->
	if cpt = X.maxrounds then raise ReachBound;
	if None <> X.easy_fixpoint s nodes then nodes, acc
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
	  if X.hard_fixpoint s nodes = None then NotFix
	  else Fix
	with
	  | Unsafe s -> Unsafe_res s
	  | ReachBound -> ReachBound_res
      end
    | Geninv (s, invariants, not_invariants) ->
      let invs, not_invs = 
	X.gen_inv_proc inv_search invariants not_invariants s in
      InvRes (invs, not_invs)
    | Tryinv (s, invariants) ->
      if X.is_inv inv_search s invariants then Inv else NotInv
	

  let search 
      inv_search invgen ~invariants ~visited ~forward_nodes ~candidates uns = 
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
	  | Unsafe_res s, _ -> raise (Unsafe s)

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
      Profiling.print_report !nb_nodes !invariants !nb_deleted [] X.print_system
    

end



module BFSnoINV ( X : I ) = struct

  include BFS_base(X)

  let search 
      ~invariants ~visited ~(forward_nodes:X.t list) ~(candidates:X.t list ref) 
      uns = 
    search 
      (fun 
	 ~invariants:_ 
	 ~visited:_ 
	 ~forward_nodes:(_:X.t list) 
	 ~candidates:(_:X.t list ref) _ -> [] )
      false ~invariants ~visited ~forward_nodes ~candidates uns

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
    
  let search ~invariants ~visited ~forward_nodes ~candidates _ = assert false
    (* search Search.search true *)

end

module BFSinvp ( X : I ) = struct

  include BFSinvp_base(X)

  module Search = BFSnoINV (struct
    include X let maxnodes = 100
  end)
    
  let search ~invariants ~visited ~forward_nodes ~candidates _ = assert false
    (* search Search.search *)

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
    let compare (l1, s1) (l2, s2) =
      let v1 = X.size s1 in
      let v2 = X.size s2 in
      let c = Pervasives.compare v1 v2 in
      if c <> 0 then c else
        let c1 = X.card s1 in
        let c2 = X.card s2 in
        let c = Pervasives.compare c1 c2 in
        if c <> 0 then c else
    	  (* let c = Pervasives.compare (X.nb_father s1) (X.nb_father s2) in *)
          (* if c <> 0 then c else *)
            Pervasives.compare l2 l1
      
  end

  module Search = BFSnoINV (struct include X let maxnodes = 100 end)

  module H = Heap.Make(S)

  let search ~invariants ~visited ~forward_nodes ~candidates uns =
    let nb_nodes = ref (if dmcmt then -1 else 0) in
    let nb_deleted = ref 0 in
    let visited = ref visited in
    let postponed = ref [] in
    let invariants = ref invariants in
    let not_invariants = ref [] in
    let rec search_rec_aux h =
      let (cpt, s), h = H.pop h in
      if cpt = X.maxrounds || !nb_nodes > X.maxnodes then
	(Profiling.print_report !nb_nodes !invariants !nb_deleted []
	   X.print_system;
	 raise ReachBound);
      X.safety s;
      let h  =
	match X.fixpoint ~invariants:!invariants 
	  ~visited:!visited (* (List.rev_append !visited !postponed) *) s
	with 
	  | Some _ -> incr Profiling.cpt_fix; h
	  | None ->
	      begin
		incr nb_nodes;
		if not quiet then Profiling.print "DFSHL" !nb_nodes (X.size s);
		if not quiet then printf " node %d= @[%a@]@." !nb_nodes 
		  (if debug then fun _ _ -> () else X.print) s;
		let ls, post = X.pre s in
		(* eprintf "pre : %d@." (List.length ls + List.length post); *)
		(* eprintf "done : %d - remaining : %d@."  *)
		(* 	(List.length !visited) (List.length (H.elements h)); *)
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
    Profiling.print_report !nb_nodes !invariants !nb_deleted [] X.print_system;
    !visited

end


module Inductification ( X : I ) = struct

  type t = X.t

  let search ~invariants ~visited ~forward_nodes ~candidates safes = 
    let q = Queue.create () in
    let rec search_rec () =
      let cpt, s = Queue.take q in
      let _ = X.post s in
      ()
    in
    List.iter (fun s -> Queue.add (0, s) q) safes;
    search_rec ();
    assert false

end
