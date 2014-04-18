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

open Format
open Options
open Ast
open Atom
open Cube

module H = Hstring
module S = Set.Make(H)

module TimePre = Search.TimePre


open Pre

(******************************************************)
(* Backward deletion of subsumed nodes : experimental *)
(******************************************************)

let filter_rev p =
  let rec find accu = function
  | [] -> accu
  | x :: l -> if p x then find (x :: accu) l else find accu l in
  find []

let is_deleted s = s.t_deleted || has_deleted_ancestor s

let ancestor_of n s = 
  (* not (List.exists (fun (_,anc) -> n == anc) s.t_from) *)
  (* List.exists (fun (_,_,anc) -> ArrayAtom.equal n.t_arru anc.t_arru) s.t_from *)
  List.exists (fun (_,_,anc) -> n.t_nb = anc.t_nb) s.t_from
 
let subsumed_by n s =
  try 
    ArrayAtom.subset s.t_arru n.t_arru ||
      (Prover.assume_goal n; 
       Prover.assume_node s.t_arru s.t_nb; 
       false)
  with Smt.Unsat _ -> true

let delete_nodes s nodes nb_del inc =
  (* if (not s.t_deleted) && not (has_deleted_ancestor s) then *)
    nodes := filter_rev
      (fun n -> 
	if not n.t_deleted && 
	  (has_deleted_ancestor n ||
	     (not (ancestor_of n s) && ArrayAtom.subset s.t_arru n.t_arru )) 
	then 
	  begin
	    (* eprintf "deleted node@."; *)
	    n.t_deleted <- true;
	    if inc 
	    (* && not (List.exists (fun (_,_,anc) -> anc.t_deleted) n.t_from) *)
	    then incr nb_del;
	    false
	  end
	else true)
      (List.rev !nodes)

let delete_nodes_trie ({t_unsafe = (nargs,_);
                        t_alpha = args, ap;
                        t_arru = anp} as s) nodes nb_del inc =
  let substs = all_permutations args nargs in
  List.iter (fun ss ->
    let u = ArrayAtom.apply_subst ss ap in
    Cubetrie.iter_subsumed (fun n ->
      if has_deleted_ancestor n || (not (ancestor_of n s)) then begin
        n.t_deleted <- true;
        if inc then incr nb_del;
      end
    ) (Array.to_list u) !nodes;
  ) substs;
  nodes := 
    Cubetrie.delete (fun n -> n.t_deleted || has_deleted_ancestor n) !nodes


let delete_nodes_inv inv nodes = 
  nodes := List.filter
  (fun n -> 
     if (not n.t_deleted) &&
       List.exists (fun i -> ArrayAtom.subset i.t_arru n.t_arru) inv then 
       begin
	 n.t_deleted <- true;
	 false
       end
     else true)
  !nodes

let delete_node s = s.t_deleted <- true

(****************************************************)
(* Invariant generation stuff... (use brab instead) *)
(****************************************************)

let rec same_number z = function 
  | Const _ -> true
  | Elem (s, v) -> 
      H.equal s z || v = Glob || v = Constr
  | Access (_, ls) -> H.list_mem z ls
  | Arith (x, _) -> same_number z x

let rec contains_only z = function
  | True | False -> true
  | Comp (i, _ , j) -> same_number z i && same_number z j
  | Ite (sa, a1, a2) -> 
      contains_only z a1 && contains_only z a2 
      && SAtom.for_all (contains_only z) sa

let partition ({ t_unsafe = (args, sa) } as s) = 
  List.fold_left 
    (fun l z -> 
       let sa', _ = SAtom.partition (contains_only z) sa in
       if SAtom.cardinal sa' < 2 then l 
       else 
	 let ar' = ArrayAtom.of_satom sa' in
	 { s with
	   t_from = [];
	   t_unsafe = [z], sa';
	   t_arru = ar';
	   t_alpha = ArrayAtom.alpha ar' [z];
	   t_deleted = false;
	   t_nb = 0;
	   t_nb_father = -1;
	 } :: l)
    [] args



let sub_cubes s =
  let _, sa = s.t_unsafe in
  if SAtom.cardinal sa <= 2 then []
  else
    SAtom.fold (fun a acc ->
      let sa', (args, _) = proper_cube (SAtom.remove a sa) in
      let ar' = ArrayAtom.of_satom sa' in
      { s with
	t_from = [];
	t_unsafe = args, sa';
	t_arru = ar';
	t_alpha = ArrayAtom.alpha ar' args;
	t_deleted = false;
	t_nb = 0;
	t_nb_father = -1;
      } :: acc) sa []
      

let impossible_inv { t_arru = p } not_invs =
  List.exists (fun { t_arru = ni } -> ArrayAtom.subset p ni) not_invs

let trivial_inv { t_arru = p } invs =
  List.exists (fun { t_arru = i } -> ArrayAtom.subset i p) invs

let impossible_inv { t_unsafe = args,_; t_alpha = aa, ap } not_invs =
  let d = all_permutations aa args in
  List.exists (fun sigma ->
    let p = ArrayAtom.apply_subst sigma ap in
    List.exists (fun { t_arru = ni } -> ArrayAtom.subset p ni) not_invs) d

let trivial_inv { t_unsafe = args,_; t_alpha = aa, ap } invs =
  let d = all_permutations aa args in
  List.exists (fun sigma ->
    let p = ArrayAtom.apply_subst sigma ap in
    List.exists (fun { t_arru = i } -> ArrayAtom.subset i p) invs) d

type inv_result =  Inv | NotInv | Nothing

let worker_inv search invariants not_invs p =
  try 
    if impossible_inv p !not_invs then Nothing
    else begin  
      search 
	~invariants:!invariants ~visited:[] 
	~forward_nodes:[] ~candidates:(ref []) [p]; 
      if not quiet then eprintf "Good! We found an invariant :-) \n %a @." 
	Pretty.print_system p;
      Inv
    end
  with | Search.Unsafe _ | ReachBound -> NotInv

let init_thread search invariants not_invs visited postponed candidates =
  
  let master_inv (p, s) res =
    (match res with
      | Inv ->
	invariants := p :: !invariants;
	s.t_deleted <- true;
	if delete then delete_nodes_inv [p] visited;
	if delete then delete_nodes_inv [p] postponed;
      | NotInv -> not_invs := p :: !not_invs
      | Nothing -> ());
    []
  in

  Thread.create (fun () ->
    while true do
      try 
	(* let candidate = Queue.pop candidates in *)
	let candidatel = Queue.fold (fun acc c -> c::acc) [] candidates in
	let cand = List.fold_left
	  (fun acc cs ->
	    (List.map (fun x -> x, cs) (partition cs)) @ acc) [] candidatel in
	Queue.clear candidates;
	if debug then eprintf "(Thread inv) Got something to do !@.";
	Functory.Cores.compute ~worker:(worker_inv search invariants not_invs)
	  ~master:master_inv 
	  (* (List.map (fun x -> x,candidate) (partition candidate));  *)
	  cand;
	Thread.yield ();
      with Queue.Empty -> 
	Thread.yield (); eprintf "(Thread inv) Nothing to do ...@."
    done;
  ) ()


let gen_inv search ~invariants not_invs s =
  List.fold_left 
    (fun (invs, not_invs) p -> 
       try
	 let invariants = invs@invariants in
	 (* if fixpoint ~invariants:invariants ~visited:[] p then invs  *)
	 (* else *)
	 if impossible_inv p not_invs then invs, not_invs
	 else begin  
	   search ~invariants:invariants ~visited:[] ~forward_nodes:[] [p]; 
	   if not quiet then eprintf "Good! We found an invariant :-) \n %a @." 
	     Pretty.print_system p;
	   p::invs, not_invs
	 end
       with | Search.Unsafe _ | ReachBound -> invs, p::not_invs) 
    ([], not_invs) (partition s)


let rec try_inv search ~invariants invs not_invs candidates =
  List.fold_left
    (fun (invs, not_invs) p ->
       try
	 let invariants' = invs@invariants in
	 if impossible_inv p not_invs || trivial_inv p invs then invs, not_invs
	 else begin
	   eprintf "candidate : %a @." Pretty.print_system p;
	   search 
	     ~invariants:invariants' ~visited:[] 
	     ~forward_nodes:[] ~candidates:(ref []) [p]; 
	   if not quiet then eprintf "INVARIANT : %a @." Pretty.print_system p;
	   p::invs, not_invs
	 (* recursisvely try sub-cubes to find a more general invariant *)
	   (* try_inv search ~invariants (p::invs) not_invs (sub_cubes p) *)
	 end
       with 
	 | Search.Unsafe _ -> invs, p::not_invs
	 | ReachBound -> invs, not_invs)
    (invs, not_invs) candidates

let rec gen_inv search ~invariants not_invs s =
  try_inv search ~invariants [] not_invs (partition s)



(*----------------------------------------------------------------------------*)

let gen_inv_proc search invs not_invs s = 
  let new_invs, _, new_not_invs, _ =
    List.fold_left 
      (fun ((new_invs, invs, new_not_invs, not_invs) as acc) p -> 
	try
	  if impossible_inv p not_invs then acc
	  else begin
	    search 
	      ~invariants:invs ~visited:[] 
	      ~forward_nodes:[] ~candidates:(ref []) [p]; 
	    if not quiet then 
	      eprintf "Good! We found an invariant :-) \n %a @." 
		Pretty.print_system p;
	    p::new_invs, p::invs, new_not_invs, not_invs
	  end
	with Search.Unsafe _ | ReachBound ->
	  new_invs, invs, p::new_not_invs, p::not_invs) 
      ([], invs, [], not_invs) (partition s)
  in
  new_invs, new_not_invs


let extract_candidates s not_invs =
  List.filter (fun p -> not (impossible_inv p not_invs)) (partition s)

let is_inv search p invs =
  try
    search 
      ~invariants:invs ~visited:[] 
      ~forward_nodes:[] ~candidates:(ref []) [p]; 
    if not quiet then 
      eprintf "Good! We found an invariant :-) \n %a @." Pretty.print_system p;
    true
  with Search.Unsafe _ | ReachBound -> false



(* ----------------- Search strategy selection -------------------*)

module T = struct
  type t = t_system

  type fsearch = 
    invariants : t list -> 
    visited : t list -> 
    forward_nodes : t list -> 
    candidates : t list ref ->
    t list -> unit

  let invariants s = 
    List.map 
      (fun ((a,u) as i) -> 
	 let ar = ArrayAtom.of_satom u in
	 { s with 
	     t_unsafe = i;
	     t_arru = ar;
	     t_alpha = ArrayAtom.alpha ar a
	 }) s.t_invs

  let candidates s =
    let cpt = ref 0 in
    List.map
      (fun ((a,u) as i) ->
	 decr cpt;
	 let ar = ArrayAtom.of_satom u in
	 { s with
	     t_from = [];
	     t_unsafe = i;
	     t_arru = ar;
	     t_alpha = ArrayAtom.alpha ar a;
	     t_deleted = false;
	     t_nb = !cpt;
	     t_nb_father = -1;
	 }) s.t_cands

  let size = size_system
  let card = card_system
  let maxrounds = maxrounds
  let maxnodes = maxnodes
  let gen_inv = gen_inv
  let gen_inv_proc = gen_inv_proc
  let is_inv = is_inv

  let init_thread = init_thread

  let delete_nodes = delete_nodes
  let delete_nodes_inv = delete_nodes_inv
  let delete_nodes_trie = delete_nodes_trie
  let delete_node = delete_node
  let is_deleted = is_deleted

  let easy_fixpoint = easy_fixpoint
  let hard_fixpoint = hard_fixpoint

  let fixpoint = fixpoint
  let safety = check_safety

  let fixpoint_trie = fixpoint_trie
  let fixpoint_trie2 = fixpoint_trie2

  let pre = pre_system

  let post = Forward.post_system

  let has_deleted_ancestor = has_deleted_ancestor
  let print = Pretty.print_node
  let print_unsafe  = Pretty.print_unsafe
  let print_bad = Pretty.print_bad
  let print_dead = Pretty.print_dead_node
  let print_cand = Pretty.print_dead_node_to_cand
  let print_system = Pretty.print_system
  let sort = List.stable_sort (fun {t_unsafe=args1,_} {t_unsafe=args2,_} ->
    Pervasives.compare (List.length args1) (List.length args2))
  let nb_father s = s.t_nb_father
  let spurious = Forward.spurious
  let spurious_error_trace = Forward.spurious_error_trace

  let system s : t_system = s

  let subsuming_candidate = Brab.subsuming_candidate
end

module StratDFS = Search.DFS(T)
module StratDFSL = Search.DFSL(T)
module StratDFSH = Search.DFSH(T)
module StratBFS = Search.BFS(T)
module StratBFS_dist = Search.BFS_dist(T)
module StratBFSinvp = Search.BFSinvp(T)
module StratDFSHL = Search.DFSHL(T)

module InvSearch = Search.BFS(struct include T let maxnodes = 10000 end)

module Induct = Search.Inductification (T)

let search = 
  match mode with
    | Dfs -> StratDFS.search
    | DfsL -> StratDFSL.search
    | DfsH -> StratDFSH.search
    | Bfs -> StratBFS.search
    | BfsDist -> StratBFS_dist.search
    | Bfsinvp -> StratBFSinvp.search
    | DfsHL -> StratDFSHL.search
    | Induct -> Induct.search


let system uns =
  let uns = List.map init_parameters uns in
  let invariants, candidates = match uns with
    | s::_ -> T.invariants s, T.candidates s
    | [] -> assert false
  in

  let visited =
    if do_brab then
      Brab.brab search invariants uns
    else
      search ~invariants ~visited:[] ~forward_nodes:[]
	     ~candidates:(ref candidates) uns
  in
  
  match trace with
  | AltErgoTr ->
     Trace.AltErgo.certificate uns visited
  | WhyTr ->
     Trace.Why3.certificate uns visited
  | NoTrace -> ()
  
