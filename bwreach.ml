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

module Debug = struct

  let fixpoint = 
    if not debug then fun _ -> () else 
      fun ls ->
	eprintf "\nAfter simplification, subsumption and fixpoint check : @.";
	match ls with
	  | [] -> eprintf "No new branches@."
	  | _ -> 
	      List.iter (eprintf "@.New branch : %a@." Pretty.print_system) ls

  let unsafe = 
    if not debug then fun _ -> () else 
      fun s -> eprintf "    %a@." Pretty.print_unsafe s

  let invariant = 
      fun s -> eprintf "Invariant ?@. %a@." Pretty.print_cube s

  let pre = 
    if not debug then fun _ _ -> () else 
      fun tr p ->
	eprintf "\nResult of the pre for transition %s (%a):@.%a@."
	  (H.view tr.tr_name)
	  Pretty.print_args tr.tr_args
	  Pretty.print_cube p

  let pre_cubes = 
    if not debug then fun _ _ -> () else 
      fun p args ->
	eprintf "Cubes (%a) :%a@." Pretty.print_args args Pretty.print_cube p

end


(***********************************************************************)
(* Pre-image of an atom w.r.t a transition, simply represented here by *)
(* a function tau						       *)
(***********************************************************************)

let rec pre_atom tau a = 
  match a with
    | True | False -> a
    | Comp (x, op, y) -> tau x op y
    | Ite (sa, a1, a2) -> 
	let pre_sa = 
	  SAtom.fold (fun a -> add (pre_atom tau a)) sa SAtom.empty 
	in
	let pre_a1 = pre_atom tau a1 in 
	let pre_a2 = pre_atom tau a2 in 
	Ite(pre_sa, pre_a1, pre_a2)

(****************************************)
(* Convert a transition into a function *)
(****************************************)

type assign = Single of term | Branch of update

let fresh_nondet = 
  let cpt = ref 0 in 
  fun (args, ret) -> 
    incr cpt; 
    let s = H.make ("*"^(string_of_int !cpt)) in
    Smt.Symbol.declare s args ret;
    s

let rec find_update a li = function
  | [] -> raise Not_found
  | { up_arr = a'; up_arg = lj; up_swts = ls} :: _ when a=a' ->
      let ls = 
	List.map 
	  (fun (ci, ti) ->
            let sigma  = List.combine lj li in
            subst_atoms sigma (* ~sigma_sort:[Var, si] *) ci,
            subst_term sigma (* ~sigma_sort:[Var, si] *) ti) ls in
      Branch { up_arr = a'; up_arg = li; up_swts = ls}
  | _ :: l -> find_update a li l


let rec find_assign tr = function
  | Elem (x, sx) -> 
      let t = 
	if H.list_mem x tr.tr_nondets then 
	  Elem (fresh_nondet (Smt.Symbol.type_of x), sx)
	else 
	  try H.list_assoc x tr.tr_assigns with Not_found -> Elem (x, sx)
      in 
      Single t

  | Const i as a -> Single a

  | Arith (x, cs1) ->
      begin
	let t = find_assign tr x in
	match t with
	  | Single (Const cs2) -> 
	      let c = 
		Const (add_constants cs1 cs2)
	      in
	      Single c
	  | Single (Arith (y, cs2)) ->
	      Single (Arith (y, add_constants cs1 cs2))
	  | Single y -> Single (Arith (y, cs1))
	  | Branch up ->
	      Branch { up with 
		up_swts = List.map (fun (sa, y) -> (sa, (Arith (y, cs1))))
		  up.up_swts
	      }
      end
  | Access (a, li) -> 
      let nli =
        List.map (fun i ->
	  if H.list_mem i tr.tr_nondets then 
	    fresh_nondet (Smt.Symbol.type_of i)
	  else 
	    try (match H.list_assoc i tr.tr_assigns with
	      | Elem (ni, _) -> ni
	      | Const _ | Arith _ | Access _ -> assert false)
	    with Not_found -> i
        ) li in
      try find_update a nli tr.tr_upds
      with Not_found -> 
	let na = 
	  try (match H.list_assoc a tr.tr_assigns with
		 | Elem (na, _) -> na
		 | Const _ | Arith _ | Access _ -> assert false)
	  with Not_found -> a
	in
	Single (Access (na, nli))

let make_tau tr x op y =
  match find_assign tr x, find_assign tr y with
    | Single tx, Single ty -> Comp (tx, op, ty)
    | Single tx, Branch {up_arr=a; up_arg=j; up_swts=ls} ->
	List.fold_right
	  (fun (ci, ti) f -> Ite(ci, Comp(tx, op, ti), f))
	  ls True
    | Branch {up_arr=a; up_arg=j; up_swts=ls}, Single tx ->
	List.fold_right
	  (fun (ci, ti) f -> Ite(ci, Comp(ti, op, tx), f))
	  ls True
    | Branch {up_arr=a1; up_arg=j1; up_swts = ls1 },
	Branch {up_arr=a2; up_arg=j2; up_swts= ls2 } ->
	List.fold_right
	  (fun (ci, ti) f -> 
	     List.fold_right 
	       (fun (cj, tj) f ->
		  Ite(SAtom.union ci cj, Comp(ti, op, tj), f)) ls2 f)
	  ls1 True

(**********************)
(* Postponed Formulas *)
(**********************)

let rec has_args_term args = function
  | Elem (x, Var) -> H.list_mem x args
  | Access (_, lx) -> List.exists (fun z -> H.list_mem z lx) args 
  | Arith (x, _) ->  has_args_term args x
  | _ -> false

let rec has_args args = function
  | True | False -> false
  | Comp (x, _, y) -> has_args_term args x || has_args_term args y
  | Ite (sa, a1, a2) -> 
      SAtom.exists (has_args args) sa || has_args args a1 || has_args args a2

let postpone args p np = 
  let sa1 = SAtom.filter (has_args args) p in
  let sa2 = SAtom.filter (has_args args) np in
  SAtom.equal sa2 sa1

let uguard sigma args tr_args = function
  | [] -> [SAtom.empty]
  | [j, dnf] ->
      let uargs = List.filter (fun a -> not (H.list_mem a tr_args)) args in
      List.fold_left 
	(fun lureq z ->
	   let m = List.map (subst_atoms ((j, z)::sigma)) dnf in
	   List.fold_left 
	     (fun acc sa -> 
		(List.map (fun zy-> SAtom.union zy sa) m) @ acc ) [] lureq
	)
	[SAtom.empty]
	uargs

  | _ -> assert false

let add_list n l =
  if List.exists (fun n' -> ArrayAtom.subset n'.t_arru n.t_arru) l then l
  else
    let l =
      if true || delete then
  	List.filter (fun n' -> not (ArrayAtom.subset n.t_arru n'.t_arru)) l
      else l
    in
      n :: l


let max_lnp = ref 0

let make_cubes =
  fun (ls, post) (args, rargs) 
    ({ t_unsafe = (uargs, p); t_nb = nb} as s) tr np ->
      let nb_uargs = List.length uargs in
      let cube acc sigma =
	let lnp = simplify_atoms (subst_atoms sigma np) in
	let tr_args = List.map (svar sigma) tr.tr_args in
	List.fold_left
	  (fun (ls, post) np ->
	     let np, (nargs, _) = proper_cube np in
	     let lureq = uguard sigma nargs tr_args tr.tr_ureq in
	     List.fold_left 
	       (fun (ls, post) ureq ->
		 try
		  let ureq = simplification_atoms np ureq in
		  let np = SAtom.union ureq np in 
		  if debug && verbose > 0 then Debug.pre_cubes np nargs;
		  if inconsistent np then begin
		    if debug && verbose > 0 then eprintf "(inconsistent)@.";
		    (ls, post)
		  end
		  else
		    if simpl_by_uc && 
		      already_closed s tr tr_args <> None 
		    then ls, post
		    else
		      let arr_np = ArrayAtom.of_satom np in
		      let from_forall = s.t_from_forall || tr.tr_ureq <> [] in
		      let new_s = 
			{ s with
			    t_from = (tr, tr_args, s)::s.t_from;
			    t_unsafe = nargs, np;
			    t_arru = arr_np;
			    t_alpha = ArrayAtom.alpha arr_np nargs;
			    t_nb = new_cube_id ();
			    t_nb_father = nb;
			    t_from_forall = from_forall;
			    t_refine = from_forall
				 (* && List.length nargs > List.length uargs *);
			} in
		      
		      match post_strategy with
			| 0 -> add_list new_s ls, post
			| 1 -> 
			    if List.length nargs > nb_uargs then
			      ls, add_list new_s post
			    else add_list new_s ls, post
			| 2 -> 
			    if not (SAtom.is_empty ureq) || postpone args p np 
			    then ls, add_list new_s post
			    else add_list new_s ls, post
			| _ -> assert false
		 with Exit -> ls, post
	       ) (ls, post) lureq ) acc lnp
      in
      if List.length tr.tr_args > List.length rargs then begin
        if !size_proc = 0 then assert false;
        (ls, post)
      end
      else
        (* let rargs = if List.length rargs > 2 then [Hstring.make "#1"; Hstring.make "#2"] else rargs in *)
	let d = all_permutations tr.tr_args rargs in
	List.fold_left cube (ls, post) d


let fresh_args ({ tr_args = args; tr_upds = upds} as tr) = 
  if args = [] then tr
  else
    let sigma = build_subst args fresh_vars in
    { tr with 
	tr_args = List.map (svar sigma) tr.tr_args; 
	tr_reqs = subst_atoms sigma tr.tr_reqs;
	tr_ureq = 
	List.map 
	  (fun (s, dnf) -> s, List.map (subst_atoms sigma) dnf) tr.tr_ureq;
	tr_assigns = 
	List.map (fun (x, t) -> x, subst_term sigma t) 
	  tr.tr_assigns;
	tr_upds = 
	List.map 
	  (fun ({up_swts = swts} as up) -> 
	     let swts = 
	       List.map 
		 (fun (sa, t) -> subst_atoms sigma sa, subst_term sigma t) swts
	     in
	     { up with up_swts = swts }) 
	  upds}


let append_extra args tr_args =
  let rec aux acc cpt = function
    | [] -> List.rev acc
    | _::r -> aux ((List.nth proc_vars (cpt - 1)) :: acc) (cpt+1) r
  in
  aux (List.rev args) (List.length args + 1) tr_args   
  

(*****************************************************)
(* Pre-image of an unsafe formula w.r.t a transition *)
(*****************************************************)

let pre tr unsafe =
  let tr = fresh_args tr in
  let tau = make_tau tr in
  let pre_unsafe = 
    SAtom.union tr.tr_reqs 
      (SAtom.fold (fun a -> SAtom.add (pre_atom tau a)) unsafe SAtom.empty)
  in
  if debug && verbose > 0 then Debug.pre tr pre_unsafe;
  let pre_unsafe, (args, m) = proper_cube pre_unsafe in
  if tr.tr_args = [] then tr, pre_unsafe, (args, args)
  else
    let nargs = append_extra args tr.tr_args in
    if !size_proc <> 0 && List.length nargs > !size_proc then
      tr, pre_unsafe, (args, args)
    else tr, pre_unsafe, (args, nargs)


(*********************************************************************)
(* Pre-image of a system s : computing the cubes gives a list of new *)
(* systems							     *)
(*********************************************************************)

let pre_system ({ t_unsafe = uargs, u; t_trans = trs} as s) =
  if profiling then TimePre.start (); 
  Debug.unsafe s;
  let ls, post = 
    List.fold_left
    (fun acc tr ->
       let tr, pre_u, info_args = pre tr u in
       make_cubes acc info_args s tr pre_u) 
    ([], []) 
    trs 
  in
  if profiling then TimePre.pause ();
  ls, post


(********************************************************)
(* Renames the parameters of the initial unsafe formula *)
(********************************************************)

let init_atoms_sigma args sa = 
  let cpt = ref 0 in
  let sigma = 
    List.map 
      (fun z -> incr cpt; z, H.make ("#"^(string_of_int !cpt))) args in
  let sa = apply_subst sa sigma in
  let args = List.map snd sigma in
  sigma, args, sa

let init_atoms args sa =
  let _, args, sa = init_atoms_sigma args sa in
  args, sa

let init_forward (args, ex_args, sa) = 
  let sigma, args, sa = init_atoms_sigma args sa in
  let ex_args = List.map (svar sigma) ex_args in
  args, ex_args, sa
  

let init_parameters ({t_unsafe = (args, sa); t_invs = invs; t_cands = cands } as s) =
  let args, sa = init_atoms args sa in
  let a = ArrayAtom.of_satom sa in
  let invs = List.map (fun (argsi, sai) -> init_atoms argsi sai) invs in
  let cands = List.map (fun (argsi, sai) -> init_atoms argsi sai) cands in
  { s with
    t_unsafe = args, sa;
    t_forward = List.map init_forward s.t_forward;
    t_arru = a; 
    t_alpha = ArrayAtom.alpha a args; 
    t_invs = invs;
    t_cands = cands;
  }



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

  if do_brab then
    Brab.brab search invariants uns
  else
    search ~invariants ~visited:[] ~forward_nodes:[]
      ~candidates:(ref candidates) uns
