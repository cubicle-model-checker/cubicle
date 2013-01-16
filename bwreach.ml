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

let rec find_update a i si = function
  | [] -> raise Not_found
  | { up_arr = a'; up_arg = j; up_swts = ls} :: _ when a=a' -> 
      let ls = 
	List.map 
	  (fun (ci, ti) -> 
            subst_atoms [j, i] ~sigma_sort:[Var, si] ci,
            subst_term [j, i] ~sigma_sort:[Var, si] ti) ls in
      Branch { up_arr = a'; up_arg = i; up_swts = ls}
  | _ :: l -> find_update a i si l


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
  | Access (a, i, si) -> 
      let ni, sni = 
	if H.list_mem i tr.tr_nondets then 
	  fresh_nondet (Smt.Symbol.type_of i), si
	else 
	  try (match H.list_assoc i tr.tr_assigns with
		 | Elem (ni, sni) -> ni, sni
		 | Const _ | Arith _ | Access _ -> assert false)
	  with Not_found -> i, si
      in
      try find_update a ni sni tr.tr_upds
      with Not_found -> 
	let na = 
	  try (match H.list_assoc a tr.tr_assigns with
		 | Elem (na, _) -> na
		 | Const _ | Arith _ | Access _ -> assert false)
	  with Not_found -> a
	in
	Single (Access (na, ni, sni))

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
  | Elem (x, Var) | Access (_, x, _) -> H.list_mem x args
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
  (* let cpt = ref 0 in *)
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
		      (* incr cpt; *)
		      let new_s = 
			{ s with
			    t_from = (tr, tr_args, s)::s.t_from;
			    t_unsafe = nargs, np;
			    t_arru = arr_np;
			    t_alpha = ArrayAtom.alpha arr_np nargs;
			    t_nb = new_cube_id ();
			    t_nb_father = nb;
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
      if List.length tr.tr_args > List.length rargs then 
	assert false (* (ls, post) *)
      else
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
      (SAtom.fold (fun a -> add (pre_atom tau a)) unsafe SAtom.empty)
  in
  if debug && verbose > 0 then Debug.pre tr pre_unsafe;
  let pre_unsafe, (args, m) = proper_cube pre_unsafe in
  if tr.tr_args = [] then tr, pre_unsafe, (args, args)
  else tr, pre_unsafe, (args, append_extra args tr.tr_args)
  (* else tr, pre_unsafe, (args, m::args) *)


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

(**********************************)
(* Invariant generation stuff...  *)
(**********************************)

let rec same_number z = function 
  | Const _ -> true
  | Elem (s, v) -> 
      H.equal s z || v = Glob || v = Constr
  | Access (_, s, _) -> H.equal s z
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


let candidates forward_nodes ({t_unsafe = args, sp; t_arru = ap} as s) =
  let f_args = match forward_nodes with 
    | {t_alpha = f_args, _} :: _ -> f_args
    | [] -> assert false
  in
  let perms = all_permutations f_args args in
  let inst_forward_nodes =
    List.fold_left (fun acc sigma ->
      let fs =
	List.fold_left (fun acc {t_alpha = f_args, af} ->
	  ArrayAtom.apply_subst sigma af :: acc) [] forward_nodes
      in fs :: acc)
      [] perms
  in
  List.map (fun c ->
    let c =
      try simplification_atoms SAtom.empty c
      with Exit -> assert false (* SAtom.singleton False  *)in
    let c, (c_args, _) = proper_cube c in
    let ac = ArrayAtom.of_satom c in
    { s with
      t_from = [];
      t_unsafe = c_args, c;
      t_arru = ac;
      t_alpha = ArrayAtom.alpha ac c_args;
      t_deleted = false;
      t_nb = 0;
      t_nb_father = -1;
    })
    (* (Prover.extract_candidates args ap inst_forward_nodes) *)
    (simple_extract_candidates ap inst_forward_nodes)




(*----------------------------------------------------------------------------*)

let bad_candidates = ref []
let bad_traces = ref []

let rec origin s = match s.t_from with
  | [] -> s
  | (_,_, p)::_ ->
      if p.t_nb < 0 then p
      else origin p

let add_bad_candidate ({t_unsafe = args, _; t_alpha = a_args, ar } as s) trace =
  List.iter (fun sigma ->
    bad_candidates := 
      fst 
        (proper_cube
           (ArrayAtom.to_satom (ArrayAtom.apply_subst sigma ar))) ::
      !bad_candidates
  ) (all_permutations a_args args);
  match trace with
    | Some tr ->
        List.iter (fun sa -> bad_candidates := sa :: !bad_candidates)
          (Forward.conflicting_from_trace s tr);
        (* if not (List.mem tr !bad_traces) then bad_traces := tr :: !bad_traces *)
    | None -> ()

let rec remove_cand s faulty candidates uns =
  let trace = List.map (fun (tr, args, _) -> tr, args) faulty.t_from in 
  let nc = 
    List.fold_left 
      (fun acc s' -> 
	(* if fixpoint ~invariants:[] ~visited:[s'] s then acc *)
	
	if (* None <> fixpoint ~invariants:[] ~visited:[s'] s || *)
	   (* List.exists  *)
	   (* (fun (_,_,s) ->  *)
	   (*   None <> fixpoint ~invariants:[] ~visited:[s'] s) s.t_from *)
           ArrayAtom.equal s.t_arru s'.t_arru
	then
	  (* raise UNSAFE if we try to remove a candidate 
	     which is an unsafe property *)
	  if List.exists (fun s -> ArrayAtom.equal s.t_arru s'.t_arru) uns then
	    raise (Search.Unsafe s)
	  else (add_bad_candidate s' (Some trace); acc)
        else if Forward.reachable_on_trace s' trace then 
          (add_bad_candidate s' None; acc)
	else s'::acc)
      [] candidates in
  List.rev nc

let rec elim_bogus_invariants search invariants candidates =
  try
    search ~invariants ~visited:[] ~forward_nodes:[] ~candidates:(ref []) candidates;
    candidates
  with
    | Search.Unsafe s ->
	(* FIXME Bug when search is parallel *)
	elim_bogus_invariants search invariants 
	  (remove_cand s s candidates [])

let rec search_bogus_invariants search invariants candidates uns =
  eprintf "Nombre d'invariants restant : %d (%a)@." 
    (List.length candidates) 
    (fun fmt l -> List.iter (fun x -> fprintf fmt "%d " x.t_nb) l) candidates;
  try
    let uns, cands = if lazyinv then uns, candidates else candidates@uns, [] in
    search ~invariants ~visited:[] ~forward_nodes:[] ~candidates:(ref cands) uns
  with
    | Search.Unsafe faulty ->
	(* FIXME Bug when search is parallel *)
	let o = origin faulty in
	eprintf "The node %d = %a is UNSAFE@." o.t_nb Pretty.print_system o;
	if o.t_nb >= 0 then raise (Search.Unsafe faulty);
	search_bogus_invariants search invariants 
	  (remove_cand o faulty candidates uns) uns


let search_backtrack_backforth search invariants uns =
  let candidates = ref [] in
  let rec search_rec uns =
    try
      search ~invariants ~visited:[] ~forward_nodes:[] ~candidates uns
    with
      | Search.Unsafe faulty ->
	(* FIXME Bug when search is parallel *)
	  let o = origin faulty in
	  eprintf "The node %d = %a is UNSAFE@." o.t_nb Pretty.print_system o;
	  if o.t_nb >= 0 then raise (Search.Unsafe faulty);
          eprintf "%d used candidates :@." (List.length !candidates);
          List.iter (fun s ->
            eprintf "   %a\n@." Pretty.print_system s) !candidates;
          candidates := remove_cand o faulty !candidates uns;
          eprintf "%d bad candidates :@." (List.length !bad_candidates);
          List.iter (fun sa ->
            eprintf "   %a\n@." Pretty.print_cube sa) !bad_candidates;
          search_rec uns
  in
  search_rec uns

(*----------------------------------------------------------------------------*)


let gen_inv_with_forward search ~invariants ~forward_nodes not_invs s =
  (* try_inv search ~invariants [] not_invs (candidates forward_nodes s) *)
  elim_bogus_invariants search invariants
    (Forward.select_relevant_candidates s forward_nodes), []
  (* List.fold_left  *)
  (*   (fun (invs, not_invs) p -> *)
  (*      try *)
  (* 	 let invariants = invs@invariants in *)
  (* 	 (\* if fixpoint ~invariants:invariants ~visited:[] p then invs  *\) *)
  (* 	 (\* else *\) *)
  (* 	 if impossible_inv p not_invs || trivial_inv p invs then invs, not_invs *)
  (* 	 else begin *)
  (* 	   eprintf "candidate : %a @." Pretty.print_system p; *)
  (* 	   search ~invariants:invariants ~visited:[] ~forward_nodes:[] [p];  *)
  (* 	   if not quiet then eprintf "INVARIANT : %a @." Pretty.print_system p; *)
  (* 	   p::invs, not_invs *)
  (* 	 end *)
  (*      with | Search.Unsafe | ReachBound -> invs, p::not_invs)  *)
  (*   ([], not_invs) (candidates forward_nodes s) *)




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


module SSAtoms = Set.Make(SAtom)

let nb_arrays_sa sa =
  SAtom.fold (fun a n -> match a with
    | Comp (Elem _, _, Elem _) -> n
    | Comp (Elem _, _, Access _) | Comp (Access _, _, Elem _) -> n + 1
    | Comp (Access _, _, Access _) -> n + 2
    | _ -> n
  ) sa 0

let nb_arrays s = nb_arrays_sa (snd s.t_unsafe)

let nb_neq s =
  SAtom.fold (fun a n -> match a with
    | Comp (_, Neq, _) -> n + 1
    | _ -> n
  ) (snd s.t_unsafe) 0


let local_parts =
  let forward_procs = Forward.procs_from_nb enumerative in
  let cpt = ref 0 in
  fun ({ t_unsafe = (args, sa) } as s) ->
    let init = 
      SAtom.fold (fun a acc ->
        if Forward.useless_candidate (SAtom.singleton a) then acc
        else SSAtoms.add (SAtom.singleton a) acc)
        sa SSAtoms.empty in
    let parts =
      SAtom.fold (fun a acc ->
        if Forward.useless_candidate (SAtom.singleton a) then acc
        else
          SSAtoms.fold (fun sa' acc ->
            let nsa = SAtom.add a sa' in
            let nargs = args_of_atoms nsa in
            if List.length nargs > enumerative then acc
            else if SAtom.cardinal nsa > 3 then acc
            else SSAtoms.add nsa acc
          ) acc acc
      ) sa init
    in
    let parts = SSAtoms.fold (fun sa' acc ->
      if SAtom.equal sa' sa then acc
      (* Heuristic : usefull for flash *)
      else if SAtom.cardinal sa' >= 3 && nb_arrays_sa sa' > 1 then acc
      else
        let sa', (args', _) = proper_cube sa' in
        if List.exists (fun sa -> SAtom.subset sa' sa || SAtom.subset sa sa')
          !bad_candidates then acc
        else
          let d = List.rev (all_permutations args' forward_procs) in
          (* keep list.rev in order for the first element of perm to be
             a normalized cube as we will keep this only one if none of
             perm can be disproved *)
          let perms = List.fold_left (fun p sigma ->
            let sa' = subst_atoms sigma sa' in
            let ar' = ArrayAtom.of_satom sa' in
            decr cpt;
            let s' = 
              { s with
	        t_from = [];
	        t_unsafe = args', sa';
	        t_arru = ar';
	        t_alpha = ArrayAtom.alpha ar' args';
	        t_deleted = false;
	        t_nb = !cpt;
	        t_nb_father = -1;
              } in
            s' :: p) [] d
          in
          perms :: acc
    ) parts []
    in
    List.fast_sort (fun l1 l2 ->
      let s1 = List.hd l1 in
      let s2 = List.hd l2 in
      let c = Pervasives.compare (card_system s1) (card_system s2) in
      if c <> 0 then c
      else 
        let c = Pervasives.compare (size_system s1) (size_system s2) in
        if c <> 0 then c
        else 
          let c = Pervasives.compare (nb_neq s2) (nb_neq s1) in
          if c <> 0 then c
          else
            Pervasives.compare (nb_arrays s1) (nb_arrays s2)
          (* if c <> 0 then c *)
          (* else *)
          (*   SAtom.compare (snd s1.t_unsafe) (snd s2.t_unsafe) *)
    ) parts

(* TODO : approx trees *)

let subsuming_candidate s =
  let parts = local_parts s in
  let check = fun s ->
    if List.exists (Forward.reachable_on_trace s) !bad_traces then 
      (add_bad_candidate s None; false)
    else true in
  Enumerative.smallest_to_resist_on_trace check parts


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
  let gen_inv_with_forward = gen_inv_with_forward
  let gen_inv_proc = gen_inv_proc
  let extract_candidates = extract_candidates
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

  let add_and_resolve = add_and_resolve

  let has_deleted_ancestor = has_deleted_ancestor
  let print = Pretty.print_node
  let print_bad = Pretty.print_bad
  let print_dead = Pretty.print_dead_node
  let print_cand = Pretty.print_dead_node_to_cand
  let print_system = Pretty.print_system
  let sort = List.stable_sort (fun {t_unsafe=args1,_} {t_unsafe=args2,_} ->
    Pervasives.compare (List.length args1) (List.length args2))
  let nb_father s = s.t_nb_father
    
  let system s  : t_system = s

  let subsuming_candidate = subsuming_candidate
end

module StratDFS = Search.DFS(T)
module StratDFSL = Search.DFSL(T)
module StratDFSH = Search.DFSH(T)
module StratBFS = Search.BFS(T)
module StratBFS_dist = Search.BFS_dist(T)
module StratBFSinvp = Search.BFSinvp(T)
module StratDFSHL = Search.DFSHL(T)
module StratBFS_trie = Search.BFS_trie(T)

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
    | Bfstrie -> StratBFS_trie.search
    | DfsHL -> StratDFSHL.search
    | Induct -> Induct.search


let system uns =
  let uns = List.map init_parameters uns in
  let invariants, candidates = match uns with
    | s::_ -> T.invariants s, T.candidates s
    | [] -> assert false
  in

  (*--------------- Forward invariants inference -------------------*)

  if stateless && forward_inv <> -1 then begin

    let procs = Forward.procs_from_nb forward_inv in

    eprintf "STATELESS SYMBOLIC FORWARD :\n-------------\n@.";
    let comps = (Forward.search_stateless procs (List.hd uns)) in
    eprintf "-------------\n@.";
    
    eprintf "CANDIDATES from trace :\n-----------------------\n@.";
    let candidates = 
      Forward.extract_candidates_from_compagnons comps (List.hd uns)
    in
    let cpt = ref 0 in
    List.iter (fun sa -> incr cpt;
      eprintf "candidate %d : %a\n@." !cpt Pretty.print_system sa)
      candidates;
    eprintf "-----------------------\n@.";

    if only_forward then exit 0;
    search_bogus_invariants search invariants candidates uns

  end

  else if forward_inv <> -1 then begin

    let procs = Forward.procs_from_nb forward_inv in

    eprintf "SYMBOLIC FORWARD :\n-------------\n@.";
    let forward_nodes = (Forward.search procs (List.hd uns)) in
    eprintf "-------------\n@.";
    
    let var_terms = Cube.all_var_terms procs (List.hd uns) in

    eprintf "CANDIDATES from trace :\n-----------------------\n@.";
    let candidates = 
      Forward.extract_candidates_from_trace 
	forward_nodes var_terms (List.hd uns)
    in
    (* let candidates = T.sort candidates in *)
    let cpt = ref 0 in
    List.iter (fun sa -> incr cpt;
      eprintf "candidate %d (%d) : %a\n@." !cpt sa.t_nb Pretty.print_system sa)
      candidates;
    eprintf "-----------------------\n@.";

    if only_forward then exit 0;      
    search_bogus_invariants search invariants candidates uns

  end

  else if enumerative <> -1 && backforth then begin

    let procs = Forward.procs_from_nb enumerative in
    eprintf "STATEFULL ENUMERATIVE FORWARD :\n-------------\n@.";
    Enumerative.search procs (List.hd uns);

    eprintf "-------------\n@.";
    
    if only_forward then exit 0;
    (* search_bogus_invariants search invariants candidates uns *)
    (* search ~invariants ~visited:[] ~forward_nodes:[] ~candidates:(ref []) uns *)
    search_backtrack_backforth search invariants uns

  end

  else if enumerative <> -1 then begin

    let procs = Forward.procs_from_nb enumerative in

    let candidates =
      if localized then begin
        eprintf "STATELESS ENUMERATIVE FORWARD (localized):\n-------------\n@.";
        Enumerative.local_stateless_search procs (List.hd uns) 
      end
      else begin
        eprintf "STATELESS ENUMERATIVE FORWARD :\n-------------\n@.";
        Enumerative.stateless_search procs (List.hd uns)
      end in

    eprintf "-------------\n@.";
    
    eprintf "CANDIDATES from trace :\n-----------------------\n@.";
    let cpt = ref 0 in
    List.iter (fun sa -> incr cpt;
      (* eprintf "candidate %d : %a\n@." !cpt Pretty.print_system sa) *)
      (* candidates; *)
      eprintf "(*candidate %d *) unsafe (%a) { %a }\n@." !cpt 
        Pretty.print_args (fst sa.t_unsafe) Pretty.print_system sa)
      candidates;
    eprintf "-----------------------\n@.";

    if only_forward then exit 0;
    search_bogus_invariants search invariants candidates uns

    (* TODO *)

  end

  else begin
    if only_forward then exit 0;      
    search ~invariants ~visited:[] ~forward_nodes:[] ~candidates:(ref candidates) uns
    
  end
