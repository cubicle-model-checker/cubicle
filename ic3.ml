open Options
open Types
open Ast

exception Unsafe of t_system

module Solver = Smt.Make(Options)

type result =
  | RSafe
  | RUnsafe

module type SigV = sig

  type t
  (* conjonction of universally quantified clauses, good*)
  type ucnf
  (* disjunction of exisentially quantified conjunctions, bad *)
  type ednf

  type res_ref =
    | Bad_Parent
    | Covered of t
    | Extrapolated of t

  val create_good : (Variable.t list * Types.SAtom.t) list -> ucnf
  val create_bad : (Variable.t list * Types.SAtom.t) list -> ednf

  (* val print_good : Format.formatter -> t -> unit *)
  (* val print_bad : Format.formatter -> t-> unit *)
  val print_vertice : Format.formatter -> t -> unit

  val create : ucnf -> ednf -> (t * transition) list -> t
  val delete_parent : t -> t -> transition -> t
  val add_parent : t -> t -> transition -> t
  val get_parents : t -> (t * transition) list

  (* hashtype signature *)
  val hash : t -> int
  val equal : t -> t -> bool

  (* orderedtype signature *)
  val compare : t -> t -> int

  val print_id : Format.formatter -> t -> unit

  (* ic3 base functions *)
    
  (* Create a list of nodes from the node
     w.r.t the transitions *)
  val expand : t -> transition list -> transition list 
    
  val refine : t -> t -> transition -> t list -> res_ref

  (* If bad is empty, our node is safe,
     else, our node is unsafe *)
  val is_bad : t -> bool
    
end 

module type SigQ = sig

  type 'a t

  exception Empty

  val create : unit -> 'a t
  val push : 'a -> 'a t -> unit
  val pop : 'a t -> 'a
  val clear : 'a t -> unit
  val copy : 'a t -> 'a t
  val is_empty : 'a t -> bool
  val length : 'a t -> int

  val iter : ('a -> unit) -> 'a t -> unit

end
  
module Make ( Q : SigQ ) ( V : SigV ) = struct
    
  type v = V.t
  type q = V.t Q.t

  module G = Map.Make(V)

  let find_graph g v = 
    try G.find v g
    with Not_found -> []

  let replace_graph v g =
    let l = find_graph g v in
    G.add v l g

  let add_extra_graph v r g =
    let l = find_graph g v in
    G.add v (r::l) g

  type transitions = transition list

  let search system = 
    (* top = (true, unsafe) *)
    (* Create the good formula of top, true *)
    let gtop = V.create_good [[], SAtom.empty]  in
    (* Create the bad formula of top, unsafe *)
    let cunsl = system.t_unsafe in
    let cuns =
      match cunsl with
	| [f] -> f
	| _ -> assert false
    in
    let (unsv, unsf) = 
      let c = cuns.cube in (c.Cube.vars, c.Cube.litterals) in
    (* Format.eprintf "Cube Uns : %a@." Cube.print cuns.cube; *)
    let btop = V.create_bad [unsv, unsf] in
    (* Create top with gtop, btop and no parents *)
    let top = V.create gtop btop [] in

    (* Print top *)
    Format.eprintf "%a@." V.print_vertice top;    
    (* root = (init, false) *)
    let (_, initfl) = system.t_init in
    let initf = match initfl with
      | [e] -> e
      | _ -> assert false
    in
    let initl = SAtom.fold (
      fun a acc -> 
	(
	  Variable.Set.elements (Atom.variables a), 
	  SAtom.singleton a
	)::acc
    ) initf [] in
    (* Create the good formula of root, init *)
    let groot = V.create_good initl in
    (* Create the bad formula of root, false *)
    let broot = V.create_bad [[], SAtom.empty] in
    (* Create root with groot, broot and no parents *)
    let root = V.create groot broot [] in
    (* Working queue of nodes to expand and refine *)
    let todo = Q.create () in
    (* rushby graph *)
    let rgraph = G.add root [root] (G.singleton top [root]) in
    let rec refine v1 v2 tr rg =
      Format.eprintf "\n*******[Refine]*******\n \nrefining %a --%a--> %a@." 
	V.print_id v1 Hstring.print tr.tr_info.tr_name 
	V.print_id v2;
      (* In this case we are trying to execute a new transition
	 from v1 but v1 is already bad so must not be considered as
	 a parent node. *)
      if V.is_bad v1 then (
	Format.eprintf 
	  "We discard the treatment of this edge since (%d) is now bad@." (V.hash v1);
	rg
      )
      else if V.is_bad v2 then
	let pr = find_graph rg v2 in
	match V.refine v1 v2 tr pr with  
	  (* v1 and tr imply bad *)
	  | V.Bad_Parent -> 
	    (* If v1 is root, we can not refine *)
	    if V.equal v1 root then raise (Unsafe system);
	    (* Else, we recursively call refine on all the parents *)
	    List.fold_left (
	      fun acc (vp, tr) -> refine vp v1 tr acc
	    ) rg (V.get_parents v1)
	  (* The node vc covers v2 by tr *)
	  | V.Covered vc -> 
	    let v2 = V.delete_parent v2 v1 tr in
	    let vc = V.add_parent vc v1 tr in
	    let rg = replace_graph v2 (replace_graph vc rg) in
	    refine v1 vc tr rg
	  | V.Extrapolated vn -> 
	    let v2 = V.delete_parent v2 v1 tr in
	    let vn = V.add_parent vn v1 tr in
	    let rg = add_extra_graph v2 vn (replace_graph vn rg) in
	    Q.push vn todo;
	    rg
      else (
	Format.eprintf "(%a) is safe, no backward refinement@." V.print_id v2;
	rg
      )
    in
    Q.push root todo;
    let transitions = system.t_trans in
    let rec expand rg =
      let v1 = Q.pop todo in
      Format.eprintf "\n*******[Induct]*******\n \n%a\n\nTransitions :@." V.print_vertice v1;
      let trans = V.expand v1 transitions in
      List.iter (
	fun tr -> 
	  Format.eprintf "\t%a@." Hstring.print tr.tr_info.tr_name
      ) trans;
      let rg = List.fold_left (
	fun acc tr -> refine v1 top tr acc ) rg trans
      in expand rg
    in
    let _ = 
      try expand rgraph
      with Q.Empty -> Format.eprintf "Empty queue, Safe system@."
    in RSafe
end

module type SigRG = sig
  val search : t_system -> result
end

module Vertice : SigV = struct
    
  type ucnf = Cube.t list

  type ednf = Cube.t list

  type t = 
      { 
	good : ucnf;
	bad  : ednf;
	parents : (t * transition) list;
	id : int;
      }
	
  (* In case we want a hashtable *)
  let hash v = v.id
  let equal v1 v2 = v1.id = v2.id

  (* In case we want a map *)
  let compare v1 v2 = Pervasives.compare v1.id v2.id

  type res_ref =
    | Bad_Parent
    | Covered of t
    | Extrapolated of t

  let create_good = 
    List.fold_left (
      fun acc (vl, sa) -> 
	let c = Cube.create vl sa in
	c::acc
    ) []

  let create_bad = create_good

  let print_good fmt g =
    List.iter (
      fun c -> Format.eprintf "\t\tForall %a, %a@." 
	Variable.print_vars c.Cube.vars 
	(SAtom.print_sep "||") c.Cube.litterals
    ) g

  let print_igood fmt g =
    List.iter (
      fun c -> Format.eprintf "\t\t%a\nAND@." 
	(SAtom.print_sep "||") c.Cube.litterals
    ) g

  let print_bad fmt b = 
    List.iter (
      fun c -> Format.eprintf "\n\t\tExists %a, %a@. OR" 
	Variable.print_vars c.Cube.vars 
	(SAtom.print_sep "&&") c.Cube.litterals
    ) b

  let print_id fmt v = 
    match v.id with
      | 1 -> Format.eprintf "top"
      | 2 -> Format.eprintf "root"
      | i -> Format.eprintf "%d" i

  let print_vertice fmt v = 
    Format.eprintf "Vertice %a\n\tGood : %a\n\tBad : %a\n\tParents : "
      print_id v print_good v.good print_bad v.bad;
    List.iter (fun (vp, tr) -> Format.eprintf "(%d, %a)\n" vp.id Hstring.print tr.tr_info.tr_name) v.parents
      
  let create =
    let cpt = ref 0 in
    fun g b p ->
      incr cpt;
      {
	good = g;
	bad = b;
	parents = p;
	id = !cpt;
      }

  let delete_parent v p tr =
    let l = v.parents in
    let trn = tr.tr_info.tr_name in
    let rec delete acc = function
      | [] -> acc
      | (p', tr')::l when 
	  equal p p' 
	  && Hstring.equal tr'.tr_info.tr_name trn
	  -> List.rev_append acc l
      | c :: l -> delete (c::acc) l
    in 
    let nl = delete [] l in
    {v with parents = nl}

  let add_parent v p tr =
    {v with parents = (p, tr)::v.parents}

  let get_parents v = v.parents

  let get_procs n m =
    let tot = n + m in
    let rec get n vars =
      match n, vars with
	| 0, _ -> []
	| n, p::vars -> let l = get (n-1) vars in
			p::l
	| n, [] -> assert false
    in get tot Variable.procs

  let instantiate_good args good = 
    List.fold_left
      (fun i_good cube ->
	let substs = Variable.all_permutations cube.Cube.vars args in
	List.fold_left (
	  fun i_good sub ->
	    let sc = Cube.subst sub cube in
	    sc :: i_good) i_good substs
      ) [] good

  let instantiate_guard args tr = 
    let ti = tr.tr_info in
    let substs = Variable.all_permutations ti.tr_args args in
    List.fold_left (
      fun i_tr sub ->
	let st = SAtom.subst sub ti.tr_reqs in
	st :: i_tr) [] substs

  let max_args = List.fold_left (fun acc c -> max acc (Cube.dim c)) 0

  let assume_good gl = 
    fun () ->
      Prover.clear_system ();
      (* The case Smt.Unsat should never occure but we never know *)
      (try
	 List.iter (
	   fun g -> Prover.assume_clause 0 g.Cube.array
	 ) gl
       with 
	   Smt.Unsat _ -> 
	     Format.eprintf "Good is not good@."; assert false
      )
  (* Solver.save_state () *)

  let assume_guard f = Prover.assume_formula_satom 0 f

  (* let restore s = Solver.restore_state s *)

  let assume_and_restore s f =
    (* Format.eprintf "[A&R] Assuming@."; *)
    Prover.assume_formula_satom 0 f;
    (* Format.eprintf "[A&R] Restoring@."; *)
    s ()

  let assume_neg_and_restore s f =
    Prover.assume_neg_formula_satom 0 f;
    Solver.restore_state s
      
  let pickable v tr = 
    if debug && verbose > 1 then
      Format.eprintf "\ncheck the transition : %a\n@." Hstring.print tr.tr_info.tr_name;
    
    let good = v.good in
    let tr_args = tr.tr_info.tr_args in

    let n_arg_go = max_args good in
    let n_arg_tr = List.length tr_args in
    let args = get_procs n_arg_go n_arg_tr in

    let inst_goods = instantiate_good args good in
    let inst_guards = instantiate_guard args tr in
    
    (* Format.eprintf "[Pickable] Assuming good@."; *)
    let s = assume_good inst_goods in
    s ();
    let a_r_s = assume_and_restore s in
    
    (* Format.eprintf "[Pickable] Assuming and restoring@."; *)
    List.exists (
      fun e -> 
	try 
	  (* Format.eprintf "[Pickable] Begin@."; *)
	  a_r_s e; 
	  (* Format.eprintf "[Pickable] Good End@."; *)
	  true 
	with 
	    Smt.Unsat _ ->    
	      (* Format.eprintf "[Pickable] Bad End@."; *)
	      false
    ) inst_guards

  let expand v trl = List.filter (pickable v) trl

  let is_true v =
    List.for_all
      (fun sa -> 
	SAtom.exists (
	  fun a -> Atom.compare a Atom.True = 0
	) sa.Cube.litterals
      ) v.good


  let implies v1 v2 = 
    let g1 = v1.good in
    let g2 = v2.good in
    let n_g1 = max_args g1 in
    let n_g2 = max_args g2 in
    let n_args = max n_g1 n_g2 in
    let args = get_procs n_args 0 in
    let inst_g1 = instantiate_good args g1 in
    let inst_g2 = instantiate_good args g2 in
    
    
    let s = assume_good inst_g1 in
    s ();
    let a_r_s = assume_and_restore s in

    List.exists (
      fun e -> 
	try 
	  (* Format.eprintf "[Cover] Begin@."; *)
	  a_r_s e.Cube.litterals; 
	  (* Format.eprintf "[Cover] Good End@."; *)
	  true 
	with 
	    Smt.Unsat _ ->    
	      (* Format.eprintf "[Cover] Bad End@."; *)
	      false
    ) inst_g2
      
  let update_good good { Forward.i_reqs = reqs;
			 i_udnfs = udnfs;
			 i_actions = actions;
			 i_touched_terms = touched_terms } =
    Format.eprintf "Actions : %a\n@." (SAtom.print_sep "&&") actions;
	
    List.fold_left (
      fun acc g ->
	let gsa = g.Cube.litterals in
	(* if debug && verbose > 1 then *)
	Format.eprintf "GSA : %a@." (SAtom.print_sep "&&") gsa;
	(* gsa is a clause of good *)
	(* We only keep the actions feasible on this clause *)
	let pgsa = Forward.prime_satom gsa in
	let action = 
	  SAtom.filter (
	    fun act ->
	      SAtom.exists (
		fun at ->
		  match act, at with
		    | Atom.Comp (t1, _, _), Atom.Comp (t2, _, _) 
		      (* -> if Term.is_prime_term t1 then *) when Term.equal t1 t2 -> true
		    | _ -> false
	      ) gsa ||
		SAtom.exists (
		  fun at ->
		    match act, at with
		      | Atom.Comp (t1, _, _), Atom.Comp (t2, _, _) when Term.equal t1 t2 -> true
		      | _ -> false
		) pgsa
	  ) actions in
	let untouched = 
	  SAtom.filter (
	    fun at ->
	      match at with
		| Atom.Comp (t, _, _) -> not (Term.Set.mem t touched_terms)
		| _ -> true
	  ) gsa in
	Format.eprintf "Unt : %a@." (SAtom.print_sep "&&") untouched;
	Format.eprintf "Action : %a@." (SAtom.print_sep "&&") action;

	Format.eprintf "PGSA : %a@." (SAtom.print_sep "&&") pgsa;
	Format.eprintf "Touch : ";
	Term.Set.iter (
	  fun t -> Format.eprintf "%a " Term.print t) touched_terms;
	Format.eprintf "@.";
	(* let unchanged = Forward.preserve_terms touched_terms gsa in *)
	(* Format.eprintf "Unch : %a@." (SAtom.print_sep "&&") unchanged; *)

	let sa = Cube.simplify_atoms_base pgsa action in
      	let sa = Forward.wrapper_elim_prime pgsa sa in
	let sa = SAtom.union sa untouched in
      	(* if debug && verbose > 1 then ( *)
	  Format.eprintf "NSA : %a@." (SAtom.print_sep "&&") sa;
	  Format.eprintf "-------------------\n@.";

	(* ); *)
	let csa = Cube.create 
	  (Variable.Set.elements (SAtom.variables sa)) sa in
	csa::acc
    ) [] good	
      
      
  let implies_by_trans v1 v2 ({tr_info = ti} as tr) = 
    (* We want to check v1 and tr and not v2
       if it is unsat, then v1 and tr imply v2
       else, v1 and tr can not lead to v2 *)
    let g1 = v1.good in
    let g2 = v2.good in
    Format.eprintf "Good1 : %a@." print_good v1.good;
    let n_g1 = max_args g1 in
    let n_g2 = max_args g2 in
    let n_tr = List.length ti.tr_args in
    let n_args = 
      if n_g1 - n_g2 - n_tr > 0 then n_g1 - n_g2
      else n_tr 
    in
    let args = get_procs n_args n_g2 in
    Format.printf "Card : %d@." (List.length args);
    let inst_g1 = instantiate_good args g1 in
    let inst_g2 = instantiate_good args g2 in
    let inst_neg_g2 = 
      List.map (
	fun c ->
	  let l = c.Cube.litterals in
	  let l = SAtom.fold (fun a l -> SAtom.add (Atom.neg a) l) l SAtom.empty in
	  Cube.create c.Cube.vars l
      ) inst_g2 in
	  
    let inst_upd = Forward.instantiate_transitions args args [tr] in

    Format.eprintf "IG1 : %a@." print_igood inst_g1;
    Format.eprintf "Good2 : %a@." print_good v2.good;
    
    Format.eprintf "IG2 : %a@." print_igood inst_neg_g2;
    Format.eprintf "%a :@." Hstring.print ti.tr_name;
    List.iter (
      fun i -> 
	Format.eprintf "\tReqs : %a\n\tActions : %a@." 
	  SAtom.print i.Forward.i_reqs
	  SAtom.print i.Forward.i_actions 
    ) inst_upd;
    
    
    let res =
      (* Good not updated *)
      let s = assume_good inst_g1 in
      s ();
      List.for_all (
	fun iupd -> 
	  try
	    (* We check if we can execute this transition *)
	    assume_guard iupd.Forward.i_reqs;
	    
	    (* We update the good formula w.r.t the transition *)
	    let uig1 = update_good inst_g1 iupd in
	    Format.eprintf "UIG1 : %a@." print_igood uig1;
	    (* Good updated assumed *)
	    let s' = assume_good uig1 in
	    s' ();
	    (* Every time we try a new good 2, we restore
	       the system to the updated good 1 *)
	    let a_r_s = assume_and_restore s' in
	    (* If it is sat, we stop, else, we continue *)
	    let res = List.for_all (
	      fun ig2 ->
		try
		  Format.eprintf "Assume %a@." SAtom.print ig2.Cube.litterals;
		  a_r_s ig2.Cube.litterals;
		  s' ();
		  Format.eprintf "Res : SAT@.";
		  false
		with Smt.Unsat _ -> Format.eprintf "Res : UNSAT@."; true
	    ) inst_neg_g2 in
	    (* We return to good not updated for the next
	       transition *)
	    s ();
	    res
	  with Smt.Unsat _ -> s (); true
      ) inst_upd
    in res	

  let find_subsuming_vertice v1 v2 tr g =
    Format.eprintf "[Subsume] %a %a (%d)@." print_id v1 print_id v2 (List.length g);
    List.find (
      fun vs ->
	Format.eprintf "Is (%a) subsumed by (%a) by (%a)?@."
	  print_id v1 print_id vs Hstring.print tr.tr_info.tr_name;
	(is_true v2 || implies vs v2) && implies_by_trans v1 vs tr
    ) g
      

  let refine v1 v2 tr g = 
    try
      Format.eprintf "[Subsumption] Is %a covered by %a ?@." 
	print_id v2 Hstring.print tr.tr_info.tr_name;
      let vs = find_subsuming_vertice v1 v2 tr g in
      Format.eprintf "[Covered] (%a) is covered by (%a) by %a@."
	print_id v2 print_id vs Hstring.print tr.tr_info.tr_name;
      Covered vs
    with Not_found -> 
      Format.eprintf "[Extrapolation]";
      failwith "TODO"
	
  let is_bad v = List.exists (fun c -> not (SAtom.is_empty c.Cube.litterals)) v.bad

end

module RG = Make(Queue)(Vertice)

(* List.iter (Format.eprintf "%a@." SAtom.print) inst_tr; *)
(* List.exists ( *)
(*   fun i_guard -> *)
(* 	(\* Format.eprintf "\n\nTest :@."; *\) *)
(* 	List.for_all ( *)
(* 	  fun i_good ->  *)
(* 	    try *)
(* 	      (\* Format.eprintf "Good : %a@." print_good [i_good]; *\) *)
(* 	      (\* Format.eprintf "Trans : %a@." SAtom.print guard; *\) *)
(* 	      Prover.check_guard args i_good.Cube.litterals i_guard; *)
(* 	      (\* Format.eprintf "SAT@."; *\) *)
(* 	      true *)
(* 	    with Smt.Unsat _ ->  *)
(* 	      (\* Format.eprintf "UNSAT@.";*\) *)
(* 	      false *)
(* 	) inst_goods *)
(*   ) inst_guards *)
