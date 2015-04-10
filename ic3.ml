open Options
open Types
open Ast

module Solver = Smt.Make(Options)

type result =
  | RSafe
  | RUnsafe

let step = ref 0

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

  (* val print_ucnf : Format.formatter -> t -> unit *)
  (* val print_ednf : Format.formatter -> t-> unit *)
  val print_vertice : Format.formatter -> t -> unit
  val print_dot_node : t -> unit
  val print_dot_parents : t -> unit

  val create : ucnf -> ednf -> (t * transition) list -> t
  val delete_parent : t -> t * transition -> unit
  val add_parent : t -> t * transition -> unit
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

  exception Unsafe of V.t list G.t
  exception Safe of V.t list G.t

  let print_graph g =
    Format.eprintf "[GRAPH]@.";
    G.iter (
      fun k e -> Format.eprintf "%a\n\tExtrapolation candidates:@." 
	V.print_vertice k;
	List.iter (
	  fun p -> Format.eprintf "\t\t(%a) @." V.print_id p;
	) e;
	Format.eprintf "\n--------------@."
    ) g;
    Format.eprintf "[ENDGRAPH]@."
      

  let find_graph g v = 
    try G.find v g
    with Not_found -> []

  let add_extra_graph v r g =
    let l = find_graph g v in
    G.add v (r::l) g

  let update_dot rg =
    G.iter (
      fun e _ -> 
	(* V.print_dot_node e; *)
	V.print_dot_parents e;
    ) rg
      

  type transitions = transition list

  let search close_dot system = 
    (* top = (true, unsafe) *)
    (* Create the good formula of top, true *)
    let gtop = V.create_good [[], SAtom.empty]  in
    (* Create the bad formula of top, unsafe *)
    let cunsl = system.t_unsafe in
    let cuns =
      match cunsl with
	| [f] -> 
	  Format.eprintf "[Uns] %a@." Cube.print f.cube;
	  f
	| _ -> assert false
    in
    let (unsv, unsf) = 
      let c = cuns.cube in (c.Cube.vars, c.Cube.litterals) in
    let btop = V.create_bad [unsv, unsf] in
    (* Create top with gtop, btop and no parents *)
    let top = V.create gtop btop [] in
    (* Print top *)
    Format.eprintf "%a@." V.print_vertice top;    
    
    (* root = (init, false) *)
    let (_, initfl) = system.t_init in
    let initf = match initfl with
      | [e] -> 
	Format.eprintf "[Init]%a@." (SAtom.print_sep "&&") e;
	e
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
      Format.eprintf 
	"\n*******[Refine]*******\n \nrefining (%a) --%a--> (%a)@." 
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
      else if V.is_bad v2 then (
	if debug && verbose > 1 then print_graph rg;
	let pr = find_graph rg v2 in
	match V.refine v1 v2 tr pr with  
	  (* v1 and tr imply bad *)
	  | V.Bad_Parent -> 
	    (* If v1 is root, we can not refine *)
	    if V.equal v1 root then raise (Unsafe rg);
	    (* Else, we recursively call refine on all the parents *)
	    List.fold_left (
	      fun acc (vp, tr) -> 
		Format.eprintf "[BPR] (%a) --%a--> ?@."
		  V.print_id vp Hstring.print tr.tr_info.tr_name;
		refine vp v1 tr acc
	    ) rg (V.get_parents v1)
	  (* The node vc covers v2 by tr *)
	  | V.Covered vc -> 
	    V.delete_parent v2 (v1, tr);
	    V.add_parent vc (v1, tr);
	    if debug && verbose > 1 then (
	      Format.eprintf "[Covered by] %a@." V.print_vertice vc;
	      Format.eprintf "[Forgotten] %a@." V.print_vertice v2;
	    );
	    refine v1 vc tr rg
	  | V.Extrapolated vn -> 
	    V.delete_parent v2 (v1, tr);
	    if debug && verbose > 1 then (
	      Format.eprintf "[Extrapolated by] %a@." V.print_vertice vn;
	      Format.eprintf "[Forgotten] %a@." V.print_vertice v2;
	    );
	    let rg' = add_extra_graph v2 vn (G.add vn [] rg) in
	    Q.push vn todo;
	    rg'
      )
      else (
	Format.eprintf "(%a) is safe, no backward refinement@." V.print_id v2;
	rg
      )
    in
    Q.push root todo;
    let transitions = system.t_trans in
    let rec expand rg =
      let v1 = 
	try Q.pop todo
	with Q.Empty -> raise (Safe rg)
      in
      Format.eprintf "\n*******[Induct]*******\n \n%a\n\nTransitions :@." V.print_vertice v1;
      let trans = V.expand v1 transitions in
      List.iter (
	fun tr -> 
	  Format.eprintf "\t%a@." Hstring.print tr.tr_info.tr_name
      ) trans;
      let rg = List.fold_left (
	fun acc tr -> refine v1 top tr acc ) rg trans
      in 
      let () = if Options.dot_level = 0 then
	Sys.set_signal Sys.sigint 
	  (Sys.Signal_handle 
	     (fun _ ->
               Stats.print_report ~safe:false [] [];
	       print_graph rg;
	       update_dot rg;
	       Format.eprintf "\n\n@{<b>@{<fg_red>ABORT !@}@} Received SIGINT@.";
	       close_dot ();
	       exit 1
             )) 
	  
      in	
      expand rg
    in
    try expand rgraph
    with 
      | Safe rg -> 
	if dot then update_dot rg;
	Format.eprintf "Empty queue, Safe system@."; 
	RSafe
      | Unsafe rg -> 
	if dot then update_dot rg;
	RUnsafe
end

module type SigRG = sig
  val search : (unit -> unit) -> t_system -> result
end

module Vertice : SigV = struct
    
  (* TYPES *)

  type ucnf = Cube.t list

  type ednf = Cube.t list

  type t = 
      { 
	mutable good : ucnf;
	mutable bad  : ednf;
	mutable parents : (t * transition) list;
	id : int;
      }
	
  type res_ref =
    | Bad_Parent
    | Covered of t
    | Extrapolated of t
	
  (* SIGNATURE FOR HASHTBL *)

  let hash v = v.id
  let equal v1 v2 = v1.id = v2.id

  (* SIGNATURE FOR MAP *)

  let compare v1 v2 = Pervasives.compare v1.id v2.id




  (* PRINT FUNCTIONS *)


  let print_ucnf fmt g =
    List.iter (
      fun c -> Format.eprintf "\t\tForall %a, %a AND@." 
	Variable.print_vars c.Cube.vars 
	(SAtom.print_sep "||") c.Cube.litterals
    ) g

  let print_iucnf fmt g =
    List.iter (
      fun c -> Format.eprintf "\t\t%a\nAND@." 
	(SAtom.print_sep "||") c.Cube.litterals
    ) g

  let print_ednf fmt b = 
    List.iter (
      fun c -> Format.eprintf "\n\t\t%a@. OR" 
	(* Variable.print_vars c.Cube.vars  *)
	(SAtom.print_sep "&&") c.Cube.litterals
    ) b

  let print_iednf fmt b = 
    List.iter (
      fun c -> Format.eprintf "\t\t%a\nOR@." 
	(SAtom.print_sep "&&") c.Cube.litterals
    ) b
      
  let get_id v =
    match v.id with
      | 1 -> "top"
      | 2 -> "root"
      | i -> string_of_int i


  let print_id fmt v = Format.eprintf "%s" (get_id v)

  let print_vertice fmt v = 
    Format.eprintf "Vertice (%a)\n\tGood : \n%a\n\tBad : \n%a\n\tParents :\n "
      print_id v print_ucnf v.good print_ednf v.bad;
    List.iter (
      fun (vp, tr) -> 
	Format.eprintf "\t\t(%a, %a)@." 
	  print_id vp Hstring.print tr.tr_info.tr_name) v.parents 

  let print_dot_node v = Dot.new_node_ic3 (get_id v)

  let print_dot_parents v =
    let parents = List.map (fun (v, t) -> (get_id v, t)) v.parents in
    Dot.new_relations_ic3 (get_id v) parents ~color:"blue"

  let print_dot_relation_step v v' tr =
    Dot.new_relation_step_ic3 ~style:"dotted" (get_id v) (get_id v') tr !step

  let print_dot_relation ?color:(c="black") v v' tr =
    Dot.new_relation_ic3 ~color:c ~style:"dotted" (get_id v) (get_id v') tr



  (* CREATION FUNCTIONS *)

      
  let create_good = 
    List.fold_left (
      fun acc (vl, sa) -> 
	let c = Cube.create vl sa in
	c::acc
    ) []

  let create_bad = create_good
    
  let create =
    let cpt = ref 0 in
    fun g b p ->
      incr cpt;
      let v =
	{
	  good = g;
	  bad = b;
	  parents = p;
	  id = !cpt;
	} in
      if dot then print_dot_node v;
      v

	

  (* MODIFICATION FUNCTIONS *)


  let update_bad v nb = v.bad <- List.fold_left
    (fun acc b -> b@acc) v.bad nb
    
  let delete_parent v (vp, tr) =
    let l = v.parents in
    let trn = tr.tr_info.tr_name in
    let rec delete acc = function
      | [] -> acc
      | (vp', tr')::l when 
	  equal vp vp' 
	  && Hstring.equal tr'.tr_info.tr_name trn
	  -> List.rev_append acc l
      | c :: l -> delete (c::acc) l
    in 
    let nl = delete [] l in
    v.parents <- nl

  let add_parent v (vp, tr) =
    if List.exists (
      fun (vp', tr') -> 
	equal vp vp' 
	&& Hstring.equal tr'.tr_info.tr_name tr.tr_info.tr_name
    ) v.parents 
    then ()
    else (
      v.parents <- ((vp, tr)::v.parents);
      if Options.dot_level >= 1 then
	(
	  incr step;
	  print_dot_relation_step v vp tr
	)
    )
      



  (* ACCESS FUNCTIONS *)

  let get_parents v = v.parents

  let get_procs n m =
    let tot = if !(Options.size_proc) > 0 then !(Options.size_proc)
      else n + m in
    let rec get n vars =
      match n, vars with
	| 0, _ -> []
	| n, p::vars -> let l = get (n-1) vars in
			p::l
	| n, [] -> assert false
    in
    get tot Variable.procs

  (* INSTANTIATION FUNCTIONS *)

  let instantiate_cube_list args good = 
    List.fold_left (
      fun i_good cube ->
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
	(st, sub) :: i_tr
    ) [] substs

  (* INSTANTIATION FUNCTIONS - ARGS GENERATION *)

  let max_args = List.fold_left (fun acc c -> max acc (Cube.dim c)) 0

  let nb_args tr = 
    let tri = tr.tr_info in
    let n = List.length tri.tr_args in
    if List.length tri.tr_ureq > 0 then n+1 else n

  (* SMT FUNCTIONS *)
  (* TODO : See if save_state and restore_state work *)

  let clear_and_assume_cnf gl n = 
    fun () ->
      Prover.clear_system ();
      (* The case Smt.Unsat should never occure but we never know *)
      (try
	 List.iter (
	   fun g -> 
	     if not (SAtom.is_empty g.Cube.litterals)
	     then
	       Prover.assume_clause  n g.Cube.array
	 ) gl
       with 
	   Smt.Unsat _ -> 
	     Format.eprintf "Good is not good@."; assert false
      )
  (* Solver.save_state () *)

  let assume_conjunction f n = 
    fun () -> Prover.assume_formula_satom n f
      
  let assume_cnf gl n =
    fun () -> 
      List.iter (
	fun g -> 
	  if not (SAtom.is_empty g.Cube.litterals)
	  then
	    Prover.assume_clause n g.Cube.array
      ) gl

  let clear_and_assume_list fl =
    fun () ->
      Prover.clear_system ();
      List.iter (fun f -> f ()) fl
	
  (* let restore s = Solver.restore_state s *)
	
  let assume_cube_and_restore s n f =
    try
      if debug && verbose > 1 then
	Format.eprintf "[A&R] Assuming@.";
      Prover.assume_formula_satom n f;
      if debug && verbose > 1 then
	Format.eprintf "[A&R] Restoring@.";
      s ();
    with Smt.Unsat n -> 
      if debug && verbose > 1 then
	Format.eprintf "[A&R] Restoring@.";
      s (); 
      raise (Smt.Unsat n)
  (* Format.eprintf "[A&R] Restoring@."; *)

  (* let assume_neg_and_restore s f = *)
  (*   Prover.assume_neg_formula_satom 0 f; *)
  (*   Solver.restore_state s *)

  (* IC3 BASE FUNCTIONS *)
	
  (* Given a transition and a node, 
     Answers SAT if we can take the transition,
     Answers UNSAT otherwise *)
  let pickable v tr = 
    if debug && verbose > 0 then
      Format.eprintf "\ncheck the transition : %a\n@." Hstring.print tr.tr_info.tr_name;

    let good = v.good in
    
    let n = v.id in

    let n_arg_go = max_args good in
    let n_arg_tr = nb_args tr in
    let args = get_procs n_arg_go n_arg_tr in

    let inst_goods = instantiate_cube_list args good in
    let inst_guards = instantiate_guard args tr in
    
    if debug && verbose > 1 then
      Format.eprintf "[Pickable] Assuming good@.";
    let s = clear_and_assume_cnf inst_goods n in
    s ();
    let a_c_r_s = assume_cube_and_restore s n in
    
    if debug && verbose > 1 then
      Format.eprintf "[Pickable] Assuming and restoring@.";
    List.exists (
      fun (guard, sigma) -> 
	try 
	  (* Format.eprintf "[subst]@."; *)
	  (* List.iter ( *)
	  (*   fun (v, sub) -> Format.eprintf "(%a, %a)@." Hstring.print v Hstring.print sub) sigma; *)
	  (* Format.eprintf "[endsubst]@."; *)
	  if debug && verbose > 1 then
	    Format.eprintf "[Pickable] Begin@.";
	  a_c_r_s guard; 
	  if debug && verbose > 1 then
	    Format.eprintf "[Pickable] guard SAT@.";
	  
	  true 
	with 
	  | Smt.Unsat _ ->    
	    if debug && verbose > 1 then
	      Format.eprintf "[Pickable] UNSAT@.";
	    false
    (* | Not_found -> false *)
    ) inst_guards

  (* Given a list of transitions and a node,
     returns the list of the pickable transitions *)
  let expand v = List.filter (pickable v)

  (* Returns true if the good part of the node is
     trivially true *)
  (* COULD BE BUGGY *)
  let is_true v =
    List.for_all (
      fun sa -> 
	Cube.size sa = 0 
	|| SAtom.exists (
	  fun a -> Atom.compare a Atom.True = 0
	) sa.Cube.litterals
    ) v.good

  (* Returns true if the bad part of the node is 
     not empty *)
  let is_bad v = 
    List.exists (
      fun c -> 
	not (SAtom.is_empty c.Cube.litterals)
    ) v.bad

  (* Given a formula, returns the formula with all the
     litterals negated *)
  let negate_litterals =
    List.map (
      fun c ->
	let l = c.Cube.litterals in
	let l = SAtom.fold (fun a l -> SAtom.add (Atom.neg a) l) l SAtom.empty in
	Cube.create c.Cube.vars l
    )

  (* Given v1 and v2 returns true if v1 => v2
     returns false otherwise *)
  let implies v1 v2 = 
    let g1 = v1.good in
    let g2 = v2.good in
    let ng2 = negate_litterals g2 in
    let n1 = v1.id in
    let n2 = v2.id in
    let n_g1 = max_args g1 in
    let n_g2 = max_args ng2 in
    let n_args = max n_g1 n_g2 in
    let args = get_procs n_args 0 in
    let inst_g1 = instantiate_cube_list args g1 in
    let inst_ng2 = instantiate_cube_list args ng2 in
    
    if debug && verbose > 1 then
      Format.eprintf "[Implies] Assuming good@.";
    let s = clear_and_assume_cnf inst_g1 n1 in
    s ();
    let a_c_r_s = assume_cube_and_restore s n2 in

    if debug && verbose > 1 then
      Format.eprintf "[Implies] Assuming and restoring@.";
    let sat = List.exists (
      fun e -> 
	try 
	  if debug && verbose > 1 then
	    Format.eprintf "[Implies] Begin@.";
	  a_c_r_s e.Cube.litterals; 
	  if debug && verbose > 1 then
	    Format.eprintf "[Implies] SAT@.";
	  true 
	with 
	    Smt.Unsat _ ->    
	      if debug && verbose > 1 then
		Format.eprintf "[Implies] UNSAT@.";
	      false
    ) inst_ng2 in
    not sat

  let find_inst fun_go n1 n2 inst_f2 l = 
    let rec find_inst = function 
      | [] -> None
      | { Forward.i_reqs = reqs;
    	  i_actions = actions;
    	  i_touched_terms = terms; }::tl ->
	try
	  fun_go ();
    	  
	  (* We check if we can execute this transition *)
    	  if debug && verbose > 1 then
    	    Format.eprintf "[ImplyTrans] Check guard@.";
    	  let fun_gu = assume_conjunction reqs n1 in
	  fun_gu ();
	  
	  if debug && verbose > 1 then
    	    (
	      Format.eprintf "[ImplyTrans] Apply action@.";
    	  (* let pactions = Forward.prime_head_satom actions in *)
	      Format.eprintf "[ACTIONS] %a@." (SAtom.print_sep "&&") actions;
	    );
	  let fun_ac = assume_conjunction actions n1 in
	  fun_ac ();

	  let reset = clear_and_assume_list [fun_go; fun_gu; fun_ac] in
	  (* We prime n2 according to the terms touched by
    	     the transition *)
    	  (* Format.eprintf "[INSTF2] %a@." print_iednf inst_f2; *)
    	  (* Format.eprintf "Terms@."; *)
	  (* Term.Set.iter ( *)
	  (*   fun t -> *)
	  (*     Format.eprintf "%a@." Term.print t *)
	  (* ) terms; *)
	  (* Format.eprintf "Smret@."; *)
	  let pinst_f2 =
	    List.map (
	      fun c ->
    		let vars = c.Cube.vars in
    		let litt = c.Cube.litterals in
		let plitt = Forward.prime_head_match_satom litt terms in
		Cube.create vars plitt
	    ) inst_f2 in
	  (* Format.eprintf "[PINSTF2] %a@." print_iednf pinst_f2; *)
    	  (* Good updated assumed *)
    	  if debug && verbose > 1 then
    	    Format.eprintf "[ImplyTrans] Assuming action@.";
    	  (* Every time we try a new good 2, we restore
    	     the system to good 1 plus the guard plus the action *)
    	  
	  let a_c_r_s = assume_cube_and_restore reset n2 in
	  let res = ref None in
	  let rec f =
	    function
	      | [], [] -> raise Not_found
	      | (pif2::tl, pif2'::tl') ->
		(
		  try
    		    if debug && verbose > 1 then
    	    	      Format.eprintf "[ImplyTrans] Assume %a@."
	    		SAtom.print pif2.Cube.litterals;
    		    a_c_r_s pif2.Cube.litterals;
    		    if debug && verbose > 1 then
    	    	      Format.eprintf "[ImplyTrans] Res : SAT@.";
    		    res := Some pif2';
		    raise Exit
    		  with Smt.Unsat _ ->
    		    if debug && verbose > 1 then
    	    	      Format.eprintf "[ImplyTrans] Res : UNSAT@.";
    		    f (tl, tl')
		)
	      | _ -> assert false
	  in 
	  try f (pinst_f2, inst_f2) 
	  with Exit -> !res
	(* We go back to good not updated for the next
    	   transition *)
	with
	  | Smt.Unsat _ | Not_found -> find_inst tl
    in find_inst l
    
  (* If the result is TRUE then f1 and tr imply f2.
     When we want to know if good1 and tr imply good2,
     FALSE means YES.
     When we want to know if good1 and tr imply bad2,
     TRUE means YES.*)
  let imply_by_trans (f1, n1) (f2, n2) ({tr_info = ti} as tr) = 
    (* We want to check v1 and tr and not v2
       if it is unsat, then v1 and tr imply v2
       else, v1 and tr can not lead to v2 *)
    if debug && verbose > 2 then 
      Format.eprintf "Good1 : %a@." print_ucnf f1;
    let n_f1 = max_args f1 in
    let n_f2 = max_args f2 in
    let n_tr = List.length ti.tr_args in
    let n_args = 
      if n_f1 - n_f2 - n_tr > 0 then n_f1 - n_f2
      else n_tr 
    in
    let args = get_procs n_args n_f2 in
    if debug && verbose > 2 then 
      Format.printf "Card : %d@." (List.length args);
    let inst_f1 = instantiate_cube_list args f1 in
    let inst_f2 = instantiate_cube_list args f2 in  
    
    let inst_upd = Forward.instantiate_transitions args args [tr] in

    if debug && verbose > 2 then ( 
      Format.eprintf "IF1 : %a@." print_iucnf inst_f1;
      Format.eprintf "Good2 : %a@." print_ucnf f2;
      
      Format.eprintf "IF2 : %a@." print_iednf inst_f2;
      Format.eprintf "%a :@." Hstring.print ti.tr_name;
      
      List.iter (
	fun i -> 
	  Format.eprintf "\tReqs : %a\n\tActions : %a\n\tTouched : " 
	    SAtom.print i.Forward.i_reqs
	    SAtom.print i.Forward.i_actions;
	  Term.Set.iter (Format.eprintf "%a " Term.print) i.Forward.i_touched_terms;
	  Format.eprintf "\n@.";
      ) inst_upd;
    );  
    (* Good not updated *)
    if debug && verbose > 1 then
      Format.eprintf "\n[ImplyTrans] Assuming good@.";
    let fun_go = assume_cnf inst_f1 n1 in
    let res = find_inst fun_go n1 n2 inst_f2 inst_upd in
    Prover.clear_system ();
    res

  (* Tries to find a node in the graph which subsume
     the current node.
     Raise Not_found*)
  let find_subsuming_vertice v1 v2 tr g =
    let n = List.length g in
    if n = 0 then
      Format.eprintf "[Subsume] %a %a No subsumption@." 
	print_id v1 print_id v2
    else Format.eprintf "[Subsume] %a %a [%d]@." 
      print_id v1 print_id v2 n;
    List.find (
      fun vs ->
	Format.eprintf "[Subsumption] (%a) and (%a) to (%a) ?@." 
	  print_id v1 Hstring.print tr.tr_info.tr_name print_id vs;
	let res =
	  (is_true v2 || implies vs v2) 
	  && (
	    let nvs = negate_litterals vs.good in
	    let res = imply_by_trans (v1.good, v1.id) 
	      (nvs, vs.id) tr in 
	    match res with 
	      | None -> true
	      | Some _ -> false
	  )
	in 
	if res
	then
	  Format.eprintf "[Subsumed] (%a) is subsumed by (%a) by (%a)@." 
	    print_id v1 print_id vs Hstring.print tr.tr_info.tr_name
	else 
	  Format.eprintf "[Not subsumed] (%a) is not subsumed by (%a) by (%a)@."
	    print_id v1 print_id vs Hstring.print tr.tr_info.tr_name;
	res
    ) g

  let generalize_litterals =
    List.map (
      fun c ->
	let v = c.Cube.vars in
	let subst = Variable.build_subst v Variable.generals in
	Cube.subst subst c
    )

  (* Given a formula, tries to find the negation of it
     and then extrapolate this negation *)
  let negate_generalize_and_extrapolate f =
    let nf = negate_litterals f in
    let nf = generalize_litterals nf in
    nf

  (* Main function of IC3 *)
  let refine v1 v2 tr cand = 
    try
      Format.eprintf "Candidates %a :@." print_id v2;
      List.iter (
	fun vc -> Format.eprintf "\t%a@." print_id vc
      ) cand;
      Format.eprintf "[Subsumption] Is (%a) covered by transition %a ?@." 
	print_id v2 Hstring.print tr.tr_info.tr_name;
      (* Format.eprintf "[Resume] %a\n%a@." *)
      (* 	print_vertice v1 print_vertice v2; *)
      let vs = find_subsuming_vertice v1 v2 tr cand in
      Format.eprintf "[Covered] (%a) is covered by (%a) by %a@."
	print_id v1 print_id vs Hstring.print tr.tr_info.tr_name;
      Covered vs
    with Not_found -> 
      Format.eprintf "[Implication] (%a.good) and %a to (%a.bad) ?@."
	print_id v1 Hstring.print tr.tr_info.tr_name print_id v2;
      let res = imply_by_trans (v1.good, v1.id) (v2.bad, v2.id) tr in
      
      (* RES = Some b means good1 and tr imply bad2,
	 we then need to find a pre formula which leads to bad2 *)
      match res with
	| Some bad ->
	  Format.eprintf "[BadToParents] (%a.good) and %a imply (%a.bad)@." 
	    print_id v1 Hstring.print tr.tr_info.tr_name print_id v2;
	  print_dot_relation ~color:"red" v2 v1 tr;
	  Format.eprintf "[BadToParents] We update (%a.bad) and refine to the parents of (%a)@."
	    print_id v1 print_id v1;
	  
      	  let ncube = Node.create bad in
	  let (nl, nl') = Pre.pre_image [tr] ncube in
	  let cl = 
	    try
	      (List.hd nl).cube
	    with Failure _ ->
	      if debug && verbose > 1 then (
		Format.eprintf "[Bad] %a@." print_ednf v2.bad;
		Format.eprintf "[IBad] %a@." Cube.print bad;
		Format.eprintf "[Transition] %a@." Hstring.print tr.tr_info.tr_name;
		List.iter (
		  fun n -> Format.eprintf "[Node] %a@." Node.print n) nl;
		List.iter (
		  fun n -> Format.eprintf "[Node'] %a@." Node.print n) nl';
	      );
	      (List.hd nl').cube
	  in

	      (* let cl' = (List.hd nl').cube in *)
	  v1.bad <- [cl];
	  Bad_Parent

	(* RES = None means good1 and tr don't imply bad2,
	   we can now extrapolate good1 by adding not bad2. *)
	| None ->
	  Format.eprintf "[Extrapolation] (%a.good) and %a do not imply (%a.bad)@." 
	    print_id v1 Hstring.print tr.tr_info.tr_name print_id v2;
	  Format.eprintf "[Extrapolation] We extrapolate (%a.bad) = eb and create a new node with (%a.good) && eb@."
	    print_id v2 print_id v2;
	  let extra_bad2 = negate_generalize_and_extrapolate v2.bad in
	  if debug && verbose > 1 then (
	    Format.eprintf "[Bad] %a@." print_ednf v2.bad;
	    Format.eprintf "[EBAD2] %a@." print_ucnf extra_bad2;
	  );
	  let ng = 
	    if v2.id = 1 
	    then extra_bad2 
	    else v2.good @ extra_bad2 
	  in
	  let nv = create ng [] [v1, tr] in
	  (* Format.eprintf "NV : %a@." print_vertice nv; *)
	  print_dot_relation ~color:"green" nv v2 tr;
	  Extrapolated nv

end

module RG = Make(Queue)(Vertice)