(* TYPES *)
open Options
open Types
open Ast

let step = ref 0

type ucnf = Cube.t list

type ednf = Cube.t list

type t_kind = 
  | KOriginal
  | KExtrapolated

type t = 
    { 
      world : ucnf;
      added_clause : ucnf;
      mutable bad  : ednf;
      mutable subsume : (t * transition) list;
      predecessor : t option;
      mutable successor : t option;
      creation : (t * transition * t) option;
      mutable bad_from : (transition * t) list;
      mutable world_from : t list;
      id : int;
      kind : t_kind;
      is_root : bool;
    }
      
type res_ref =
  | Bad_Parent of (int * Cube.t list)
  | Covered of t
  | Extrapolated of t

type res_easy = EDontKnow | EUnsat


let hash v = v.id
let equal v1 v2 = v1.id = v2.id
  
(* SIGNATURE FOR HASHTBL *)

(* module HTVertice = ( *)
(*   struct *)
(*     type z = t *)
(*     type t = z *)
(*     let equal = equal *)
(*     let hash = hash *)
(*   end *)
(* ) *)

module Ordered_couple = 
struct
  type t = transition * int
  let compare (t1, i1) (t2, i2) = 
    let hc = Hstring.compare (t1.tr_info.tr_name) (t2.tr_info.tr_name) in
    if hc = 0 then
      Pervasives.compare i1 i2
    else hc
end  

module MA = Map.Make (Ordered_couple)
  
module SA = Set.Make (Ordered_couple)

module HI = Hashtbl.Make (
  struct
    type t = int
    let equal = (=)
    let hash x = x
  end
)

let hic = HI.create 19

let hic_add id t id' b =
  let map = try HI.find hic id 
    with Not_found -> MA.empty
  in
  let map' = MA.add (t, id') b map in
  HI.replace hic id map' 

let hif = HI.create 19

  

(* module HVB : Hashtbl.S with type key = HTVertice.t = Hashtbl.Make (HTVertice) *)

(* SIGNATURE FOR MAP *)

let compare v1 v2 = Pervasives.compare v1.id v2.id

let all_permutations = Variable.all_permutations

(** IC3 Printing and saving function *)

(* PRINT FUNCTIONS *)

let get_id v =
  match v.id with
    | 1 -> "top"
    | 2 -> "root"
    | i -> string_of_int i

let print_ucnf fmt g =
  List.iter (
    fun c -> Format.eprintf "\t\tForall %a, @[%a@] AND\n@." 
      Variable.print_vars c.Cube.vars 
      (SAtom.print_sep "||") c.Cube.litterals
  ) g

let print_lbl_ucnf fmt g =
  List.iter (
    fun c -> Format.fprintf fmt "%a \\n" 
      (* Variable.print_vars c.Cube.vars  *)
      (SAtom.print_sep "||") c.Cube.litterals
  ) g

let print_iucnf fmt g =
  List.iter (
    fun c -> Format.eprintf "\t\t@[%a@] AND\n@." 
      (SAtom.print_sep "||") c.Cube.litterals
  ) g

let print_ednf fmt b = 
  List.iter (
    fun c -> Format.eprintf "\t\t@[%a@] OR\n@." 
      (* Variable.print_vars c.Cube.vars *)
      (SAtom.print_sep "&&") c.Cube.litterals
  ) b

let print_vednf fmt v =
  List.iter (
    fun c -> Format.eprintf "\t\t@[%a@] OR\n@." 
      (* Variable.print_vars c.Cube.vars  *)
      (SAtom.print_sep "&&") c.Cube.litterals
  ) v.bad
    
let print_iednf fmt b = 
  List.iter (
    fun c -> Format.eprintf "\t\t@[%a@] OR\n@." 
      (SAtom.print_sep "&&") c.Cube.litterals
  ) b

let print_id fmt v = Format.eprintf "%s" (get_id v)
let save_id fmt v = Format.fprintf fmt "%s" (get_id v)

let print_vertice fmt v = 
  Format.eprintf 
    "Vertice (%a)\n\tWorld : \n%a\n\tBad : \n%a\n\tParents :"
    print_id v print_ucnf v.world print_ednf v.bad;
  List.iter (
    fun (vp, tr) -> 
      Format.eprintf "\n\t\t(%a, %a)@." 
	print_id vp Hstring.print tr.tr_info.tr_name
  ) v.subsume;
  Format.eprintf "\n\tBad from : %a " print_id v;
  List.iter (
    fun (tr, v) -> Format.eprintf "--%a--> %a "
      Hstring.print tr.tr_info.tr_name
      print_id v
  ) v.bad_from;
  Format.eprintf "\n\tWorld from : ";
  let rec wf = function
    | [] -> ()
    | [e] -> Format.eprintf "not %a.bad" print_id e
    | hd::tl -> Format.eprintf "not %a.bad && " print_id hd;
      wf tl
  in wf v.world_from
  
let rec save_ucnf_tex fmt g =
  match g with 
    | [] -> Format.fprintf fmt "\n"
    | [c] -> 
      (match c.Cube.vars with
        | [] ->
          Format.fprintf fmt "\t\t\t\t\t\\bullet & & $\\parbox[t]{0.7\\textwidth}{$%a$}$ &\n" 
	    (SAtom.print_sep_tex "\\vee") c.Cube.litterals
        | l -> 
          Format.fprintf fmt 
            "\t\t\t\t\t\\bullet & \\forall %a & $\\parbox[t]{0.7\\textwidth}{$%a$}$ &\n" 
	    Variable.print_vars_tex l 
	    (SAtom.print_sep_tex "\\vee") c.Cube.litterals
      )
    | c::g -> 
      (match c.Cube.vars with
        | [] ->
          Format.fprintf fmt 
            "\t\t\t\t\t\\bullet &  & $\\parbox[t]{0.7\\textwidth}{$%a$}$ & \\bigwedge \\\\\n" 
	    (SAtom.print_sep_tex "\\vee") c.Cube.litterals
        | l -> 
          Format.fprintf fmt 
            "\t\t\t\t\t\\bullet & \\forall %a & $\\parbox[t]{0.7\\textwidth}{$%a$}$ & \\bigwedge \\\\\n" 
	    Variable.print_vars_tex l 
	    (SAtom.print_sep_tex "\\vee") c.Cube.litterals
      );
      save_ucnf_tex fmt g

let rec save_ednf_tex fmt b = 
  match b with
    | [] -> Format.fprintf fmt "\n"
    | [c] -> 
      Format.fprintf fmt "\t\t\t\t\t\\bullet & $\\parbox[t]{0.7\\textwidth}{$%a$}$ & \n" 
  	(SAtom.print_sep_tex "\\wedge") c.Cube.litterals
    | c::b -> 
      Format.fprintf fmt 
        "\t\t\t\t\t\\bullet & $\\parbox[t]{0.7\\textwidth}{$%a$}$ & \\bigvee\\\\" 
 	(SAtom.print_sep_tex "\\wedge") c.Cube.litterals;
      save_ednf_tex fmt b
        
let save_vertice fmt v =
  Format.fprintf fmt
    "\n\t\\paragraph{}\\textbf{Vertice (%a)}\n\
          \t\t\\\\[0.2cm]\\textcolor{green}{World} : \n\
               \t\t\t\\(\\left\\{\n\
                    \t\t\t\t\\begin{array}{l l l r} \n\
                      %a\
                    \t\t\t\t\\end{array}\n\
                  \t\t\t\\right.\\)\n\
          \t\t\\\\[0.2cm]\\textcolor{red}{Bad} : \n\
               \t\t\t\\(\\left\\{\n\
                    \t\t\t\t\\begin{array}{l l r} \n\
                      %a\
                    \t\t\t\t\\end{array}\n\
                  \t\t\t\t\\right.\\)" 
    save_id v save_ucnf_tex v.world save_ednf_tex v.bad;
  (match v.creation with
    | None -> ()
    | Some (v1, t, v2) -> 
      Format.fprintf fmt 
        "\n\t\t\\\\[0.2cm]Creation : \\(%a \\xrightarrow{%a} %a\\)"
        save_id v1 (Hstring.print_tex false) t.tr_info.tr_name
        save_id v2
  );
  Format.fprintf fmt "\n\t\t\\\\[0.2cm]Parents :\n\
                        \t\t\t\\(\\left\\{\n\
                        \t\t\t\t\\begin{array}{l l}";
  List.iter (
    fun (vp, tr) -> 
      Format.fprintf fmt "\n\t\t\t\t\t%a & \\xrightarrow{%a}\\\\"
	save_id vp (Hstring.print_tex false) tr.tr_info.tr_name
  ) v.subsume;
  Format.fprintf fmt "\n\t\t\t\t\\end{array}\n\
                        \t\t\t\\right.\\)\n";
  Format.fprintf fmt "\n\t\t\\noindent Bad from : %a \\("
    save_id v;
  List.iter (
    fun (tr, v) -> 
      Format.fprintf fmt "\n\t\t\t\t\\xrightarrow{%a} %a "
	(Hstring.print_tex false) tr.tr_info.tr_name save_id v
  ) v.bad_from;
  Format.fprintf fmt "\\)";
  if v.id > 2 then (
    Format.fprintf fmt "\n\t\t\\\\[0.2cm]\\noindent World from : \\(";
    let rec wf = function
      | [] -> Format.fprintf fmt "\\)"
      | [e] -> Format.fprintf fmt "\\neg Unsafe\\)"
      | hd::tl -> Format.fprintf fmt "\\neg Bad_{%a} \\wedge "
        save_id hd;
        wf tl
    in wf v.world_from)

(* Returns true if the bad part of the node is 
   not empty *)
let is_bad v = 
  List.exists (
    fun c -> 
      not (SAtom.is_empty c.Cube.litterals)
  ) v.bad



(* Interface with dot *)

let lbl_node v =
  match Options.dot_level with
    | 0 -> get_id v
    | 1 -> Format.asprintf "%s(%d)" (get_id v) 
      (List.length v.world)
    | _ -> Format.asprintf "%s\\n%a" (get_id v) print_lbl_ucnf v.world

let lbl_node_ext v =
  match Options.extra_level with
    | 0 -> get_id v
    | 1 -> Format.asprintf "%s(%d)" (get_id v) 
      (List.length v.world)
    | _ -> Format.asprintf "%s\\n%a" (get_id v) print_lbl_ucnf v.world
      
let add_node_dot v = 
  let c = if is_bad v then "red" else "green" in
  Dot.new_node_ic3 ~color:c (get_id v) (lbl_node v)

let add_node_extra v =
  Dot.new_node_ext_ic3 (get_id v) (lbl_node_ext v)

let add_node_step v c = 
  Dot.new_node_step_ic3 ~color:c (get_id v) (lbl_node v)

let add_relation_extra v =
  try
    let b = List.hd v.world_from in
    Dot.new_relation_ext_ic3 (get_id v) (get_id b)
  with
    | Failure _ -> ()

let add_subsume_dot v =
  let subsume = List.map (fun (v, t) -> (get_id v, t)) v.subsume in
  Dot.new_relations_ic3 (get_id v) subsume ~color:"blue"

let add_subsume_step v =
  let subsume = List.map (fun (v, t) -> (get_id v, t)) v.subsume in
  Dot.new_relations_step_ic3 (get_id v) subsume ~color:"blue"
    
let add_relation_dot ?color:(c="black") v v' tr =
  Dot.new_relation_ic3 ~color:c ~style:"dashed" 
    (get_id v) (get_id v') tr

let add_relation_step ?color:(c="black") ?style:(s="solid") v v' tr =
  Dot.new_relation_step_ic3 ~color:c ~style:s (get_id v) (get_id v') tr

let add_relation_dot_count v v' tr =
  Dot.new_relation_ic3_count ~style:"dotted" 
    (get_id v) (get_id v') tr !step


(* CREATION FUNCTIONS *)

    
let create_world l = 
  let b = List.fold_left (
    fun acc (vl, sa) -> 
      let c = Cube.create vl sa in
      c::acc
  ) [] l in
  List.rev b

let create_bad = create_world
  
let create =
  let cpt = ref 0 in
  fun ?is_root:(ir=false) ?creation w ac k b ->
    incr cpt;
    let subs, pred = 
      match creation with
        | None -> [], None
        | Some (v1, t, v2) -> 
          let p = if v2.id = 1 then None else Some v2 in
          [v1, t], p
    in
    (* assert (!cpt < 3 || List.length ac < 2); *)
    (* List.iter ( *)
    (*   fun c -> Format.eprintf "[Added Clause] %a@." Cube.print c *)
    (* ) ac; *)
    let v =
      {
	world = w;
        added_clause = ac;
	bad = b;
	subsume = subs;
        predecessor = pred;
        successor = None;
        creation = creation;
        bad_from = [];
        world_from = [];
	id = !cpt;
        kind = k;
        is_root = ir;
      } in
    v

      

(* MODIFICATION FUNCTIONS *)


(* let update_bad v nb = v.bad <- List.fold_left *)
(*   (fun acc b -> b@acc) v.bad nb *)
  
let update_bad_from v1 tr v2 =
  v1.bad_from <- (tr, v2)::v2.bad_from

let update_world_from v1 v2 =
  v1.world_from <- v2::v2.world_from

let delete_parent v (vp, tr) =
  let l = v.subsume in
  let trn = tr.tr_info.tr_name in
  let rec delete (acc, del) = function
    | [] -> (acc, false)
    | (vp', tr')::l when 
	equal vp vp' 
	&& Hstring.equal tr'.tr_info.tr_name trn
	-> (List.rev_append acc l, true)
    | c :: l -> delete ((c::acc), del) l
  in 
  let (nl, del) = delete ([], false) l in
  v.subsume <- nl;
  del

let add_parent v (vp, tr) =
  if List.exists (
    fun (vp', tr') -> 
      equal vp vp' 
      && Hstring.equal tr'.tr_info.tr_name tr.tr_info.tr_name
  ) v.subsume 
  then ()
  else (
    v.subsume <- ((vp, tr)::v.subsume);
  (* if Options.dot_level >= 1 then *)
  (* 	( *)
  (* 	  incr step; *)
  (* 	  add_relation_dot_count v vp tr *)
  (* 	) *)
  )
    



(* ACCESS FUNCTIONS *)

let get_subsume v = v.subsume

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

let instantiate_cube args acc cube = 
  let substs = all_permutations cube.Cube.vars args in
  (* List.iter ( *)
  (*   fun subst -> *)
  (*     List.iter ( *)
  (*       fun (v1, v2) -> Format.eprintf "(%a, %a) " *)
  (*         Variable.print v1 Variable.print v2 *)
  (*     ) subst; *)
  (*     Format.eprintf "@." *)
  (* ) substs; *)

  List.rev (List.fold_left (
    fun i_cube sub ->
      let sc = Cube.subst sub cube in
      sc :: i_cube
  ) acc substs)
    
let instantiate_cube_list args world = 
  List.rev (List.fold_left (instantiate_cube args) [] world)

let instantiate_guard args tr = 
  let ti = tr.tr_info in
  let substs = all_permutations ti.tr_args args in
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

let assume_distinct nvars = 
  fun () -> Prover.assume_distinct nvars

let assume_cube n f =
  fun () ->
    if debug_smt && verbose > 1 then
      Format.eprintf "[A&R] Assuming@.";
    if debug_smt then Format.eprintf "[smt] Cube@.";
    Prover.assume_formula_satom n f
      
let assume_cnf n gl =
  fun () -> 
    if debug_smt then Format.eprintf "[smt] cnf@.";
    List.iter (
      fun g -> 
	if not (SAtom.is_empty g.Cube.litterals)
	then
	  Prover.assume_clause n g.Cube.array
    ) gl

let assume_udnfs n udnfs = 
  fun () ->
    if debug_smt then Format.eprintf "[smt] Udnf@.";
    List.iter (
      fun udnf ->
        Prover.assume_dnf n udnf
    ) udnfs
      
let clear_and_restore fl =
  fun () ->
    Prover.clear_system ();
    List.iter (fun f -> f ()) fl
      
      
(* let restore s = Solver.restore_state s *)
      
      
(* Format.eprintf "[A&R] Restoring@."; *)

(* let assume_neg_and_restore s f = *)
(*   Prover.assume_neg_formula_satom 0 f; *)
(*   Solver.restore_state s *)

(* IC3 BASE FUNCTIONS *)

let equivalent c1 c2 =
  if Cube.compare_cubes c1 c2 <> 0 then false
  else 
    begin
      let sigmas = Instantiation.relevant ~of_cube:c1 ~to_cube:c2 in
      let sa1 = c1.Cube.litterals in
      let sa2 = c2.Cube.litterals in
      List.exists (
        fun sigma ->
          let sa1 = SAtom.subst sigma sa1 in
          SAtom.equal sa1 sa2
      ) sigmas
    end
      

let is_subformula c1 c2 =
  if Cube.compare_cubes c1 c2 > 0 then false
  else 
    begin
      let sigmas = Instantiation.relevant ~of_cube:c1 ~to_cube:c2 in
      let sa1 = c1.Cube.litterals in
      let sa2 = c2.Cube.litterals in
      List.exists (
        fun sigma ->
          let sa1 = SAtom.subst sigma sa1 in
          SAtom.subset sa1 sa2
      ) sigmas
    end        



let negate_cube c = 
  let l = c.Cube.litterals in
  let l = SAtom.fold (
    fun a l -> SAtom.add (Atom.neg a) l
  ) l SAtom.empty in
  let v = c.Cube.vars in
  let c = Cube.create v l in
  let subst = Variable.build_subst v Variable.procs in
  Cube.subst subst c

    
(* Given a formula, returns the formula with all the
   litterals negated *)
let negate_litterals = List.map negate_cube


let find_pre tr acc bad =
  let ncube = Node.create bad in
  let (nl, nl') = Pre.pre_image [tr] ncube in
  let nc = List.map (fun n -> n.cube) nl in
  let nc' = List.map (fun n -> n.cube) nl' in
  nc@nc'@acc


let easy_imply_by_trans cnf dnf ({tr_info = ti} as tr)=
  
  let ndnf = List.fold_left (find_pre tr) [] dnf in
  
  let ncnf = negate_litterals cnf in
  (* if verbose > 2 then *)
  (*   ( *)
  let res =
    List.for_all (
      fun cube ->
        List.exists2 (
          fun nclause clause -> 
            is_subformula nclause cube
            || Cube.inconsistent_clause_cube clause cube
        ) ncnf cnf
    ) ndnf in
  if res then (
    incr Stats.cpt_easy_true;
    EUnsat
  )
  else (
    incr Stats.cpt_easy_false;
    EDontKnow)

      
let find_inst fun_dist fun_wo n1 n2 inst_f2 l =
  let rec find_inst = function 
    | [] -> None
    | ({ Ic3_forward.i_reqs = reqs;
         i_udnfs = udnfs;
    	 i_actions = actions;
    	 i_touched_terms = terms;
         i_args = iargs;
       } as it)::tl ->
      try
        let n1 = n1 + 1 in
	(* Format.eprintf "[find_inst] fun_wo@."; *)
        (* We check if we can execute this transition *)
    	(* if debug && verbose > 1 then *)
    	(*   Format.eprintf "[ImplyTrans] Check guard@."; *)
    	let fun_gu = assume_cube n1 reqs in
	(* Format.eprintf "[find_inst] fun_gu@."; *)
        let fun_ugu = assume_udnfs n1 udnfs in

	(* if debug && verbose > 1 then *)
    	(*   ( *)
	(*     Format.eprintf  *)
        (*       "[ImplyTrans] Apply action@."; *)
    	(*     Format.eprintf  *)
        (*       "[ACTIONS] %a@." (SAtom.print_sep "&&") actions; *)
	(*   ); *)
	let fun_ac = assume_cube n1 actions in
	(* Format.eprintf "[find_inst] fun_ac@."; *)
	let fun_cr = clear_and_restore 
          [fun_dist; fun_wo; fun_gu; fun_ugu; fun_ac] in
	
        let pinst_f2 =
	  List.map (
	    fun c ->
    	      let vars = c.Cube.vars in
    	      let litt = c.Cube.litterals in
	      let plitt = Ic3_forward.prime_match_satom litt terms in
	      Cube.create vars plitt
	  ) inst_f2 in
        
        (* Format.eprintf "[PINSTF2] %a@." print_iednf pinst_f2; *)
    	(* World updated assumed *)
    	(* if debug && verbose > 1 then *)
    	(*   Format.eprintf "[ImplyTrans] Assuming action@."; *)
    	(* Every time we try a new world 2, we restore
    	   the system to world 1 plus the guard plus the action *)
    	
	let res = ref None in

        let rec f =
	  function
	    | [], [] -> raise Not_found
	    | (pif2::tl, pif2'::tl') ->
	      (
		try
    		  if debug_smt && verbose > 0 then
    	    	    Format.eprintf "[Find_Inst] Clear@.";
                  (*   Format.eprintf "[ImplyTrans] Assume %a@." *)
	    	  (*     SAtom.print pif2.Cube.litterals; *)

    		  (* Format.eprintf "[find_inst] begin acrs@."; *)
                  fun_cr ();
                  if debug_smt && verbose > 0 then
    	    	    Format.eprintf "[Find_Inst] Cube@.";
                  assume_cube n2 pif2.Cube.litterals ();
                  Prover.run ();

    		  if debug_smt && verbose > 0 then
    	    	    Format.eprintf "[Find_Inst] Res : SSAT\n@.";
    		  res := Some (pif2', it);
		  raise Exit
    		with Smt.Unsat _ ->
    		  if debug_smt && verbose > 0 then
    	    	    Format.eprintf "[Find_Inst] Res : SUNS*AT\n@.";
    		  f (tl, tl')
	      );
              
	    | _ -> assert false
	in 
	let r = 
          try f (pinst_f2, inst_f2) 
	  with Exit -> !res
        in
        r
      (* We go back to world not updated for the next
    	 transition *)
      with
	| Smt.Unsat _ | Not_found -> 
          find_inst tl
  in 
  let r = find_inst l in
  r

type res = 
  | HSat of Cube.t
  | HUnsat



(* If the result is TRUE then f1 and tr imply f2.
   When we want to know if world1 and tr imply world2,
   FALSE means YES.
   When we want to know if world1 and tr imply bad2,
   TRUE means YES.*)
let hard_imply_by_trans (cnf, n1) (dnf, n2) ({tr_info = ti} as tr) = 
  Format.eprintf "[HIT] Smt call@.";
  (* We want to check v1 and tr and not v2
     if it is unsat, then v1 and tr imply v2
     else, v1 and tr can not lead to v2 *)
  (* if verbose > 0 then *)
  (*   ( *)
  (*     Format.eprintf "[CNF] %a@." print_ucnf cnf; *)
  (*     Format.eprintf "[DNF] %a@." print_ednf dnf; *)
  (*   ); *)
  (* let ndnf = List.fold_left (find_pre tr) [] dnf in *)
  
  (* try *)
  (*   let res =  *)
  (*     List.find ( *)
  (*       fun cube -> *)
          
  let n_cnf = max_args cnf in
  let n_dnf = max_args dnf in
  let n_tr = List.length ti.tr_args in
  let n_args =
    if n_cnf - n_dnf - n_tr > 0 then n_cnf - n_dnf
    else n_tr
  in
  let args = get_procs n_args n_dnf in
  (* if debug && verbose > 2 then  *)
  (*   Format.printf "Card : %d@." (List.length args); *)
  
  let inst_dnf = instantiate_cube_list args dnf in
  
  (* Format.eprintf "[CNF] %a@." print_ucnf cnf; *)
  (* Format.eprintf "[DNF] %a@." print_ednf dnf; *)
  (* Format.eprintf "[Partition Impossible]\n%a@." print_ednf imp; *)
  (* Format.eprintf "[Partition Possible]\n%a@." print_ednf pos; *)
  (* Format.eprintf "[Result] %s@." (if res then "true" else "false"); *)
  
  let inst_cnf = instantiate_cube_list args cnf in
  let inst_upd = Ic3_forward.instantiate_transitions args args [tr] in
  let fun_dist = assume_distinct (List.length args) in
  let fun_world = assume_cnf n1 inst_cnf in
  let res = find_inst fun_dist fun_world n1 n2 inst_dnf inst_upd in
  match res with
    | Some (b, it) -> HSat b
    | None -> HUnsat


(* Given a transition and a node, 
   Answers SAT if we can take the transition,
   Answers UNSAT otherwise *)
let pickable =
  let empty = [Cube.create [] SAtom.empty] in
  fun v tr -> 
    match easy_imply_by_trans v.world empty tr with
      | EUnsat -> false
      | EDontKnow -> match hard_imply_by_trans
          (v.world, v.id) (empty, v.id + 1) tr with
          | HUnsat -> false
          | HSat _ -> true
          
      

(* Given a list of transitions and a node,
   returns the list of the pickable transitions *)
let expand v = List.filter (pickable v)

(* Returns true if the world part of the node is
   trivially true *)
(* COULD BE BUGGY *)
let is_true v =
  List.for_all (
    fun sa -> 
      Cube.size sa = 0 
      || SAtom.exists (
	fun a -> Atom.compare a Atom.True = 0
      ) sa.Cube.litterals
  ) v.world


(* Given v1 and v2 returns true if v1 => v2
   returns false otherwise *)
let implies v1 v2 = 
  (* if ic3_level = 0 then *)
    (* if v1.id >= v2.id then true *)
    (* else false *)
  true
  (* else  *)
  (*   begin *)
      (* let w1 = v1.world in *)
      (*   let w2 = v2.world in *)
      (*   let nw2 = negate_litterals w2 in *)
      (*   let n1 = v1.id in *)
      (*   let n2 = v2.id in *)
      (*   let n_w1 = max_args w1 in *)
      (*   let n_w2 = max_args nw2 in *)
      (*   let n_args = max n_w1 n_w2 in *)
      (*   let args = get_procs n_args 0 in *)
      (* (\* Format.eprintf "[IMPLIES] w1 : %d, w2 : %d, args : %d@." *\) *)
      (* (\* n_w1 n_w2 n_args; *\) *)
      (*   let inst_w1 = instantiate_cube_list args w1 in *)
      (*   let inst_nw2 = instantiate_cube_list args nw2 in *)
      
      (*   if debug && verbose > 1 then *)
      (*     Format.eprintf "[Implies] Assuming world@."; *)
      (*   let fun_dist = assume_distinct n_args in *)
      (*   let fun_world = assume_cnf n1 inst_w1 in *)
      (*   let fun_cr = clear_and_restore [fun_dist; fun_world] in *)
      
      (*   if debug && verbose > 1 then *)
      (*     Format.eprintf "[Implies] Assuming and restoring@."; *)
      (*   let sat = List.exists ( *)
      (*     fun e ->  *)
      (*       try  *)
      (*         if debug && verbose > 1 then *)
      (*           Format.eprintf "[Implies] Begin@."; *)
      (*         fun_cr (); *)
      (*   	  assume_cube n2 e.Cube.litterals (); *)
      (*         Prover.run (); *)
      (*         if debug && verbose > 1 then *)
      (*           Format.eprintf "[Implies] SAT@."; *)
      (*         true  *)
      (*       with  *)
      (*         | Smt.Unsat _ ->     *)
      (*           if debug && verbose > 1 then *)
      (*             Format.eprintf "[Implies] UNSAT@."; *)
      (*           false *)
      (*   ) inst_nw2 in *)
      (*   not sat *)
    (*   failwith "IMPLIES TODO" *)
    (* end *)
      
module T = Util.TimerIc3
module IT = Util.TimerITIc3

let imply_by_trans v1 tr vs v2 =
  let nvs = negate_litterals vs.added_clause in 
  let rec f v =
    (* Format.eprintf "[TestingFS] %a --%a--> %a " *)
    (*   print_id v Hstring.print tr.tr_info.tr_name print_id vs; *)
    (* Format.eprintf  *)
    (*   "[TestingFS] With (%a).added_clause = %a\nand (%a).nvs = %a@." *)
    (*   print_id v print_ucnf v.added_clause *)
    (*   print_id vs print_ednf nvs; *)
    if profiling then T.start ();
    let res = easy_imply_by_trans v.added_clause nvs tr in
    if profiling then T.pause ();
    match res with
      | EUnsat ->
        (* Format.eprintf " EUnsat @."; *)
        true
      | EDontKnow ->
        (* Format.eprintf " EDontKnow @."; *)
        (* false *)
        match v.predecessor with
          | None ->
            Format.eprintf "[TestingFS] Back to (%a).world@." print_id v1;
            
            let res = hard_imply_by_trans (v1.world, v1.id) (nvs, vs.id) tr
            in (
              match res with
                | HUnsat -> Format.eprintf " HUNSAT @.";true
                | HSat _ -> Format.eprintf " HSAT @.";false
            )
          | Some vp ->
            (if debug then
                try
                  let map = HI.find hic vp.id in
                  try
                    let bind = MA.find (tr, vs.id) map in
                    let bind = if bind then "true" else "false" in
                    Format.eprintf
                      "[Predecessor] Predecessor %a --%a--> %a %s@."
                      print_id vp Hstring.print tr.tr_info.tr_name print_id vs bind
                  with Not_found -> Format.eprintf
                    "[Predecessor] No bind from %a with (%a, %a)@."
                    print_id vp Hstring.print tr.tr_info.tr_name print_id vs
                with Not_found -> Format.eprintf
                  "[Predecessor] No map found for %a@." print_id vp);
            f vp
  in f v1
        
        
(* Tries to find a node in the graph which subsume
   the current node.
   Raise Not_found *)
let find_subsuming_vertice v1 v2 tr candidates =
  (* if verbose > 0 then *)
  ( let n = List.length candidates in
    if n = 0 then
      Format.eprintf "[Subsume] %a %a No subsumption@." 
        print_id v1 print_id v2
  );
  (* else Format.eprintf "[Subsume] %a %a [%d]@."  *)
  (* print_id v1 print_id v2 n; *)
  List.find (
    fun vs ->
      (* if verbose > 0 then *)
      Format.eprintf "[Subsumption] (%a) and (%a) to (%a) ?@." 
	print_id v1 Hstring.print tr.tr_info.tr_name print_id vs;
      let res =
	(is_true v2 || implies vs v2) 
	&& (
          (* if debug then *)
          (* HI.iter ( *)
          (*   fun id1 map -> *)
          (*     Format.eprintf "[HV] %d" id1; *)
          (*     MA.iter ( *)
          (*       fun (t, id2) b -> *)
          (*         let res = if b then "true" else "false" in *)
          (*         Format.eprintf "\t--%a--> %d (%s)@." Hstring.print t.tr_info.tr_name id2 res *)
          (*     ) map *)
          (* ) hic; *)
	  (* May need an adaptation when ic3_level = 1 *)
          let res = imply_by_trans v1 tr vs v2 in
          res
        (* find_sub_base v1 tr vs *)
        )    
      in 
      (* if not res then *)
      hic_add v1.id tr vs.id res;
      if res
      then (
        Format.eprintf
          "[Subsumed] (%a) is subsumed by (%a) by (%a)@." 
          print_id v2 print_id vs Hstring.print tr.tr_info.tr_name
      )
      else (
        Format.eprintf 
          "[Not subsumed] (%a) is not subsumed by (%a) by (%a)@."
          print_id v2 print_id vs Hstring.print tr.tr_info.tr_name
      );
      res
  ) candidates

let imply_by_trans_easy v1 tr vs v2 =
  let nvs = negate_litterals vs.added_clause in 
  let rec f v =
    (* Format.eprintf "[TestingFS] %a --%a--> %a " *)
    (*   print_id v Hstring.print tr.tr_info.tr_name print_id vs; *)
    (* Format.eprintf  *)
    (*   "[TestingFS] With (%a).added_clause = %a\nand (%a).nvs = %a@." *)
    (*   print_id v print_ucnf v.added_clause *)
    (*   print_id vs print_ednf nvs; *)
    if profiling then T.start ();
    let res = easy_imply_by_trans  v.added_clause nvs tr in
    if profiling then T.pause ();
    match res with
      | EUnsat ->
        (* Format.eprintf " EUnsat @."; *)
        true
      | EDontKnow ->
        (* Format.eprintf " EDontKnow @."; *)
        (* false *)
        match v.predecessor with
          | None -> false
          | Some vp ->
            (if debug then
                try
                  let map = HI.find hic vp.id in
                  try
                    let bind = MA.find (tr, vs.id) map in
                    let bind = if bind then "true" else "false" in
                    Format.eprintf
                      "[Predecessor] Predecessor %a --%a--> %a %s@."
                      print_id vp Hstring.print tr.tr_info.tr_name print_id vs bind
                  with Not_found -> Format.eprintf
                    "[Predecessor] No bind from %a with (%a, %a)@."
                    print_id vp Hstring.print tr.tr_info.tr_name print_id vs
                with Not_found -> Format.eprintf
                  "[Predecessor] No map found for %a@." print_id vp);
            f vp
  in f v1

let imply_by_trans_hard v1 tr vs v2 =
  let nvs = negate_litterals vs.added_clause in 
  let res = hard_imply_by_trans (v1.world, v1.id) (nvs, vs.id) tr
  in 
  match res with
    | HUnsat -> true
    | HSat _ -> false

(* Tries to find a node in the graph which subsume
   the current node.
   Raise Not_found *)
let find_subsuming_vertice_switch v1 v2 tr candidates =
  (* if verbose > 0 then *)
  ( let n = List.length candidates in
    if n = 0 then
      Format.eprintf "[Subsume] %a %a No subsumption@." 
        print_id v1 print_id v2
  );
  (* else Format.eprintf "[Subsume] %a %a [%d]@."  *)
  (* print_id v1 print_id v2 n; *)
  try 
    List.find (
      fun vs ->
      (* if verbose > 0 then *)
        Format.eprintf "[Subsumption Easy] (%a) and (%a) to (%a) ?@." 
	  print_id v1 Hstring.print tr.tr_info.tr_name print_id vs;
        let res =
	  (is_true v2 || implies vs v2) 
	  && (imply_by_trans_easy v1 tr vs v2)    
        in 
      (* if not res then *)
        hic_add v1.id tr vs.id res;
        if res
        then (
          Format.eprintf
            "[Subsumed] (%a) is subsumed by (%a) by (%a)@." 
            print_id v2 print_id vs Hstring.print tr.tr_info.tr_name
        )
        else (
          Format.eprintf 
            "[Not subsumed] (%a) is not subsumed by (%a) by (%a)@."
            print_id v2 print_id vs Hstring.print tr.tr_info.tr_name
        );
        res
    ) candidates
  with Not_found ->
    List.find (
      fun vs ->
      (* if verbose > 0 then *)
        Format.eprintf "[Subsumption Easy] (%a) and (%a) to (%a) ?@." 
	  print_id v1 Hstring.print tr.tr_info.tr_name print_id vs;
        let res =
	  (is_true v2 || implies vs v2) 
	  && (imply_by_trans_hard v1 tr vs v2)    
        in 
      (* if not res then *)
        hic_add v1.id tr vs.id res;
        if res
        then (
          Format.eprintf
            "[Subsumed] (%a) is subsumed by (%a) by (%a)@." 
            print_id v2 print_id vs Hstring.print tr.tr_info.tr_name
        )
        else (
          Format.eprintf 
            "[Not subsumed] (%a) is not subsumed by (%a) by (%a)@."
            print_id v2 print_id vs Hstring.print tr.tr_info.tr_name
        );
        res
    ) candidates


let generalize_cube c =
  let v = c.Cube.vars in
  let subst = Variable.build_subst v Variable.generals in
  Cube.subst subst c

let all_subsatom c =
  let litt = c.Cube.litterals in
  let rec all_rec acc = function
    | [] -> acc
    | x :: l -> 
      let r = all_rec acc l in
      (SAtom.singleton x, SAtom.remove x litt )::(
        (List.map (
          fun (s, s') ->
            let s = SAtom.add x s in
            let s' = SAtom.remove x s' in
            (s, s')
         ) r)@r)
  in
  let l = all_rec [] (SAtom.elements litt) in
  List.fast_sort (
    fun (l1,_) (l2,_) -> Pervasives.compare 
      (SAtom.cardinal l1) (SAtom.cardinal l2)
  ) l


let contains g b =
  List.exists (equivalent b) g 
    
(* try *)
(*   Prover.clear_system (); *)
(*   (\* Format.eprintf "\n[Test contains]World:@."; *\) *)
(*   let n_g = max_args g in *)
(*   let args = get_procs n_g 0 in *)
(*   let inst_g = instantiate_cube_list args g in *)
(*   assume_cnf n2 inst_g (); *)
(*   (\* Format.eprintf "[Test contains]%a@." print_ednf [b]; *\) *)
(*   assume_cube (n2+1) b.Cube.litterals (); *)
(*   Format.eprintf "[New extrapolant]\n%a@." print_ednf [b]; *)
(*   false *)
(* with Smt.Unsat _ -> true *)

let find_extra v1 v2 tr cube lextra =
  let subs = all_subsatom cube in
  if (* debug && *) verbose > 0 then
    Format.eprintf "[Extrapolation] Original cube : %a@."
      (SAtom.print_sep "&&") cube.Cube.litterals;
  let rec find_extra = function
    | [] -> assert false
    | [_, l] ->
      assert (SAtom.equal l SAtom.empty);
      if (* debug &&  *)verbose > 0 then
        Format.eprintf
          "[Extrapolation] We found no better bad@.";
      let gncube = generalize_cube (negate_cube cube) in
      (cube, (gncube, KOriginal))
    | (sub, l)::tl ->
      let csub = Cube.create_normal sub in
      if contains lextra csub then
        find_extra tl
      else
        begin
          let ncsub = negate_cube csub in
          if contains v2.world ncsub then find_extra tl
          else
            let res1 = easy_imply_by_trans v1.world [csub] tr in
            match res1 with
              | EUnsat ->
                if (* debug  && *) verbose > 0 then
                  Format.eprintf
                    "[ExtrapolationE] We found a better bad\n%a@."
                    Cube.print csub;
                let gnecsub = generalize_cube ncsub in
                (csub, (gnecsub, KExtrapolated))
              | EDontKnow ->
                (* let res2 = hard_imply_by_trans  *)
                (*   (v1.world, v1.id) ([csub], v2.id) tr in *)
                (* match res2 with *)
                (*   | HUnsat ->  *)
                (*     if (\* debug  && *\) verbose > 0 then *)
                (*       Format.eprintf *)
                (*         "[ExtrapolationE] We found a better bad\n%a@." *)
                (*         Cube.print csub; *)
                (*     let gnecsub = generalize_cube ncsub in *)
                (*     let acube = generalize_cube ( negate_cube ( *)
                (*       Cube.create_normal l)) in *)
                (*     (gnecsub, Extrapolated acube) *)
                find_extra tl
        end
  in 
  let (c, extra) = find_extra subs in
  (extra, c::lextra)

(* Given a formula, extrapolate it and then
   generalize and negate it *)
let extrapolate v1 v2 tr =
  (* let w2 = v2.world in *)
  let b2 = v2.bad in
  let nb2, _ = List.fold_left (
    fun (nb2, lextra) cube ->
      let res, lextra' =
        if ic3_level = 1 then find_extra v1 v2 tr cube lextra
        else 
          let ncube = negate_cube cube in
          let gncube = generalize_cube ncube in
          (gncube, KOriginal), [] in
      (res::nb2, lextra')
  ) ([], []) b2 in
  nb2
    
let compare_cubes = Cube.compare_cubes
  
let cube_implies c cl =
  try 
    let res = List.find (
      fun b -> 
        is_subformula b c
        || Cube.inconsistent_clause_cube (negate_cube b) c
    ) cl in
    (* Format.eprintf "[Cube_Implies] Yes : \n\t%a@." Cube.print res; *)
    Some res
  with Not_found -> 
    (* Format.eprintf "[Cube_Implies] No@."; *)
    None

(* let filter_consistent_bad_in_world w1 b2 = *)
(*   let nw1 = negate_litterals w1 in *)
(*   List.filter ( *)
(*     fun cube -> *)
(*       let v1 = cube.Cube.vars in *)
(*       List.for_all ( *)
(*         fun nclause ->  *)
(*           let v2 = nclause.Cube.vars in *)
(*           let sigmas = Variable.all_permutations v2 v1 in *)
(*           not (List.exists ( *)
(*             fun sigma -> *)
(*               let nclause = Cube.subst sigma nclause in *)
(*               let res = Cube.inconsistent_2 nclause cube in *)
(*               (\* Format.eprintf "[CI] C1 : %a\n C2: %a\n\t%s@." *\) *)
(*               (\*   Cube.print nclause Cube.print cube *\) *)
(*               (\*   (if res then "true" else "false"); *\) *)
(*               not res *)
(*           ) sigmas) *)
(*       ) nw1 *)
(*   ) b2      *)

let simplify_dnf w1 b2 dnf =
  let nw1 = negate_litterals w1 in
  let sdnf, _ = List.fold_left (
    fun (acc, count) cube ->
      let cig = cube_implies cube nw1 in
      match cig with 
        | Some c ->
          if debug && verbose > 0 then
            Format.eprintf 
              "[Simp negation] \n%a\n [is negated by] \n%a@."
              Cube.print cube Cube.print c;
          (acc, count)
        | None ->
          let cib = cube_implies cube b2 in
          match cib with
            | Some c ->
              if debug && verbose > 0 then
                Format.eprintf
                  "[Simp already bad]\n%a\n [was already in] \n%a@."
                  Cube.print cube Cube.print c;
              ((c, count)::acc, count + 1)
            (* (acc, count) *)
            | None -> 
              
              match Fixpoint.FixpointCubeList.check cube acc with
                | None -> ((cube, count)::acc, count + 1)
                | Some l -> (acc, count)
  ) ([], 1) dnf in
  fst (List.split sdnf)
    
let partition_l dim l =
  let rec f acc ll =
    match ll with 
      | hd::tl when (Cube.dim hd) = dim -> f (hd::acc) tl
      | _ -> acc, ll
  in f [] l

let select_procs l v1 v2 =
  (* Format.eprintf "[Select procs]\n%a@." print_ednf l; *)
  let rec s l =
    match l with
      | [] -> None
      | hd::tl ->
        let dim = Cube.dim hd in
        let less_proc, others = partition_l dim l in
        let nl = simplify_dnf v1.world v2.bad less_proc in
        match nl with
          | [] -> s others
          | _ -> Some nl
  in s l

let find_all_bads v1 v2 =
  if debug && verbose > 0 then
    Format.eprintf "[FindBads]%s, %s@." (get_id v1) (get_id v2);
  (* assert (v1.id > v2.id); *)
  (* let rec find acc v = *)
  (*   if v.id = v2.id then acc *)
  (*   else match v.predecessor with *)
  (*     | None -> v::acc *)
  (*     | Some r ->  *)
  (*       Format.eprintf "[FindBads] %s refines %s@." (get_id v) (get_id r); *)
  (*       find (v::acc) r *)
  (* in find [] v1 *)
  let rec find acc v =
    match v.successor with
      | None -> acc
      | Some r -> 
        if debug && verbose > 0 then
          Format.eprintf "[FindBads] %s is refined by %s@." (get_id v) (get_id r);
        find (v::acc) r
  in find [] v2
  
exception No_bad

let find_subsuming_vertice = 
  if ic3_switch then find_subsuming_vertice_switch
  else find_subsuming_vertice

(* Main function of IC3 *)
let refine v1 v2 tr candidates =
  try
    (* if verbose > 0 then *)
    Format.eprintf "[Subsumption] Is (%a) covered by transition %a ?@." 
      print_id v2 Hstring.print tr.tr_info.tr_name;
    let vs = find_subsuming_vertice v1 v2 tr candidates in
    (* Format.eprintf "[Covered] (%a) is covered by (%a) by %a@." *)
    (*   print_id v1 print_id vs Hstring.print tr.tr_info.tr_name; *)
    Covered vs
  with Not_found -> 
    (* if verbose > 0 then *)
    Format.eprintf "[Implication] (%a.world) and %a to (%a.bad) ?@."
      print_id v1 Hstring.print tr.tr_info.tr_name print_id v2;
    if profiling then IT.start ();
    let res =
      (* if v1.id = 2 then *)
      List.fold_left (
        fun acc cube ->
          let res = easy_imply_by_trans v1.world [cube] tr in
          match res with
            | EUnsat ->
               (* Format.eprintf " EUnsat@."; *)
              acc
            | EDontKnow ->
              Format.eprintf " EDontKnow@.";
              if ic3_smt then
                let res = hard_imply_by_trans
                  (v1.world, v1.id) ([cube], v2.id) tr in
                match res with
                  | HSat _ ->
                    cube :: acc
                  | HUnsat -> acc
              else cube::acc
      ) [] v2.bad
    (* else v2.bad *)
    in
    if profiling then IT.pause ();
    try
      match res with
        
      (* RES = No means world1 and tr don't imply bad2,
         we can now extrapolate world1 by adding not bad2. *)
      | [] -> raise No_bad

      (* RES = Yes b means world1 and tr imply bad2,
	 we then need to find a pre formula which leads to bad2 *)
          
      | bads ->
        if verbose > 0 then
          Format.eprintf
            "[BadToSubsumed] (%a.world) and %a imply (%a.bad) ?@."
	    print_id v1 Hstring.print tr.tr_info.tr_name
            print_id v2;
	if dot then add_relation_dot ~color:"red" v2 v1 tr;
        let pre_image = List.fold_left (
          fun acc bad -> find_pre tr acc bad
        ) [] v2.bad in
        let bads = find_all_bads v1 v2 in
        (* Format.eprintf "[Bads] "; *)
        (* List.iter ( *)
        (*   fun v -> Format.eprintf "%s " (get_id v) *)
        (* ) bads; *)
        (* Format.eprintf "@."; *)
        
        let pre_image =
          List.fold_left (
            fun acc cl ->
              List.fold_left (find_pre tr) acc cl.bad
          ) pre_image bads
        in
        let pre_image = List.fast_sort compare_cubes pre_image in
        if debug && verbose > 0 then
          Format.eprintf "[Pre images]\n%a@." print_ednf pre_image;
        let pre_image = select_procs pre_image v1 v2 in
        match pre_image with
          | None -> 
            assert false;
          | Some p ->    
            (* Format.eprintf "[Pre_image] %a@." Cube.print p; *)
            v1.bad <- p;
            Bad_Parent (v1.id, p)
    with No_bad ->
      try
        if verbose > 0 then
          Format.eprintf
            "[BadToSubsumed] (%a.world) and %a imply (%a.bad) ?@."
	    print_id v1 Hstring.print tr.tr_info.tr_name
            print_id v2;
        match v2.successor, v1.kind with 
          | Some v, KOriginal -> 
            Format.eprintf
              "[Subsumed no bad] (%a) is already subsumed by (%a) by (%a)@." 
              print_id v2 print_id v Hstring.print tr.tr_info.tr_name;
            Covered v
          | Some v, KExtrapolated ->
            (* let nw = negate_litterals v1.world in *)
            (* Format.eprintf  *)
            (*   "[Not World] %a@." print_ednf nw; *)
            (* let res = easy_imply_by_trans v1.world nw tr in *)
            (* (match res with *)
            (*   | EUnsat -> Format.eprintf "[EUnsat] (%a).world and %a imply %a@." *)
            (*     print_id v1 Hstring.print tr.tr_info.tr_name print_ednf nw; *)
            (*     Covered v *)
            (*   | EDontKnow -> Format.eprintf "[EDontKnow] (%a).world and %a do not imply %a@." *)
            (*     print_id v1 Hstring.print tr.tr_info.tr_name print_ednf nw; *)
            (*     (match hard_imply_by_trans (v1.world, v1.id) (nw, v1.id + 1) tr with *)
            (*       | HUnsat -> Format.eprintf "[HUnsat] (%a).world and %a imply %a@." *)
            (*         print_id v1 Hstring.print tr.tr_info.tr_name print_ednf nw; *)
            (*         Covered v *)
            (*       | HSat _ -> Format.eprintf "[HSat] (%a).world and %a do not imply %a@." *)
            (*         print_id v1 Hstring.print tr.tr_info.tr_name print_ednf nw; *)
            (*         raise Exit) *)
            (* ) *)
            raise Exit
          | None, _ -> raise Exit

      with Exit ->
        Format.eprintf "[Extrapolation] (%a.world) and %a do not imply (%a.bad)@."
          print_id v1 Hstring.print tr.tr_info.tr_name print_id v2;
        let extra_bad2 =
          extrapolate v1 v2 tr in
        if debug && verbose > 1 then (
          Format.eprintf "[Bad] %a@." print_ednf v2.bad;
          (* Format.eprintf "[EBAD2] %a@." print_ucnf extra_bad2; *)
        );
        (* assert (List.length extra_bad2 = 1); *)
        let (extra_bad2, kind) = 
          let kind = ref KOriginal in
          let eb = List.map (
            fun (eb', k) ->
              (match k with
                | KExtrapolated -> kind := k
                | _ -> ());
              eb'
          ) extra_bad2 in
          eb, !kind in
        let nw =
          if is_true v2
          then extra_bad2
          else v2.world @ extra_bad2
        in
        let nv = create ~creation:(v1, tr, v2) nw extra_bad2
          kind [] in
        v2.successor <- Some nv;
        Format.eprintf 
          "[Extrapolation] We extrapolate (%a.bad) = eb and \
                 create a new node with (%a.world) && eb -> (%a)@."
          print_id v2 print_id v2 print_id nv;
        if debug && verbose > 0 
        then Format.eprintf "NV : %a@." print_vertice nv;
        if dot then add_relation_dot ~color:"green" v2 nv tr;
        Extrapolated nv
