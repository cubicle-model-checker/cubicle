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
      
let tmp_vis = ref []

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

let print_lbl_ednf fmt g =
  List.iter (
    fun c -> Format.fprintf fmt "%a \\n" 
      (* Variable.print_vars c.Cube.vars  *)
      (SAtom.print_sep "||") c.Cube.litterals
  ) g

let print_lbl_ucnf fmt g =
  List.iter (
    fun c -> Format.fprintf fmt "%a \\n" 
      (* Variable.print_vars c.Cube.vars  *)
      (SAtom.print_sep "&&") c.Cube.litterals
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
    | _ -> Format.asprintf "%s\\n%a" (get_id v) 
      (* (if is_bad v then (print_lbl_ednf Format.str_formatter v.bad) *)
      (*  else ( *)print_lbl_ucnf v.world

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
    incr Stats.cpt_nodes;
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

let add_successor v vs =
  v.successor <- Some vs

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
    if debug_smt && ic3_verbose > 1 then
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
      (* let sigmas = Variable.all_permutations c1.Cube.vars c2.Cube.vars in *)
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
      (* let sigmas = Variable.all_permutations c1.Cube.vars c2.Cube.vars in *)
      let sa1 = c1.Cube.litterals in
      let sa2 = c2.Cube.litterals in
      List.exists (
        fun sigma ->
          let sa1 = SAtom.subst sigma sa1 in
          SAtom.subset sa1 sa2
      ) sigmas
    end        

let negate_cube_same_vars c =
  let l = c.Cube.litterals in
  let l = SAtom.fold (
    fun a l -> SAtom.add (Atom.neg a) l
  ) l SAtom.empty in
  let v = c.Cube.vars in
  Cube.create v l
    
let negate_cube_procs c = 
  let c = negate_cube_same_vars c in
  let v = c.Cube.vars in
  let subst = Variable.build_subst v Variable.procs in
  Cube.subst subst c

let generalize_cube c =
  let v = c.Cube.vars in
  let subst = Variable.build_subst v Variable.generals in
  Cube.subst subst c

let general_to_procs c =
  let v = c.Cube.vars in
  let subst = Variable.build_subst v Variable.procs in
  Cube.subst subst c

    
(* Given a formula, returns the formula with all the
   litterals negated *)
let negate_litterals = List.map negate_cube_procs


let find_pre tr acc bad =
  let ncube = Node.create bad in
  let (nl, nl') = Pre.pre_image [tr] ncube in
  let nc = List.map (fun n -> n.cube) nl in
  let nc' = List.map (fun n -> n.cube) nl' in
  nc@nc'@acc

module ET = Util.TimerEasyIc3


let easy_imply_by_trans cnf dnf ({tr_info = ti} as tr)=
  ET.start ();
  let ndnf = List.fold_left (find_pre tr) [] dnf in
  
  let ncnf = negate_litterals cnf in
  (* if ic3_verbose > 2 then *)
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
  ET.pause ();
  if res then (
    incr Stats.cpt_easy_true;
    EUnsat
  )
  else (
    incr Stats.cpt_easy_false;
    EDontKnow)

type res = 
  | HSat (* of Cube.t *)
  | HUnsat


let delete_subsumed f =
  (* f is supposedly sorted *)
  List.fold_left (
    fun acc c ->
      match Fixpoint.FixpointCubeList.check c acc with
        | None -> c::acc
        | Some l -> acc
  ) [] f

exception Fixpoint

let check_fixpoint cube visited nvars =
  Prover.assume_goal_cube_ic3 0 nvars cube;
  let c_array = cube.Cube.array in
  let cubes, _ = 
    List.fold_left
      (fun (cubes, count) vis_cube ->
        let vis_cube = general_to_procs vis_cube in
        let nvis_cube = negate_cube_same_vars vis_cube in
        let d = Instantiation.relevant ~of_cube:nvis_cube ~to_cube:cube in
        (* let d = Variable.all_permutations vis_cube.Cube.vars cube.Cube.vars in *)
        List.fold_left
	  (fun (cubes, count) ss ->
            let vis_renamed =
              ArrayAtom.apply_subst ss vis_cube.Cube.array in
            ((vis_cube, vis_renamed)::cubes, count+1)
	  ) (cubes, count) d
      ) ([], 1) visited
  in
  let cubes =
    List.fast_sort
      (fun (c1, a1) (c2, a2) -> 
        ArrayAtom.compare_nb_common c_array a1 a2)
      cubes
  in
  List.iteri (fun id (vn, ar_renamed) -> 
    Prover.assume_clause id ar_renamed
  ) cubes

let compare_cubes = Cube.compare_cubes
  
let hit_calls = ref 0
let extra_hit_calls = ref 0

module HT = Util.TimerHardIc3

(* If the result is TRUE then f1 and tr imply f2.
   When we want to know if world1 and tr imply world2,
   FALSE means YES.
   When we want to know if world1 and tr imply bad2,
   TRUE means YES.*)
let hard_imply_by_trans (cnf, n1) (dnf, n2) ({tr_info = ti} as tr) = 
  if profiling then HT.start ();
  incr hit_calls;
  (* Format.eprintf "[HIT] Smt call@."; *)
  (* We want to check v1 and tr and not v2
     if it is unsat, then v1 and tr imply v2
     else, v1 and tr can not lead to v2 *)
  if debug && ic3_verbose > 2 then
    (
      Format.eprintf "[CNF] %a@." print_ucnf cnf;
      Format.eprintf "[DNF] %a@." print_ednf dnf;
    );
  
      
  let n_cnf = max_args cnf in
  let n_dnf = max_args dnf in
  let n_tr = List.length ti.tr_args in
  let n_args =
    if n_cnf - n_dnf - n_tr > 0 then n_cnf
    else n_tr + n_dnf
  in

  let ndnf = List.fold_left (find_pre tr) [] dnf in
  let ndnf = List.fast_sort compare_cubes ndnf in
        
  (* let ndnf = delete_subsumed ndnf in *)

  let res =
    List.exists (
      fun cube ->
        try 
          check_fixpoint cube cnf n_args;
          true
        with
          | Exit -> false
          | Fixpoint -> true
          | Smt.Unsat _ -> false
    ) ndnf in
  HT.pause ();
  if res then HSat else HUnsat
  
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
          | HSat -> true
          
      

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
let implies v1 v2 = true
      

let imply_by_trans v1 tr vs v2 =
  let nvs = negate_litterals vs.added_clause in 
  let rec f v =
    (* Format.eprintf "[TestingFS] %a --%a--> %a " *)
    (*   print_id v Hstring.print tr.tr_info.tr_name print_id vs; *)
    (* Format.eprintf  *)
    (*   "[TestingFS] With (%a).added_clause = %a\nand (%a).nvs = %a@." *)
    (*   print_id v print_ucnf v.added_clause *)
    (*   print_id vs print_ednf nvs; *)
    let res = easy_imply_by_trans v.added_clause nvs tr in
    match res with
      | EUnsat ->
        (* Format.eprintf " EUnsat @."; *)
        true
      | EDontKnow ->
        (* Format.eprintf " EDontKnow @."; *)
        (* false *)
        match v.predecessor with
          | None ->
            if ic3_verbose > 1 then
              Format.eprintf "[TestingFS] Back to (%a).world@." 
                print_id v1;
            let res = hard_imply_by_trans 
              (v1.world, v1.id) (nvs, vs.id) tr
            in (
              match res with
                | HUnsat -> (* Format.eprintf " HUNSAT @."; *)true
                | HSat -> (* Format.eprintf " HSAT @."; *)false
            )
          | Some vp -> f vp
  in f v1
        
        
(* Tries to find a node in the graph which subsume
   the current node.
   Raise Not_found *)
let find_subsuming_vertice v1 v2 tr candidates =
  (* if ic3_verbose > 0 then *)
  if ic3_verbose > 0 then (
    let n = List.length candidates in
     if n = 0 then
       Format.eprintf "[Subsume] %a %a No subsumption@." 
         print_id v1 print_id v2
    );
  (* else Format.eprintf "[Subsume] %a %a [%d]@."  *)
  (* print_id v1 print_id v2 n; *)
  List.find (
    fun vs ->
      if ic3_verbose > 0 then
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
          imply_by_trans v1 tr vs v2
        )    
      in 
      (* if not res then *)
      hic_add v1.id tr vs.id res;
      if ic3_verbose > 0 then
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
    let res = easy_imply_by_trans v.added_clause nvs tr in
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
    | HSat -> false

(* Tries to find a node in the graph which subsume
   the current node.
   Raise Not_found *)
let find_subsuming_vertice_switch v1 v2 tr candidates =
  (* if ic3_verbose > 0 then *)
  if ic3_verbose > 0 then (
    let n = List.length candidates in
    if n = 0 then
      Format.eprintf "[Subsume] %a %a No subsumption@." 
        print_id v1 print_id v2
    );
  (* else Format.eprintf "[Subsume] %a %a [%d]@."  *)
  (* print_id v1 print_id v2 n; *)
  try 
    List.find (
      fun vs ->
        if ic3_verbose > 0 then
          Format.eprintf "[Subsumption Easy] (%a) and (%a) to (%a) ?@." 
	    print_id v1 Hstring.print tr.tr_info.tr_name print_id vs;
        let res =
	  (is_true v2 || implies vs v2) 
	  && (imply_by_trans_easy v1 tr vs v2)    
        in 
        hic_add v1.id tr vs.id res;
        if ic3_verbose > 0 then
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
        if ic3_verbose > 0 then
          Format.eprintf "[Subsumption Easy] (%a) and (%a) to (%a) ?@." 
	    print_id v1 Hstring.print tr.tr_info.tr_name print_id vs;
        let res =
	  (is_true v2 || implies vs v2) 
	  && (imply_by_trans_hard v1 tr vs v2)    
        in 
        hic_add v1.id tr vs.id res;
        if ic3_verbose > 0 then
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
      
let all_subsatom_recterm c =
  let litt = c.Cube.litterals in
  let rec all_rec acc = function
    | [] -> acc
    | x :: l ->
      let nacc = List.rev_map (
        fun a -> SAtom.add x a ) acc
      in
      let acc = List.rev_append nacc acc in
      all_rec acc l
  in
  let elts = SAtom.elements litt in
  let l = all_rec [SAtom.empty] elts in
  List.tl (List.fast_sort (
    fun sa1 sa2 -> Pervasives.compare 
      (SAtom.cardinal sa1) (SAtom.cardinal sa2)
  ) l)
    

let contains g b =
  List.exists (equivalent b) g 
    

let find_extra v1 v2 tr cube lextra =
  let subs = all_subsatom_recterm cube in
  if (* debug && *) ic3_verbose > 0 then
    Format.eprintf "[Extrapolation] Original cube : %a@."
      (SAtom.print_sep "&&") cube.Cube.litterals;
  let rec find_extra = function
    | [] -> assert false
    | [_] ->
      if (* debug &&  *)ic3_verbose > 0 then
        Format.eprintf
          "[Extrapolation] We found no better bad@.";
      let gncube = generalize_cube (negate_cube_same_vars cube) in
      (cube, (gncube, KOriginal))
    | sub::tl ->
      let csub = Cube.create_normal sub in
      if contains lextra csub then
        find_extra tl
      else
        begin
          let ncsub = negate_cube_procs csub in
          if  contains v2.world ncsub then find_extra tl
          else
            let res1 = easy_imply_by_trans v1.world [csub] tr in
            match res1 with
              | EUnsat ->
                if (* debug  && *) ic3_verbose > 0 then
                  Format.eprintf
                    "[ExtrapolationE] We found a better bad\n%a@."
                    Cube.print csub;
                let gnecsub = generalize_cube ncsub in
                (csub, (gnecsub, KExtrapolated))
              | EDontKnow -> 
                 incr extra_hit_calls;
                let res2 = hard_imply_by_trans
                  (v1.world, v1.id) ([csub], v2.id) tr in
                match res2 with
                  | HUnsat ->
                    if (* debug  && *) ic3_verbose > 0 then
                      Format.eprintf
                        "[ExtrapolationE] We found a better bad\n%a@."
                        Cube.print csub;
                    let gnecsub = generalize_cube ncsub in
                    (csub, (gnecsub, KExtrapolated))
                  | HSat ->find_extra tl
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
          let ncube = negate_cube_same_vars cube in
          let gncube = generalize_cube ncube in
          (gncube, KOriginal), [] in
      (res::nb2, lextra')
  ) ([], []) b2 in
  nb2
      
let cube_implies c cl =
  try 
    let res = List.find (
      fun b -> 
        is_subformula b c
        || Cube.inconsistent_clause_cube (negate_cube_procs b) c
    ) cl in
    Some res
  with Not_found -> None

let simplify_dnf w1 b2 dnf =
  let nw1 = negate_litterals w1 in
  let sdnf = List.fold_left (
    fun acc cube ->
      let cig = cube_implies cube nw1 in
      match cig with 
        | Some c -> acc
        | None ->
          let cib = cube_implies cube b2 in
          match cib with
            | Some c -> c::acc
            | None -> 
              match Fixpoint.FixpointCubeList.check cube acc with
                | None -> cube::acc
                | Some l -> acc
  ) [] dnf in
  sdnf
    
let partition_l dim l =
  let rec f acc ll =
    match ll with 
      | hd::tl when (Cube.dim hd) = dim -> f (hd::acc) tl
      | _ -> acc, ll
  in f [] l

let select_procs lb v1 v2 =
  
  (* Format.eprintf "[Select procs]\n%a@." print_ednf l; *)
  let rec s l =
    match l with
      | [] -> 
        Format.eprintf "V1 :\n %a\n\nV2 :\n %a\n\nl :\n %a@."
          print_ucnf v1.world print_ednf v2.bad 
          print_ednf lb;
        assert false
      | hd::tl ->
        let dim = Cube.dim hd in
        let less_proc, others = partition_l dim l in
        let nl = simplify_dnf v1.world v2.bad less_proc in
        match nl with
          | [] -> s others
          | _ -> Stats.cpt_process := max Stats.(!cpt_process) dim; nl
  in s lb

let find_all_bads v1 v2 =
  let rec find acc v =
    match v.successor with
      | None -> acc
      | Some r -> find (v::acc) r
  in find [] v2
  
exception No_bad

let find_subsuming_vertice = 
  if ic3_switch then find_subsuming_vertice_switch
  else find_subsuming_vertice

(* Main function of IC3 *)
  let refine v1 v2 tr cand =
    try
      if ic3_verbose > 0 then
        Format.eprintf "[Subsumption] Is (%a) covered by transition %a ?@." 
	  print_id v2 Hstring.print tr.tr_info.tr_name;
      let vs = find_subsuming_vertice v1 v2 tr cand in
      Covered vs
    with Not_found -> 
      if ic3_verbose > 0 then
        Format.eprintf "[Implication] (%a.good) and %a to (%a.bad) ?@."
	  print_id v1 Hstring.print tr.tr_info.tr_name print_id v2;
      let res = 
        List.fold_left (
          fun acc cube -> 
            let res = easy_imply_by_trans v1.world [cube] tr in
            match res with
              | EUnsat -> acc
              | EDontKnow ->
                let res = hard_imply_by_trans
                  (v1.world, v1.id) ([cube], v2.id) tr in
                match res with
                  | HSat ->
                    cube :: acc
                  | HUnsat -> acc
        ) [] v2.bad
      in
      match res with
          
	(* RES = [] means good1 and tr don't imply bad2,
           we can now extrapolate good1 by adding not bad2. *)
        | [] ->
          if ic3_verbose > 0 then
	    Format.eprintf "[Extrapolation] (%a.good) and %a do not imply (%a.bad)@." 
	      print_id v1 Hstring.print tr.tr_info.tr_name print_id v2;
	  let extra_bad2 = extrapolate v1 v2 tr in
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
          if ic3_verbose > 1 then (
	    Format.eprintf "[Bad] %a@." print_ednf v2.bad;
	    Format.eprintf "[EBAD2] %a@." print_ucnf extra_bad2;
	  );
          let nw =
            if is_true v2
            then extra_bad2
            else v2.world @ extra_bad2
          in
	  let nv = create ~creation:(v1, tr, v2) nw extra_bad2 kind [] in
          (* (try  *)
          (*    let v = List.find ( *)
          (*      fun v ->  *)
          (*        let w1 = v.world in *)
          (*        if List.length w1 <> List.length nw then false else *)
          (*          List.for_all2 ( *)
          (*            fun c1 c2 -> SAtom.equal c1.Cube.litterals c2.Cube.litterals *)
          (*          ) w1 nw *)
          (*    ) (!tmp_vis) in *)
          (*    Format.eprintf "nv(%a) equals previous v(%a) @." print_id nv print_id v; *)
          (*    Format.eprintf "\n%a\n\n%a\n@." print_vertice nv print_vertice v; *)
          (*    exit 1 *)
          (*  with Not_found -> tmp_vis := nv::(!tmp_vis) *)
          (* ); *)
	  if ic3_verbose > 0 then (
            Format.eprintf "[Extrapolation] We extrapolate \
                     (%a.bad) = eb and create a new node with \
                     (%a.good) && eb -> (%a)@."
	            print_id v2 print_id v2 print_id nv;
            Format.eprintf "NV : %a@." print_vertice nv;
          );
	  if dot then add_relation_dot ~color:"green" v2 nv tr;
	  Extrapolated nv

        (* RES = Yes b means good1 and tr imply bad2,
	   we then need to find a pre formula which leads to bad2 *)
            
        | bads ->
          if ic3_verbose > 0 then
            Format.eprintf 
              "[BadToParents] (%a.good) and %a imply (%a.bad)@." 
	      print_id v1 Hstring.print tr.tr_info.tr_name
              print_id v2;
	  if dot then add_relation_dot ~color:"red" v2 v1 tr;
      	  let pre_image = List.fold_left (
            fun acc bad -> find_pre tr acc bad
          ) [] bads in
          let pre_image = 
            match v2.successor with
              | None -> pre_image
              | Some vs ->
                let bads = find_all_bads v1 vs in
                List.fold_left (
                  fun acc cl -> 
                    List.fold_left (find_pre tr) acc cl.bad
                ) pre_image bads 
          in
          let pre_image = List.fast_sort compare_cubes pre_image in
          (* Format.eprintf "[Pre images]\n%a@." print_ednf pre_image; *)
          let pre_image = select_procs pre_image v1 v2 in
          if ic3_verbose > 0 then
          Format.eprintf
            "[BadCube] %a@." print_ednf pre_image;
          v1.bad <- pre_image;
          Bad_Parent (v1.id, pre_image)
