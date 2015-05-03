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

  val create :  ?c:(t * transition * t) -> ucnf -> ednf -> t
  val delete_parent : t -> t * transition -> bool
  val add_parent : t -> t * transition -> unit
  val get_parents : t -> (t * transition) list

  (* hashtype signature *)
  val hash : t -> int
  val equal : t -> t -> bool

  (* orderedtype signature *)
  val compare : t -> t -> int

  (* display functions *)
  val print_vertice : Format.formatter -> t -> unit
  val save_vertice : Format.formatter -> t -> unit
  val print_id : Format.formatter -> t -> unit
  val save_id : Format.formatter -> t -> unit
  val print_vednf : Format.formatter -> t -> unit

  (* Interface with dot *)
  val add_node_dot : t -> unit
  val add_node_step : t -> string -> unit
  val add_parents_dot : t -> unit
  val add_parents_step : t -> unit
    
  val add_relation_step : ?color:string -> ?style:string -> 
    t -> t -> transition -> unit

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
end
  
module Make ( Q : SigQ ) ( V : SigV ) = struct
    
  type v = V.t
  type q = V.t Q.t

  module G = Map.Make(V)
  module C = Map.Make(
    struct
      type t = transition
      let compare t1 t2 = Hstring.compare 
	t1.tr_info.tr_name
	t2.tr_info.tr_name
    end
  )
    
  exception Unsafe of V.t list G.t * V.t
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

  let save_graph rg =
    let bfile = Filename.chop_extension (Filename.basename file) in
    let file = bfile ^ ".latex" in
    let oc = open_out ("graphs/" ^ file) in
    let oc_fmt = Format.formatter_of_out_channel oc in
    Format.fprintf oc_fmt 
      "\\documentclass{article}\n\
       \\usepackage[utf8]{inputenc}\n\
       \\usepackage[usenames,dvipsnames,svgnames,table]{xcolor}\n\
       \\usepackage{amsmath}\n\
       \\usepackage{setspace}\n\
       \\onehalfspacing\n\
       \\begin{document}\n@.";
    G.iter (
      fun k e -> 
        Format.fprintf oc_fmt "%a\t\t\\\\[0.2cm]Extrapolation candidates:@." 
	  V.save_vertice k;
	(* List.iter ( *)
	(*   fun p ->  *)
        (*     Format.fprintf oc_fmt "\t\t(%a) @." V.save_id p; *)
	(* ) e; *)
	(* Format.fprintf oc_fmt "\n--------------@." *)
    ) rg;
    Format.fprintf oc_fmt "\\end{document}@.";
    close_out oc;
    (* match Sys.command ("pdflatex graphs/"^file) with *)
    (*   | 0 -> () *)
    (*   | _ -> *)
    (*     Format.eprintf  *)
    (*       "There was an error with dot. Make sure graphviz is installed." *)()


  let find_graph v g = 
    try G.find v g
    with Not_found -> []

  let add_extra_graph v r g =
    let l = find_graph v g in
    G.add v (r::l) g

  let update_dot rg =
    G.iter (
      fun v _ -> 
	V.add_node_dot v;
	V.add_parents_dot v;
    ) rg
      
  let update_step rg v1 =
    G.iter (
      fun v _ -> 
	let c = 
	  if V.is_bad v 
	  then if V.equal v1 v then "orange" else "red" 
	  else "chartreuse" in
	  V.add_node_step v c;
	(* V.print_step_parents e; *)
    ) rg

  type transitions = transition list

  type r = Bad | Expand | Cover | Extra

  type step = 
      { v : V.t;
	v' : V.t;
	tr : transition;
	delete : bool;
	from : r;
      }

  let update_steps s =
    List.iter (
      fun {v=v;
	   v'=v';
	   tr=tr;
	   delete=delete;
	   from=from;
	  } ->
	let c = match from with
	  | Bad -> "red"
	  | Expand -> "gray"
	  | Extra -> "green"
	  | Cover -> "blue"
	in 
	let s = match from with 
	  | Expand -> "bold"
	  | _ -> if delete then "dashed" else "solid"
	in
	V.add_relation_step ~color:c ~style:s v v' tr;
    ) s

  let search close_dot system = 
    (* top = (true, unsafe) *)
    (* Create the good formula of top, true *)
    let gtop = V.create_good [] in
    (* Create the bad formula of top, unsafe *)
    let cunsl = system.t_unsafe in
    let unsl = 
      List.fold_left (
	fun acc cuns -> 
	  let c = cuns.cube in 
	  (c.Cube.vars, c.Cube.litterals)::acc
      ) [] cunsl in
    let btop = V.create_bad unsl in
    (* Create top with gtop, btop and no parents *)
    let top = V.create gtop btop in
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
    let broot = V.create_bad [] in
    (* Create root with groot, broot and no parents *)
    let root = V.create groot broot in
    
    (* Working queue of nodes to expand and refine *)
    let todo = Q.create () in
    
    (* List of nodes for dot *)
    let steps = ref [] in
    let add_steps v v' from tr del =
      let s = {v = v;
	       v' = v';
	       tr = tr;
	       from = from;
	       delete = del;
	      } in
      steps := s::(!steps)
    in
    
    (* rushby graph *)
    let rgraph = G.add root [] (G.singleton top []) in

    let trans_cover = List.fold_left (
      fun acc tr ->
        C.add tr top acc
    ) C.empty system.t_trans in
    
    let rec refine v1 v2 tr rg tc =
      Format.eprintf 
	"\n*******[Refine]*******\t(%a) --%a--> (%a)\n@." 
	V.print_id v1 Hstring.print tr.tr_info.tr_name 
	V.print_id v2;
      (* In this case we are trying to execute a new transition
	 from v1 but v1 is already bad so must not be considered as
	 a parent node. *)
      if V.is_bad v1 then (
	Format.eprintf 
	  "We discard the treatment of this edge since (%a) is now bad@." 
          V.print_id v1;
	(rg, tc)
      )
      else if V.is_bad v2 then (
	if debug && verbose > 0 then print_graph rg;
	let pr = List.rev (find_graph v2 rg) in
	match V.refine v1 v2 tr pr with  

	  (* v1 and tr imply bad *)
	  | V.Bad_Parent -> 
	    (* If v1 is root, we can not refine *)
	    if V.equal v1 root then raise (Unsafe (rg, v1));
	    (* Else, we recursively call refine on all the parents *)
	    Format.eprintf "[New Bad] (%a).bad = %a@."
	      V.print_id v1 V.print_vednf v1;
	    if dot_step then add_steps v2 v1 Bad tr false;
	    List.fold_left (
	      fun (rg, tc) (vp, tr) -> 
		Format.eprintf "[BadParent] (%a) --%a--> (%a).bad@."
		  V.print_id vp Hstring.print tr.tr_info.tr_name 
		  V.print_id v1;
		if dot_step then add_steps vp v1 Bad tr true;
		refine vp v1 tr rg tc
	    ) (rg, tc) (V.get_parents v1)

	  (* The node vc covers v2 by tr *)
	  | V.Covered vc -> 
	    let del = V.delete_parent v2 (v1, tr) in
	    V.add_parent vc (v1, tr);
	    if dot_step then (
	      add_steps v1 vc Cover tr false;
	      if del then add_steps v1 v2 Cover tr true;
	    );
	    if debug && verbose > 1 then (
	      Format.eprintf "[Covered by] %a@." V.print_vertice vc;
	      Format.eprintf "[Forgotten] %a@." V.print_vertice v2;
	    );
            let tc = 
              if ic3_level = 0 then C.add tr vc tc
              else tc
            in
	    refine v1 vc tr rg tc

	  (* We created and extrapolant vn *)
	  | V.Extrapolated vn -> 
	    let del = V.delete_parent v2 (v1, tr) in
	    if debug && verbose > 1 then (
	      Format.eprintf 
                "[Extrapolated by] %a@." V.print_vertice vn;
	      Format.eprintf 
                "[Forgotten] %a@." V.print_vertice v2;
	    );
	    if dot_step then (
	      add_steps v1 vn Extra tr false;
	      if del then add_steps v1 v2 Extra tr true;
	    );
	    let rg' = add_extra_graph v2 vn (G.add vn [] rg) in
	    Q.push vn todo;
	    (rg', tc)
      )
      else (
	Format.eprintf "(%a) is safe, no backward refinement@." 
          V.print_id v2;
	(rg, tc)
      )
    in
    Q.push root todo;
    let transitions = system.t_trans in
    let rec expand rg tc =
      let v1 = 
	try Q.pop todo
	with Q.Empty -> raise (Safe rg)
      in
      Format.eprintf 
        "\n*******[Induct]*******\n \n%a\n\nTransitions :@." 
        V.print_vertice v1;
      let trans = V.expand v1 transitions in
      List.iter (
	fun tr -> 
	  Format.eprintf "\t%a@." Hstring.print tr.tr_info.tr_name
      ) trans;
      let rg, tc = List.fold_left (
	fun (rg, tc) tr ->
          let v2 = C.find tr tc in
          if dot_step then add_steps v1 v2 Expand tr false;
	  refine v1 top tr rg tc
      ) (rg, tc) trans
      in 
      let () = Sys.set_signal Sys.sigint 
	  (Sys.Signal_handle 
	     (fun _ ->
               print_graph rg;
               save_graph rg;
               Stats.print_report ~safe:false [] [];
	       if dot then (
                 update_dot rg;
	         Format.eprintf 
                   "\n\n@{<b>@{<fg_red>ABORT !@}@} Received SIGINT@.";
	         if dot_step then (
		   let close_step = Dot.open_step () in
		   update_step rg v1;
		   update_steps (List.rev !steps);
		   close_step ();
	         )
               );
               close_dot ();
	       exit 1
             )) 
      in
      if dot_step then (
	let close_step = Dot.open_step () in
	update_step rg v1;
	update_steps (List.rev !steps);
	steps := [];
	close_step ();
      );
      expand rg tc
    in
    try expand rgraph trans_cover
    with 
      | Safe rg -> 
	if dot then update_dot rg;
	print_graph rg;
        save_graph rg;
	Format.eprintf "Empty queue, Safe system@."; 
	RSafe
      | Unsafe (rg, v1) -> 
	if dot then update_dot rg;
	if dot_step then (
	  let close_step = Dot.open_step () in
	  update_step rg v1;
	  update_steps (List.rev !steps);
	  close_step ();
	);
	print_graph rg;
        save_graph rg;
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
        creation : (t * transition * t) option;
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
      fun c -> Format.eprintf "\t\tForall %a, %a AND\n@." 
	Variable.print_vars c.Cube.vars 
	(SAtom.print_sep "||") c.Cube.litterals
    ) g

  let print_iucnf fmt g =
    List.iter (
      fun c -> Format.eprintf "\t\t%a AND\n@." 
	(SAtom.print_sep "||") c.Cube.litterals
    ) g

  let print_ednf fmt b = 
    List.iter (
      fun c -> Format.eprintf "\n\t\t%a OR\n@." 
	(* Variable.print_vars c.Cube.vars  *)
	(SAtom.print_sep "&&") c.Cube.litterals
    ) b

  let print_vednf fmt v =
    List.iter (
      fun c -> Format.eprintf "\n\t\t%a@. OR\n@." 
	(* Variable.print_vars c.Cube.vars  *)
	(SAtom.print_sep "&&") c.Cube.litterals
    ) v.bad

  let print_iednf fmt b = 
    List.iter (
      fun c -> Format.eprintf "\t\t%a OR\n@." 
	(SAtom.print_sep "&&") c.Cube.litterals
    ) b
      
  let get_id v =
    match v.id with
      | 1 -> "top"
      | 2 -> "root"
      | i -> string_of_int i


  let print_id fmt v = Format.eprintf "%s" (get_id v)
  let save_id fmt v = Format.fprintf fmt "%s" (get_id v)

  let print_vertice fmt v = 
    Format.eprintf 
      "Vertice (%a)\n\tGood : \n%a\n\tBad : \n%a\n\tParents :"
      print_id v print_ucnf v.good print_ednf v.bad;
    List.iter (
      fun (vp, tr) -> 
	Format.eprintf "\n\t\t(%a, %a)@." 
	  print_id vp Hstring.print tr.tr_info.tr_name
    ) v.parents 

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
          \t\t\\\\[0.2cm]\\textcolor{green}{Good} : \n\
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
      save_id v save_ucnf_tex v.good save_ednf_tex v.bad;
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
    ) v.parents;
    Format.fprintf fmt "\n\t\t\t\t\\end{array}\n\
                        \t\t\t\\right.\\)\n"




  (* Interface with dot *)

  let lbl_node v =
    match Options.dot_level with
      | 0 -> get_id v
      | _ -> Format.asprintf "%s(%d, %d)@." (get_id v) 
	(List.length v.good) (List.length v.bad)
	     
	
  let add_node_dot v = 
    Dot.new_node_ic3 (get_id v) (lbl_node v)

  let add_node_step v c = 
    Dot.new_node_step_ic3 ~color:c (get_id v) (lbl_node v)

  let add_parents_dot v =
    let parents = List.map (fun (v, t) -> (get_id v, t)) v.parents in
    Dot.new_relations_ic3 (get_id v) parents ~color:"blue"

  let add_parents_step v =
    let parents = List.map (fun (v, t) -> (get_id v, t)) v.parents in
    Dot.new_relations_step_ic3 (get_id v) parents ~color:"blue"
      
  let add_relation_dot ?color:(c="black") v v' tr =
    Dot.new_relation_ic3 ~color:c ~style:"dashed" 
      (get_id v) (get_id v') tr

  let add_relation_step ?color:(c="black") ?style:(s="solid") v v' tr =
    Dot.new_relation_step_ic3 ~color:c ~style:s (get_id v) (get_id v') tr

  let add_relation_dot_count v v' tr =
    Dot.new_relation_ic3_count ~style:"dotted" 
      (get_id v) (get_id v') tr !step


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
    fun ?c g b ->
      incr cpt;
      let p = 
        match c with
          | None -> []
          | Some (v1, t, _) -> [v1, t]
      in
      let v =
	{
	  good = g;
	  bad = b;
	  parents = p;
          creation = c;
	  id = !cpt;
	} in
      v

	

  (* MODIFICATION FUNCTIONS *)


  let update_bad v nb = v.bad <- List.fold_left
    (fun acc b -> b@acc) v.bad nb
    
  let delete_parent v (vp, tr) =
    let l = v.parents in
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
    v.parents <- nl;
    del

  let add_parent v (vp, tr) =
    if List.exists (
      fun (vp', tr') -> 
	equal vp vp' 
	&& Hstring.equal tr'.tr_info.tr_name tr.tr_info.tr_name
    ) v.parents 
    then ()
    else (
      v.parents <- ((vp, tr)::v.parents);
      (* if Options.dot_level >= 1 then *)
      (* 	( *)
      (* 	  incr step; *)
      (* 	  add_relation_dot_count v vp tr *)
      (* 	) *)
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

  let assume_distinct nvars = 
    fun () -> Prover.assume_distinct nvars

  let assume_cube n f =
    fun () ->
      if debug && verbose > 1 then
        Format.eprintf "[A&R] Assuming@.";
      Prover.assume_formula_satom n f
 
  let assume_cnf n gl =
    fun () -> 
      List.iter (
	fun g -> 
	  if not (SAtom.is_empty g.Cube.litterals)
	  then
	    Prover.assume_clause n g.Cube.array
      ) gl

  let assume_udnfs n udnfs = 
    fun () ->
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
	
  (* Given a transition and a node, 
     Answers SAT if we can take the transition,
     Answers UNSAT otherwise *)
  let pickable v tr = 
    if debug && verbose > 0 then
      Format.eprintf "\ncheck the transition : %a\n@." 
        Hstring.print tr.tr_info.tr_name;

    let good = v.good in
    
    let n = v.id in

    let n_arg_go = max_args good in
    let n_arg_tr = nb_args tr in
    let args = get_procs n_arg_go n_arg_tr in

    let inst_goods = instantiate_cube_list args good in
    let inst_tr = Forward.instantiate_transitions args args [tr] in
    
    if debug && verbose > 1 then
      Format.eprintf "[Pickable] Assuming good@.";
    let fun_dist = assume_distinct (List.length args) in
    let fun_good = assume_cnf n inst_goods in
    let fun_cr = clear_and_restore [fun_dist; fun_good] in
        
    if debug && verbose > 1 then
      Format.eprintf "[Pickable] Assuming and restoring@.";
    List.exists (
      fun 
        {
          Forward.i_reqs = reqs;
          i_udnfs = udnfs;
        } -> 
	  try 
	    if debug && verbose > 1 then
	      Format.eprintf "[Pickable] Begin@.";
            (* Format.eprintf "[%a]%a@." Hstring.print tr.tr_info.tr_name *)
            (*   (SAtom.print_sep "&&") reqs; *)
            (* List.iter ( *)
            (*   fun lsa -> *)
            (*     Format.eprintf "[udnf]@."; *)
            (*     List.iter ( *)
            (*       fun sa -> Format.eprintf "\t%a@." (SAtom.print_sep "&&") sa; *)
            (*     Format.eprintf "@.";) lsa *)
            (* ) udnfs; *)
            fun_cr ();
            assume_cube n reqs ();
            if debug && verbose > 1 then
	      Format.eprintf "[Pickable] guard SAT@.";
            assume_udnfs (n+1) udnfs ();
            if debug && verbose > 1 then
              Format.eprintf "[Pickable] uguard SAT@.";
            true
	  with 
	    | Smt.Unsat _ ->    
	      if debug && verbose > 1 then
	        Format.eprintf "[Pickable] UNSAT@.";
	      false
    ) inst_tr

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

  let negate_cube c = 
    let l = c.Cube.litterals in
    let l = SAtom.fold (
      fun a l -> SAtom.add (Atom.neg a) l
    ) l SAtom.empty in
    Cube.create c.Cube.vars l
      
  (* Given a formula, returns the formula with all the
     litterals negated *)
  let negate_litterals = List.map negate_cube

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
    (* Format.eprintf "[IMPLIES] g1 : %d, g2 : %d, args : %d@." *)
      (* n_g1 n_g2 n_args; *)
    let inst_g1 = instantiate_cube_list args g1 in
    let inst_ng2 = instantiate_cube_list args ng2 in
    
    if debug && verbose > 1 then
      Format.eprintf "[Implies] Assuming good@.";
    let fun_dist = assume_distinct n_args in
    let fun_good = assume_cnf n1 inst_g1 in
    let fun_cr = clear_and_restore [fun_dist; fun_good] in
    
    if debug && verbose > 1 then
      Format.eprintf "[Implies] Assuming and restoring@.";
    let sat = List.exists (
      fun e -> 
	try 
	  if debug && verbose > 1 then
	    Format.eprintf "[Implies] Begin@.";
          fun_cr ();
    	  assume_cube n2 e.Cube.litterals ();
	  if debug && verbose > 1 then
	    Format.eprintf "[Implies] SAT@.";
	  true 
	with 
	  | Smt.Unsat _ ->    
	    if debug && verbose > 1 then
	      Format.eprintf "[Implies] UNSAT@.";
	    false
    ) inst_ng2 in
    not sat

  module T = Util.TimerIc3
  module IT = Util.TimerITIc3

  let find_inst fun_dist fun_go n1 n2 inst_f2 l =
    let rec find_inst = function 
      | [] -> None
      | { Forward.i_reqs = reqs;
          i_udnfs = udnfs;
    	  i_actions = actions;
    	  i_touched_terms = terms; }::tl ->
	try
          let n1 = n1 + 1 in
	  (* Format.eprintf "[find_inst] fun_go@."; *)
          (* We check if we can execute this transition *)
    	  if debug && verbose > 1 then
    	    Format.eprintf "[ImplyTrans] Check guard@.";
    	  let fun_gu = assume_cube n1 reqs in
	  (* Format.eprintf "[find_inst] fun_gu@."; *)
          let fun_ugu = assume_udnfs n1 udnfs in

	  if debug && verbose > 1 then
    	    (
	      Format.eprintf 
                "[ImplyTrans] Apply action@.";
    	      Format.eprintf 
                "[ACTIONS] %a@." (SAtom.print_sep "&&") actions;
	    );
	  let fun_ac = assume_cube n1 actions in
	  (* Format.eprintf "[find_inst] fun_ac@."; *)
	  
	  let fun_cr = clear_and_restore [fun_dist; fun_go; fun_gu; fun_ugu; fun_ac] in
	  
          let pinst_f2 =
	    List.map (
	      fun c ->
    		let vars = c.Cube.vars in
    		let litt = c.Cube.litterals in
		let plitt = Forward.prime_match_satom litt terms in
		Cube.create vars plitt
	    ) inst_f2 in
    
          (* Format.eprintf "[PINSTF2] %a@." print_iednf pinst_f2; *)
    	  (* Good updated assumed *)
    	  if debug && verbose > 1 then
    	    Format.eprintf "[ImplyTrans] Assuming action@.";
    	  (* Every time we try a new good 2, we restore
    	     the system to good 1 plus the guard plus the action *)
    	  
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

    		    (* Format.eprintf "[find_inst] begin acrs@."; *)
                    fun_cr ();
                    
                    assume_cube n2 pif2.Cube.litterals ();

    		    if debug && verbose > 1 then
    	    	      Format.eprintf "[ImplyTrans] Res : SAT@.";
    		    res := Some pif2';
		    raise Exit
    		  with Smt.Unsat _ ->
    		    if debug && verbose > 1 then
    	    	      Format.eprintf "[ImplyTrans] Res : UNSAT@.";
    		    f (tl, tl')
		);
                
	      | _ -> assert false
	  in 
	  let r = 
            try f (pinst_f2, inst_f2) 
	    with Exit -> !res
          in
          r
	(* We go back to good not updated for the next
    	   transition *)
	with
	  | Smt.Unsat _ | Not_found -> 
            find_inst tl
    in 
    let r = find_inst l in
    r
    
  type res = 
    | Yes of Cube.t 
    | No of ((unit -> unit) * (unit -> unit) * Forward.inst_trans list) 

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
    (* Format.eprintf "[IMPLIESTRANS] f1 : %d, f2 : %d, upd : %d@." *)
      (* (List.length inst_f1) (List.length inst_f2) (List.length inst_upd); *)
    
    
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
	  Term.Set.iter (
            Format.eprintf "%a " Term.print
          ) i.Forward.i_touched_terms;
	  Format.eprintf "\n@.";
      ) inst_upd;
    );  
    (* Good not updated *)
    if debug && verbose > 1 then
      Format.eprintf "\n[ImplyTrans] Assuming good@.";
    let fun_dist = assume_distinct (List.length args) in
    let fun_good = assume_cnf n1 inst_f1 in
    if profiling then 
      IT.start ();
    let time = IT.get () in
    let res = find_inst fun_dist fun_good n1 n2 inst_f2 inst_upd in
    if profiling then (
      IT.pause ();
      Format.eprintf "[ITimer] %f@." (IT.get () -. time);
    );
    match res with
      | Some b -> Yes b
      | None -> No (fun_dist, fun_good, inst_upd)


  (* Tries to find a node in the graph which subsume
     the current node.
     Raise Not_found *)
  let find_subsuming_vertice v1 v2 tr g =
    let n = List.length g in
    if n = 0 then
      Format.eprintf "[Subsume] %a %a No subsumption@." 
	print_id v1 print_id v2;
    (* else Format.eprintf "[Subsume] %a %a [%d]@."  *)
    (* print_id v1 print_id v2 n; *)
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
	      | No _ -> true
	      | Yes _ -> false
	  )
	in 
	if res
	then
	  Format.eprintf 
            "[Subsumed] (%a) is subsumed by (%a) by (%a)@." 
	    print_id v1 print_id vs Hstring.print tr.tr_info.tr_name
	else 
	  Format.eprintf 
            "[Not subsumed] (%a) is not subsumed by (%a) by (%a)@."
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

  let all_subsatom c =
    let rec all_rec acc = function
      | [] -> acc
      | x :: l -> 
        let r = all_rec acc l in
        (SAtom.singleton x)::(
          (List.map (fun s -> SAtom.add x s) r)@r)
    in
    let l = all_rec [] (SAtom.elements c.Cube.litterals) in
    List.fast_sort (
      fun l1 l2 -> Pervasives.compare 
        (SAtom.cardinal l1) (SAtom.cardinal l2)
    ) l


  let contains g b n2 =
    try
      Prover.clear_system ();
      Format.eprintf "\n[Test contains]Good:@.";
      let n_g = max_args g in
      let args = get_procs n_g 0 in
      let inst_g = instantiate_cube_list args g in
      assume_cnf n2 inst_g ();
      Format.eprintf "[Test contains]%a@." print_ednf [b];
      assume_cube (n2+1) b.Cube.litterals ();
      Format.eprintf "[New extrapolant]\n%a@." print_ednf [b];
      false
    with Smt.Unsat _ -> true


  (* Given a formula, extrapolate it and then
     generalize and negate it *)
  let extrapolate v2 fun_dist fun_go n1 n2 inst_upd =
    let b2 = v2.bad in
    Format.eprintf "[b2] %a@." print_ednf b2;
    let eb2 = 
      if ic3_level = 1 then
        match b2 with
          | [c] -> 
            let subs = all_subsatom c in
            let rec find_extra = function
              | [] -> assert false
              | [_] -> 
                Format.eprintf 
                  "[Extrapolation] We found no better bad@.";
                b2
              | sub::tl ->
                begin
                  let csub = Cube.create_normal sub in
                  let res = find_inst fun_dist fun_go 
                    n1 n2 [csub] inst_upd in
                  match res with 
                    | None -> 
                      let g2 = v2.good in
                      if contains g2 csub n2 then
                        find_extra tl
                      else [csub]
                    | Some _ -> find_extra tl
                end
            in
            find_extra subs
          | _ -> b2
      else b2 in
    let nb2 = negate_litterals eb2 in
    let nb2 = generalize_litterals nb2 in
    nb2

  (* Main function of IC3 *)
  let refine v1 v2 tr cand =
    try
      (* Format.eprintf "Candidates %a :@." print_id v2; *)
      (* List.iter ( *)
      (*   fun vc -> Format.eprintf "\t%a@." print_id vc *)
      (* ) cand; *)
      Format.eprintf "[Subsumption] Is (%a) covered by transition %a ?@." 
	print_id v2 Hstring.print tr.tr_info.tr_name;
      (* Format.eprintf "[Resume] %a\n%a@." *)
      (* 	print_vertice v1 print_vertice v2; *)
      let vs = find_subsuming_vertice v1 v2 tr cand in
      (* Format.eprintf "[Covered] (%a) is covered by (%a) by %a@." *)
      (*   print_id v1 print_id vs Hstring.print tr.tr_info.tr_name; *)
      Covered vs
    with Not_found -> 
      Format.eprintf "[Implication] (%a.good) and %a to (%a.bad) ?@."
	print_id v1 Hstring.print tr.tr_info.tr_name print_id v2;
      let res = imply_by_trans (v1.good, v1.id) (v2.bad, v2.id) tr in
      
      (* RES = Yes b means good1 and tr imply bad2,
	 we then need to find a pre formula which leads to bad2 *)
      match res with
	| Yes bad ->
	  Format.eprintf "[BadToParents] (%a.good) and %a imply (%a.bad)@." 
	    print_id v1 Hstring.print tr.tr_info.tr_name print_id v2;
	  if dot then add_relation_dot ~color:"red" v2 v1 tr;
	  Format.eprintf 
            "[BadToParents] We update (%a.bad) with bad = %a\n\t\tand refine to his parents@."
	    print_id v1 Cube.print bad;
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

	(* RES = No _ means good1 and tr don't imply bad2,
	   we can now extrapolate good1 by adding not bad2. *)
	| No (fun_dist, fun_go, inst_upd) ->
	  Format.eprintf "[Extrapolation] (%a.good) and %a do not imply (%a.bad)@." 
	    print_id v1 Hstring.print tr.tr_info.tr_name print_id v2;
	  let extra_bad2 = 
            extrapolate v2 fun_dist fun_go v1.id v2.id inst_upd in
	  if debug && verbose > 1 then (
	    Format.eprintf "[Bad] %a@." print_ednf v2.bad;
	    Format.eprintf "[EBAD2] %a@." print_ucnf extra_bad2;
	  );
	  let ng = 
	    if v2.id = 1 
	    then extra_bad2 
	    else v2.good @ extra_bad2 
	  in
	  let nv = create ~c:(v1, tr, v2) ng [] in
	  Format.eprintf "[Extrapolation] We extrapolate (%a.bad) = eb and create a new node with (%a.good) && eb -> (%a)@."
	    print_id v2 print_id v2 print_id nv;
	  Format.eprintf "NV : %a@." print_vertice nv;
	  if dot then add_relation_dot ~color:"green" v2 nv tr;
	  Extrapolated nv

end

module RG = Make(Queue)(Vertice)
