open Options
open Types
open Ast

module Solver = Smt.Make(Options)

type result =
  | RSafe
  | RUnsafe

module type SigQ = sig

  type 'a t

  exception Empty

  val create : unit -> 'a t
  val push : 'a -> 'a t -> unit
  val pop : 'a t -> 'a
end
  
let select_strat =
  (match Options.ic3_mode with
    | "bfs" -> (module Queue : SigQ)
    | "dfs" -> (module Stack)
    | _ -> assert false
  )

module Q : SigQ = (val (select_strat))

module V = Vertice  


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
    fun k e -> Format.eprintf "%a\n\tExtrapolation candidates: " 
      V.print_vertice k;
      List.iter (
	fun p -> Format.eprintf "%a " V.print_id p;
      ) e;
      Format.eprintf "\n--------------@."
  ) g;
  Format.eprintf "[ENDGRAPH]@."   

let save_graph rg =
  if ic3_pdf then
    let bfile = Filename.chop_extension (Filename.basename file) in
    let file = bfile ^ "-" ^ (string_of_int ic3_level) ^ "fp.latex" in
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
        Format.fprintf oc_fmt "%a\t\t\\\\[0.2cm]@." 
	  V.save_vertice k;
    (* List.iter ( *)
    (*   fun p -> *)
    (*     Format.fprintf oc_fmt "\t\t(%a) @." V.save_id p; *)
    (* ) e; *)
    (* Format.fprintf oc_fmt "\n--------------@." *)
    ) rg;
    Format.fprintf oc_fmt "\\end{document}@.";
    close_out oc;
    match Sys.command ("pdflatex -output-directory graphs graphs/"^file) with
      | 0 -> ()
      | _ ->
        Format.eprintf
          "There was an error with dot. Make sure graphviz is installed."


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
      V.add_subsume_dot v;
  ) rg
    
let update_extra rg =
  G.iter (
    fun v _ ->
      V.add_node_extra v;
      V.add_relation_extra v;
  ) rg
    
    
let update_step rg v1 =
  G.iter (
    fun v _ -> 
      let c = 
	if V.is_bad v 
	then if V.equal v1 v then "orange" else "red" 
	else "chartreuse" in
      V.add_node_step v c;
  (* V.print_step_subsume e; *)
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

let search dots system = 
  (* top = (true, unsafe) *)
  (* Create the world formula of top, true *)
  let wtop = V.create_world [] in
  (* Create the bad formula of top, unsafe *)
  let cunsl = system.t_unsafe in
  let unsl = 
    List.fold_left (
      fun acc cuns -> 
	let c = cuns.cube in 
	(c.Cube.vars, c.Cube.litterals)::acc
    ) [] cunsl in
  let btop = V.create_bad unsl in
  (* Create top with gtop, btop and no subsume *)
  let top = V.create wtop wtop V.KOriginal btop in
  (* Print top *)
  if ic3_verbose > 0 then
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
  (* Create the world formula of root, init *)
  let wroot = V.create_world initl in
  (* Create the bad formula of root, false *)
  let broot = V.create_bad [] in
  (* Create root with groot, broot and no subsume *)
  let root = V.create ~is_root:true wroot wroot V.KOriginal broot in
  if ic3_verbose > 0 then
    Format.eprintf "%a@." V.print_vertice root;    
  
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
    if ic3_verbose > 0 then
      Format.eprintf 
        "\n*******[Refine]*******\t(%a) --%a--> (%a)\n@." 
        V.print_id v1 Hstring.print tr.tr_info.tr_name 
        V.print_id v2;
    (* In this case we are trying to execute a new transition
       from v1 but v1 is already bad so must not be considered as
       a parent node. *)
    if V.is_bad v1 then (
      if ic3_verbose > 0 then
        Format.eprintf 
	  "We discard the treatment of this edge since (%a) is now bad\n@." 
          V.print_id v1;
      (rg, tc)
    )
    else if V.is_bad v2 then (
      if debug && verbose > 0 then print_graph rg;
      let pr = List.rev (find_graph v2 rg) in
      match V.refine v1 v2 tr pr with  

	(* v1 and tr imply bad *)
	| V.Bad_Parent bad ->
	  (* If v1 is root, we can not refine *)
	  if V.equal v1 root then raise (Unsafe (rg, v1));
	  (* Else, we recursively call refine on all the subsume *)
          
	  Format.eprintf "[Bad] (%a).world and %a imply (%a).bad@."
            V.print_id v1 Hstring.print tr.tr_info.tr_name V.print_id v2;
          if ic3_verbose > 1 then
            Format.eprintf "[New Bad] (%a).bad = %a@."
	      V.print_id v1 V.print_vednf v1;
	  if dot_step then add_steps v2 v1 Bad tr false;
          V.update_bad_from v1 tr v2;
	  List.fold_left (
	    fun (rg, tc) (vp, tr) -> 
              if ic3_verbose > 0 then
                Format.eprintf "[BadParent] (%a) --%a--> (%a).bad@."
		  V.print_id vp Hstring.print tr.tr_info.tr_name 
		  V.print_id v1;
	      if dot_step then add_steps vp v1 Bad tr true;
              refine vp v1 tr rg tc
	  ) (rg, tc) (V.get_subsume v1)
            
	(* The node vc covers v2 by tr *)
	| V.Covered vc -> 
	  let del = V.delete_parent v2 (v1, tr) in
	  V.add_parent vc (v1, tr);
	  if dot_step then (
	    add_steps v1 vc Cover tr false;
	    if del then add_steps v1 v2 Cover tr true;
	  );
	  if debug && ic3_verbose > 1 then (
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
	  if debug && ic3_verbose > 1 then (
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
          V.update_world_from vn v2;
	  Q.push vn todo;
	  (rg', tc)
    )
    else (
      (* if verbose > 0 then *)
      if ic3_verbose > 0 then
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
      (if verbose > 0 
       then V.print_vertice 
       else V.print_id) v1;
    let trans = V.expand v1 transitions in
    if ic3_verbose > 0 then
      List.iter (
        fun tr -> 
	  Format.eprintf "\t%a@." Hstring.print tr.tr_info.tr_name
      ) trans;
    let rg, tc = List.fold_left (
      fun (rg, tc) tr ->
        let v2 = C.find tr tc in
        if dot_step then add_steps v1 v2 Expand tr false;
	refine v1 v2 tr rg tc
    ) (rg, tc) trans
    in 
    let () = Sys.set_signal Sys.sigint 
      (Sys.Signal_handle 
	 (fun _ ->
           if debug && verbose > 0 then print_graph rg;
           save_graph rg;
           Stats.print_report ~safe:false [] [];
	   if dot then (
             update_dot rg;
	     Format.eprintf 
               "\n\n@{<b>@{<fg_red>ABORT !@}@} Received SIGINT@.";
             if dot_extra then update_extra rg;
	     if dot_step then (
	       let close_step = Dot.open_step () in
	       update_step rg v1;
	       update_steps (List.rev !steps);
	       close_step ();
	     )
           );
           dots ();
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
      if dot_extra then update_extra rg;
      if debug && verbose > 0 then print_graph rg;
      save_graph rg;
      Format.eprintf "Empty queue, Safe system@."; 
      RSafe
    | Unsafe (rg, v1) -> 
      if dot then update_dot rg;
      if dot_extra then update_extra rg;
      if dot_step then (
	let close_step = Dot.open_step () in
	update_step rg v1;
	update_steps (List.rev !steps);
	close_step ();
      );
      if debug && verbose > 0 then print_graph rg;
      save_graph rg;
      RUnsafe
