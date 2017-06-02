open Ast
open Far_modules
open Options
open Util

exception Bad of (transition * Vertex.t * Far_cube.t list)
exception PropBad of Far_cube.t list

let filter_l dim l =
  let rec f acc ll =
    match ll with 
      | hd::tl when (Far_cube.dim hd) = dim -> f (hd::acc) tl
      | _ -> acc
  in f [] l
  
let rec unwind v1 t v2 graph system =
  if far_verb then
    Format.eprintf 
      "\n********[Unwind]********\t(%a) --%a--> (%a)\n@." 
      Vertex.print_id v1 Hstring.print t.tr_info.tr_name 
      Vertex.print_id v2;
  
  (* If the source vertex is already bad, the unwinding is useless *)
  if Vertex.is_bad v1 then 
    (if far_verb then Format.eprintf "[Already Bad] %a\n@." Vertex.print_id v1)
  (* If the destination vertex isn't bad, the unwinding is useless *)
  else if not (Vertex.is_bad v2) then ()
  else 
    match Far_close.close v1 t v2 graph system with
      | Far_close.Bad_part bp ->
        (* let bp = [List.hd bp] in *)
        if far_verb then (Format.eprintf "\t[Bad part]"; Far_bads.print_bads bp);
        
        (* If the source vertex, now bad, is the root vertex, the system is bad *)
        if Vertex.is_root v1 then raise Exit
        else 
          let bp = List.fast_sort Far_cube.compare_by_breadth bp in
          (match List.filter (
            fun n ->
              Stats.(!cpt_process) = Far_cube.dim n) bp 
           with
             | [] -> raise (Bad (t, v2, bp))
             | b -> raise (PropBad b)
          )
      | Far_close.Covered vc ->
        if far_verb then Format.eprintf "\t[Covered by] %a@." Vertex.print_id vc;
        Far_graph.update_edge v1 t v2 vc graph;
        unwind v1 t vc graph system; 
      | Far_close.Refined r ->
        let nv = Vertex.create_from_refinement v2 r in
        Stats.new_vertex nv;
        Far_graph.add_vertex nv graph;
        Far_graph.update_edge v1 t v2 nv graph;
        if far_verb then Format.eprintf "\t[New node] %a@." Vertex.print_id nv;
        Q.push nv queue
          
and prop v b graph system =
  let d = Node.dim (List.hd b) in
  let b = filter_l d b in
  let b = List.fold_left (
    fun acc b -> match Fixpoint.FixpointList.check b acc with
      | None -> b::acc
      | Some _ -> acc
  ) [] b in
  let b = [List.hd b] in
  let b =
    if Options.far_brab then
      List.map (fun nb ->
        match Approx.Selected.good nb with
          | None -> nb
          | Some c ->
            try
              (* Replace node with its approximation *)
              Safety.check system c;
              (* candidates := c :: !candidates; *)
              Stats.candidate nb c;
              (* Format.eprintf
                 "Approximation : \n%a ->  \n%a@." Node.print nb Node.print c; *)
              c
            with Safety.Unsafe _ -> nb
            (* If the candidate is directly reachable, no need to
               backtrack, just forget it. *)
            (* if ic3_verbose > 0 then *)
      ) b
    else b in
  Vertex.update_bad v b;
  List.iter Stats.new_node b;
  let parents = Far_graph.get_parents v graph in
  List.iter (
    fun (vp, t') ->
      unwind vp t' v graph system
  ) parents
    
let propagate v bads graph system =
  TimeSelect.start ();
  let bp = Far_bads.select_parts v bads graph system in
  TimeSelect.pause ();
  prop v bp graph system
