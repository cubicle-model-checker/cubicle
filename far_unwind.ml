open Ast
open Far_modules
open Options

let rec unwind v1 t v2 graph system =
  if not quiet then
    Format.eprintf 
      "\n********[Unwind]********\t(%a) --%a--> (%a)\n@." 
      Vertex.print_id v1 Hstring.print t.tr_info.tr_name 
      Vertex.print_id v2;
  
  (* If the source vertex is already bad, the unwinding is useless *)
  if Vertex.is_bad v1 then (* Format.eprintf "[Already Bad] %a\n@." Vertex.print_id v1 *) ()
  (* If the destination vertex isn't bad, the unwinding is useless *)
  else if not (Vertex.is_bad v2) then ()
  else 
    match Far_close.close v1 t v2 graph system with
      | Far_close.Bad_part bp ->
        (* Format.eprintf "\t[Bad part]"; Far_bads.print_bads bp; *)
        
        (* If the source vertex, now bad, is the root vertex, the system is bad *)
        if Vertex.is_root v1 then raise Exit
        else 
          begin
            Vertex.update_bad v1 bp t v2;
            let parents = Far_graph.get_parents v1 graph in
            List.iter (
              fun (vp, t') ->
                unwind vp t' v1 graph system
            ) parents
          end
      | Far_close.Covered vc ->
        (* Format.eprintf "\t[Covered by] %a@." Vertex.print_id vc; *)
        Far_graph.update_edge v1 t v2 vc graph;
        unwind v1 t vc graph system; 
      | Far_close.Refined r ->
        let nv = Vertex.create_from_refinement v2 r in
        Stats.new_vertex nv;
        Far_graph.add_vertex nv graph;
        Far_graph.update_edge v1 t v2 nv graph;
        (* Format.eprintf "\t[New node] %a@." Vertex.print_id nv; *)
        (* Format.eprintf "\n%a@." Vertex.print_world nv; *)
        Q.push nv queue
          
          
