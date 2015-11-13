open Far_modules

let rec unwind v1 t v2 graph =
  (* If the source vertex is already bad, the unwinding is useless *)
  if Vertex.is_bad v1 then ()
    (* If the destination vertex isn't bad, the unwinding is useless *)
  else if not (Vertex.is_bad v2) then ()
  else 
    match Far_close.close v1 t v2 graph with
      | Far_close.Bad_part bp ->
        (* If the source vertex, now bad, is the root vertex, the system is bad *)
        if Vertex.is_root v1 then raise Exit
        else 
          begin
            Vertex.update_bad v1 bp t v2;
            let parents = Far_graph.get_parents v1 graph in
            List.iter (
              fun (t', vp) ->
                unwind vp t' v1 graph
            ) parents
          end
      | Far_close.Covered vc ->
        Far_graph.update_edge v1 t v2 vc graph;
        unwind v1 t vc graph;
      | Far_close.Refined r ->
        let nv = Vertex.create_from_refinement v2 r in
        Far_graph.add_vertex nv graph;
        Far_graph.update_edge v1 t v2 nv graph;
        Q.push nv queue
          
          
