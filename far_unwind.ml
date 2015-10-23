type furesult = FSafe | FUnsafe
    
let rec unwind v1 t v2 graph =
  (* If the source vertex is already bad, the unwinding is useless *)
  if Far_vertex.is_bad v1 then ()
    (* If the destination vertex isn't bad, the unwinding is useless *)
  else if not (Far_Vertice.is_bad v2) then ()
  else 
    match Far_close.close v1 t v2 with
      | Far_close.Bad_part bp ->
        (* If the source vertex, now bad, is the root vertex, the system is bad *)
        if Far_vertex.is_root v1 then raise FUnsafe
        else 
          begin
            Far_vertex.update_bad v1 bad t v2;
            let parents = Far_vertex.get_parents v1 in
            List.iter (
              fun (vp, t') ->
                unwind vp t' v1 graph
            ) parents
          end
      | Far_close.Covered vc ->
        Far_graph.update_edge v1 t v2 vc graph;
        unwind v1 t vc graph;
      | Far_close.Refined r ->
        let nv = Vertex.create_refinement v2 r in
        Far_graph.add_vertex vn graph;
        Far_graph.update_edge v1 t v2 nv graph;
        Q.push nv Far.queue
          
          
