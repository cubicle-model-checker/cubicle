open Ed_graph

let center_row = ref ""

type model_t = Edge of (G.V.t * G.V.t) | Node of G.V.t | UnsafeNode of G.V.t 

(* Model for the treeview on the left *)

module Model = struct

  open Gobject.Data

  let cols = new GTree.column_list
  let name = cols#add string
  let vertex = cols#add caml
  let model = GTree.tree_store cols
  let rows = H.create 97


  let find_row v =
    try 
      H.find rows v
    with Not_found -> 
      Format.eprintf "anomaly: no model row for %s@." (string_of_label v);
      raise Not_found

  let add_vertex v =
    let row = model#append () in
    model#set ~row ~column:name (get_str_label v);
    model#set ~row ~column:vertex v;
    H.add rows v row;
    row

  let add_vertex_unsafe v = 
    let row = model#append () in
    model#set ~row ~column:name ("Unsafe :\n"^get_str_label v);
    model#set ~row ~column:vertex v;
    H.add rows v row;
    row

  let add_edge_1 row_v w =
    let row = model#append ~parent:row_v () in
    model#set ~row ~column:name (get_str_label w);
    model#set ~row ~column:vertex w
      
  let add_edge v w =
    let row_v = find_row v in
    add_edge_1 row_v w;
    if not G.is_directed then
      (let row_w = find_row w in
       add_edge_1 row_w v)

        
  let find_children row_v w =
    (let nb_child = model#iter_n_children (Some row_v) in
     let rec find n = 
       let child = model#iter_children ~nth:(n - 1) (Some row_v) in
       let child_vertex = model#get ~row:child ~column:vertex  in
       match n with
         | 0 -> raise Not_found
         | n -> 
           if (G.V.equal child_vertex  w)
           then child
           else find (n-1)
     in
     find nb_child)

  let remove_edge_1 row_v w =
    ignore (model#remove (find_children row_v w))

  let remove_edge v w =
    let row_v = find_row v in
    remove_edge_1 row_v w;
    if not G.is_directed then 
      let row_w = find_row w in
      remove_edge_1 row_w v

  let remove_vertex vertex = 
    G.iter_succ (fun w -> remove_edge w vertex) !graph vertex;
    let row = find_row vertex in
    model#remove row

  let reset () =
    H.clear rows;
    model#clear ();
    G.iter_vertex
      (fun v -> 
        let row = add_vertex v in
        G.iter_succ (add_edge_1 row) !graph v)
      !graph

end

let background_cell_data renderer (model:GTree.model) iter =
  let ver = Model.model#get ~row:iter ~column:Model.name in
  if ver = !center_row then
    renderer#set_properties [`BACKGROUND "white"; `FOREGROUND "black"]
  else
    renderer#set_properties [`BACKGROUND "light grey"; `FOREGROUND "grey"]

(* let () = Model.reset () *)

let model_reset ()  = Model.reset () 
