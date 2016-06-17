(**************************************************************************)
(*                                                                        *)
(*  Ocamlgraph: a generic graph library for OCaml                         *)
(*  Copyright (C) 2004-2010                                               *)
(*  Sylvain Conchon, Jean-Christophe Filliatre and Julien Signoles        *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(* This file is a contribution of Benjamin Vadon *)

open Format
open Ed_hyper
open Ed_graph
open Ed_display

let graph_trace = Queue.create ()

let m = Mutex.create ()

exception End_trace

let cpt = ref 1

module HT  = 
  Hashtbl.Make
    (struct 
      type t = string
      let equal x y = (String.trim x) = (String.trim y) 
      let hash x  = Hashtbl.hash x 
    end)

let ht = HT.create 500

let debug = ref false
let trace f x = 
  try f x with e -> eprintf "TRACE: %s@." (Printexc.to_string e); raise e

let _ = GMain.init ()

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

  let add_edge_1 row_v w =
    let row = model#append ~parent:row_v () in
    model#set ~row ~column:name (string_of_label w);
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
      let child = model#iter_children ~nth:(n-1) (Some row_v) in
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

let () = Model.reset ()

let model_reset ()  = Model.reset () 

let ed_name = "Ocamlgraph's Editor"

(* Main GTK window *)
let window = GWindow.window ~border_width: 10 ~position: `CENTER () 

(* usual function to change window title *)
let set_window_title () =
  window#set_title
    (match !graph_name with
     | None -> ed_name
     | Some name -> ed_name^" : "^(Filename.chop_extension (Filename.basename name)))

(* menu bar *)
let v_box = GPack.vbox ~homogeneous:false ~spacing:30  ~packing:window#add ()

let menu_bar_box = GPack.vbox ~packing:v_box#pack () 

(* treeview on the left, canvas on the right *)
let h_box = GPack.hbox ~homogeneous:false ~spacing:30  ~packing:v_box#add ()

let sw = GBin.scrolled_window ~shadow_type:`ETCHED_IN ~hpolicy:`NEVER
    ~vpolicy:`AUTOMATIC ~packing:h_box#add () 

let canvas =  
  GnoCanvas.canvas 
    ~aa:!aa 
    ~width:(truncate w) 
    ~height:(truncate h) 
    ~packing:h_box#add () 

(* unit circle as root of graph drawing *)
let canvas_root =
  let circle_group = GnoCanvas.group ~x:(w/.2.) ~y:(h/.2.) canvas#root in
  circle_group#lower_to_bottom ();
  let w2 = 2. in
  let circle = GnoCanvas.ellipse 
 ~props:[ `X1 (-.w/.2. +.w2); `Y1 (-.h/.2. +.w2); 
          `X2  (w/.2. -.w2) ; `Y2 ( h/.2. -.w2) ;
          `FILL_COLOR color_circle ; `OUTLINE_COLOR "black" ; 
          `WIDTH_PIXELS (truncate w2) ] circle_group 
  in
  circle_group#lower_to_bottom ();
  circle#show();
  let graph_root = GnoCanvas.group ~x:(-.(w/.2.)) ~y:(-.(h/.2.)) circle_group in
  graph_root#raise_to_top ();
  set_window_title ();
  graph_root

(* current root used for drawing *)
let root = ref (choose_root ())

(* refresh rate *)
let refresh = ref 0

let do_refresh () =
  !refresh mod !refresh_rate = 0 

(* graph drawing *)
let draw tortue canvas =
  match !root with
  | None -> ()
  | Some root -> 
    try 
      Ed_draw.draw_graph root tortue;
      Ed_display.draw_graph root canvas; 
    if do_refresh () then
      canvas_root#canvas#update_now ()
    with Not_found  -> ()
        
let refresh_draw () =
  refresh := 0;    
  let tor = make_turtle !origine 0.0 in
  draw tor canvas_root

let refresh_display () =
  Ed_display.draw_graph !root canvas_root

let root_change vertex ()= 
  root := vertex; 
  origine := start_point;
  let turtle = make_turtle_origine () in
  draw turtle canvas_root

let node_selection ~(model : GTree.tree_store) path =
  let row = model#get_iter path in
  let vertex = model#get ~row ~column: Model.vertex in
  root_change (Some vertex) ()

(* usual function ref, for vertex event *)
let set_vertex_event_fun = ref (fun _ -> ())

(* event for each vertex of canvas *)
let vertex_event vertex item ellispe ev =
  (* let vertex_info = G.V.label vertex in*)
  begin match ev with
    | `ENTER_NOTIFY _ -> 
      item#grab_focus ();
      update_vertex vertex Focus;
      refresh_display ()

    | `LEAVE_NOTIFY ev ->
      if not (Gdk.Convert.test_modifier `BUTTON1 (GdkEvent.Crossing.state ev))
      then begin

        update_vertex vertex Unfocus;
        refresh_display ()
      end

    | `BUTTON_RELEASE ev ->
      ellispe#parent#ungrab (GdkEvent.Button.time ev);

    | `MOTION_NOTIFY ev -> 
      incr refresh;
      let state = GdkEvent.Motion.state ev in
      if Gdk.Convert.test_modifier `BUTTON1 state  then
        begin
          let curs = Gdk.Cursor.create `FLEUR in
          ellispe#parent#grab [`POINTER_MOTION; `BUTTON_RELEASE]
            curs (GdkEvent.Button.time ev);
          if do_refresh ()
          then begin
            let old_origin = !origine in
            let turtle = motion_turtle ellispe ev in
            let hspace = hspace_dist_sqr turtle in 
            if hspace <=  rlimit_sqr then begin
              draw turtle canvas_root;
            end else begin
              origine := old_origin;
              let turtle = { turtle with pos = old_origin } in
              draw turtle canvas_root
            end
          end
        end

   | `BUTTON_PRESS ev ->  ()
    | `TWO_BUTTON_PRESS ev->
      if (GdkEvent.Button.button ev) = 1
      then 
        begin
          match !root with
            | None -> ()
            | Some root -> 
              let v = G.V.label vertex in 
              v.changed <- true ;
              G.iter_succ_e (fun x -> let e = G.E.label x in
              e.visible_label <- not e.visible_label) !graph vertex ;
              if v.label_mode = Num_Label then 
                (v.label <- v.str_label;
                 v.label_mode <- Str_Label)
              else
            (v.label <- v.num_label;
             v.label_mode <- Num_Label);
              refresh_draw ()
        end

    | _ ->
      ()
  end;
  true

let set_vertex_event vertex =
  let item,ell,_ = H.find nodes vertex in
  ignore (item#connect#event ~callback:(vertex_event vertex item ell))

let () = set_vertex_event_fun := set_vertex_event

let set_canvas_event () =
  G.iter_vertex set_vertex_event !graph

(* treeview *)
let add_columns ~(view : GTree.view) ~model =
  let renderer = GTree.cell_renderer_text [`XALIGN 0.] in
  let vc = GTree.view_column ~title:"Nodes" ~renderer:(renderer, ["text", Model.name]) ()
  in
  ignore (view#append_column vc);
  vc#set_sizing `FIXED;
  vc#set_fixed_width 100;
  vc#set_sizing `AUTOSIZE;
  view#selection#connect#after#changed ~callback:
    begin fun () ->
      List.iter
        (fun p -> node_selection ~model p)
        view#selection#get_selected_rows;
    end

let _ = window#connect#destroy~callback:GMain.quit 

let treeview = GTree.view ~model:Model.model ~packing:sw#add ()
let () = treeview#set_rules_hint true
let () = treeview#selection#set_mode `MULTIPLE
let _ = add_columns ~view:treeview ~model:Model.model

(* reset *)

let reset_table_and_canvas () =
  let l =  canvas_root#get_items in
  List.iter (fun v -> trace v#destroy ()) l;
  H2.clear intern_edges;
  H2.clear successor_edges;
  reset_display canvas_root;
  origine := start_point;
  nb_selected:=0
  
let rec node_name  = function
  |[] -> ""
  |x::[] -> 
    (match Str.split (Str.regexp "\n") (String.trim x) with
      |[] -> failwith "pb format trace 2"
      |y::_ ->  y)
  |x::s -> (String.trim x)^"\n"^(node_name s)
        
let create_node s first = 
  (* Printf.printf "node\n"; *)
  let pos = Str.search_forward (Str.regexp "=") s 0 in
  let before = Str.global_replace (Str.regexp "[\n| ]+") "" 
        ( String.trim (Str.string_before s pos)) in 
  let after = node_name (Str.split (Str.regexp "&&") (Str.string_after s (pos + 1))) in
  let v = G.V.create (make_node_info (string_of_int !cpt) after) in
  if !first then
    root := Some v;
  first := false;
  HT.add ht before v;
  G.add_vertex !graph v;
  ignore (Model.add_vertex v);
  Ed_display.add_node canvas_root v;
  !set_vertex_event_fun v;
  let tor = make_turtle !origine 0.0 in
  draw tor canvas_root;
  (try
     let arrow_pos = Str.search_forward (Str.regexp "->") before 0 in
     let transition = Str.string_before before arrow_pos in
     let node = Str.global_replace (Str.regexp "[\n| ]+") "" 
       (Str.string_after before (arrow_pos + 2)) in 
     let n = HT.find ht node in 
     let e = G.E.create n (make_edge_info_label transition) v in 
     G.add_edge_e !graph e;
     ignore (Model.add_edge n v);
   with Not_found -> ());
  incr cpt;
  Thread.delay 0.1
  
let rec list_to_node curr_node first = function
  |[] -> ()
  |[x] -> 
    (try
       let pos = Str.search_forward (Str.regexp "==") x 0 in 
       let before = Str.string_before x pos in 
       create_node before first;
       raise End_trace
     with Not_found -> (curr_node := !curr_node ^ x))
  |x::s -> 
    curr_node := !curr_node ^ x;
    create_node !curr_node first;
    curr_node := "";
    list_to_node curr_node first s 
      
let rec build_node curr_node str first = 
  let str_l = Str.split (Str.regexp "node [0-9]+:") str in
  match str_l with
  |[] -> ()
  |[x] -> 
    (if !curr_node <> "" then
        create_node !curr_node first;
     curr_node := x)
  |x::s ->
    list_to_node curr_node first str_l
  
let load_graph () =
  try
    let curr_node = ref "" in
    let first = ref true in 
    while true do
      try
        Mutex.lock m;
        let str = Queue.pop graph_trace in
        Mutex.unlock m;
        if Str.string_match (Str.regexp "==") str 0 then
          (build_node curr_node str first;
           raise End_trace)
        else if Str.string_match (Str.regexp "node [0-9]+:") str 0 then 
            build_node curr_node str first
        else
          curr_node := !curr_node ^ str
      with Queue.Empty -> Printf.printf " "; Mutex.unlock m;
    done
  with End_trace -> ()

let show_tree file () = 
  let ic = Unix.open_process_in ("cubicle -nocolor -v "^file) in
     (try
       while true do
         let s = input_line ic in
         Mutex.lock m;
         Queue.push (s^"\n") graph_trace;
         Mutex.unlock m;
         Thread.yield ();
       done
     with
         End_of_file ->
           close_in ic)

let tree file  = 
  Queue.clear graph_trace;
  ignore (Thread.create (show_tree file) ());
  ignore (Thread.create load_graph ()) 

let open_graph file  =
  reset_table_and_canvas ();
  draw (make_turtle_origine ()) canvas_root;
  set_canvas_event ();
  canvas#set_scroll_region ~x1:0. ~y1:0. ~x2:w ~y2:h ;
  ignore (window#show ());
  tree file ;
  GtkThread.main ()
    

         
 


