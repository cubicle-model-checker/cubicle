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

type model_t = Edge of (G.V.t * G.V.t) | Node of G.V.t | UnsafeNode of G.V.t 

(* let mode_equals = ref false  *)

let mode_change = ref false

let mode_value = ref false

(* let mode_and = ref false  *)

let m = Mutex.create ()

let m_end = Mutex.create ()

let c = Condition.create ()

let c_end = Condition.create ()

let var_l = ref []

let end_show_tree = ref false

let center_row = ref ""

let end_load_graph = ref false

exception End_trace

exception KillThread

let kill_thread = ref false

let cpt = ref 1

let scroll_to_transition = ref (fun _ -> ())

(* let model = Queue.create () *)
(* let m_model = Mutex.create ()  *)
(* let c_model = Condition.create () *)
(* module Var_L = Map.Make (String) *)

module HTString  =
  (struct
    type t = string
    let equal x y = (String.trim x) = (String.trim y)
    let hash x  = Hashtbl.hash x
   end)

module HT = Hashtbl.Make (HTString)

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

let () = Model.reset ()

let model_reset ()  = Model.reset () 

let ed_name = "Ocamlgraph's Editor"

let window =
  let wnd = GWindow.window
    ~border_width: 10
    ~resizable: true
    ~position: `CENTER () in
  let _ = wnd#destroy_with_parent in
  let _ = wnd#event#connect#delete ~callback:(fun b -> 
    kill_thread := true;
    wnd#misc#hide ();
    true(* GMain.quit *))in wnd

(* menu bar *)
let v_box = GPack.vbox ~homogeneous:false ~spacing:30  ~packing:window#add () 

let toolbox_frame = GBin.frame ~border_width:8  ~packing:(v_box#pack ~expand:false ~fill:false ) () 

let toolbox = GPack.hbox  ~packing:(toolbox_frame#add) () 

let toolbar =
  let t = GButton.toolbar ~tooltips:true ~packing:toolbox#add () 
  in t#set_icon_size `DIALOG; t 

let start_button = 
  toolbar#insert_button 
    ~text:" Start"
    ~icon:(GMisc.image ~stock:`EXECUTE ())#coerce ()

let stop_button =
  toolbar#insert_button
    ~text:" Abort"
    ~icon:(GMisc.image ~stock:`STOP  ~icon_size:`LARGE_TOOLBAR())#coerce () 

let test_button = 
  toolbar#insert_button 
    ~text:" " () 

let resultbox, result_image, result_label =
  toolbar#insert_space ();
  let hbox = GPack.hbox () in
  let result_image = GMisc.image ~icon_size:`LARGE_TOOLBAR
    ~packing:hbox#add () in
  let result_label = GMisc.label ~text:" " ~packing:hbox#add () in
  ignore(toolbar#insert_widget hbox#coerce); hbox, result_image, result_label

let menu_bar_box = GPack.vbox ~packing:v_box#pack () 

(* treeview on the left, canvas on the right *)
let h_box = GPack.hbox ~homogeneous:false ~spacing:30  ~packing:v_box#add () 

(* let sw_frame =  *)
(*   GBin.frame ~border_width:8 ~packing:(h_box#add) () *)

let sw = GBin.scrolled_window 
  ~shadow_type:`ETCHED_IN
  ~hpolicy:`NEVER
  ~vpolicy:`AUTOMATIC
  ~packing:h_box#add () 

(* let canvas_frame =  *)
(*   GBin.frame ~border_width:8  ~packing:(h_box#add) () *)

let canvas = 
  (GnoCanvas.canvas 
     ~aa:!aa 
     ~width:(truncate w) 
     ~height:(truncate h) 
     ~packing:h_box#add ()) 

(* unit circle as roots of graph drawing *)
let (canvas_root, focus_rectangle) =
  let circle_group = GnoCanvas.group ~x:(w/.2.) ~y:(h/.2.) canvas#root in
  circle_group#lower_to_bottom ();
  let w2 = 2. in
  let circle = GnoCanvas.ellipse 
    ~props:[ `X1 (-.w/.2. +. w2); `Y1 (-.h/.2. +.w2); 
             `X2 (  w/.2. -. w2); `Y2 ( h/.2. -. w2) ;
             `FILL_COLOR color_circle ; `OUTLINE_COLOR "black" ; 
             `WIDTH_PIXELS (truncate w2) ] circle_group 
  in
  circle_group#lower_to_bottom ();
   let r = GnoCanvas.rect
    ~x1:(-. 100.) ~y1:(-. 80.)
    ~x2:(100.) ~y2:(80.) ~props:[`FILL_COLOR "#e0e0e0"] circle_group
   in
   r#hide ();
   circle_group#lower_to_bottom ();
   circle#show();
  let graph_root = GnoCanvas.group ~x:(-.(w/.2.)) ~y:(-.(h/.2.)) circle_group in
  graph_root#raise_to_top ();
  (graph_root, r)

 (* current root used for drawing *)
 let root = ref (choose_root ())

 (* refresh rate *)
 let refresh = ref 0

let do_refresh () =
  !refresh mod !refresh_rate = 0 

let treeview = GTree.view 
  ~model:Model.model 
  ~packing:sw#add ()

(* graph drawing *)
let draw tortue canvas (vc : GTree.view_column) renderer =
  match !root with
    | None -> ()
    | Some root -> 
      try 
        Ed_draw.draw_graph root tortue;
        let center_node = Ed_display.draw_graph root canvas in
        if do_refresh () then
          canvas_root#canvas#update_now ();
        match center_node with 
          |None -> ()
          |Some v -> 
            let row = Model.find_row v in
            center_row := Model.model#get ~row:row ~column:Model.name;
            let path = Model.model#get_path row in 
            treeview#scroll_to_cell ~align:(0.5, 0.5) path vc;
            vc#set_cell_data_func renderer (background_cell_data renderer);
      with Not_found  -> ()

        
let refresh_draw vc renderer () =
  refresh := 0;    
  let tor = make_turtle !origine 0.0 in
  draw tor canvas_root vc renderer

let root_change vertex vc renderer () = 
  root := vertex; 
  origine := start_point;
  let turtle = make_turtle_origine () in
  draw turtle canvas_root vc renderer

let node_selection ~(model : GTree.tree_store) path vc renderer =
  let row = model#get_iter path in
  let vertex = model#get ~row ~column: Model.vertex in
  root_change (Some vertex) vc renderer ()

(* treeview *)
let add_columns ~(view : GTree.view) ~model =
  let renderer = GTree.cell_renderer_text [`XALIGN 0.] in
  let vc = GTree.view_column ~title:"Nodes" ~renderer:(renderer, ["text", Model.name]) ()
  in
  ignore (view#append_column vc);
  vc#set_sizing `AUTOSIZE;
  ignore (view#selection#connect#after#changed ~callback:
            begin
              fun () ->
                List.iter
                  (fun p -> node_selection ~model p vc renderer)
                  view#selection#get_selected_rows;
            end);
  vc, renderer

let () = treeview#set_rules_hint true
let () = treeview#selection#set_mode `MULTIPLE
let (vc, renderer) = add_columns ~view:treeview ~model:Model.model

let refresh_display () =
  ignore (Ed_display.draw_graph !root canvas_root)

(* usual function ref, for vertex event *)
let set_vertex_event_fun = ref (fun _ -> ())


let contextual_menu vertex ev =
  let menu = new GMenu.factory (GMenu.menu ()) in
  ignore (menu#add_item "As root" ~callback:(root_change (Some vertex) vc renderer));
  menu#menu#popup ~button:3 ~time:(GdkEvent.Button.time ev)

(* event for each vertex of canvas *)
let vertex_event vertex item ellipse ev =
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
      focus_rectangle#hide();
      ellipse#parent#ungrab (GdkEvent.Button.time ev);

    | `MOTION_NOTIFY ev -> 
      incr refresh;
      let state = GdkEvent.Motion.state ev in
      if Gdk.Convert.test_modifier `BUTTON1 state  then
        begin
          let curs = Gdk.Cursor.create `FLEUR in
          focus_rectangle#show();
          ellipse#parent#grab [`POINTER_MOTION; `BUTTON_RELEASE]
            curs (GdkEvent.Button.time ev);
          if do_refresh ()
          then begin
            let old_origin = !origine in
            let turtle = motion_turtle ellipse ev in
            let hspace = hspace_dist_sqr turtle in
            if hspace <= rlimit_sqr then begin
              draw turtle canvas_root vc renderer;
            end else begin
              origine := old_origin;
              let turtle = { turtle with pos = old_origin } in
              draw turtle canvas_root vc renderer
            end
          end

        end
    | `BUTTON_PRESS ev ->  
      if (GdkEvent.Button.button ev) = 3
      then 
        contextual_menu vertex ev 
    | `TWO_BUTTON_PRESS ev->
      if (GdkEvent.Button.button ev) = 1
      then 
        begin
          match !root with
            | None -> ()
            | Some root -> 
              let v = G.V.label vertex in 
              v.changed <- true ;
              if v.label_mode = Num_Label then 
                (v.label <- v.str_label;
                 v.label_mode <- Str_Label;
                 G.iter_succ_e (fun x -> let e = G.E.label x in
                                         e.visible_label <- true) !graph vertex )
              else
                (v.label <- v.num_label;
                 v.label_mode <- Num_Label;
                 G.iter_succ_e (fun x -> let e = G.E.label x in
                                         e.visible_label <- false) !graph vertex );
              refresh_draw vc renderer ()
        end

    | _ ->
      ()
  end;
  true

let contextual_menu_text t ev =
  let menu = new GMenu.factory (GMenu.menu ()) in
  ignore (menu#add_item "Show in editor"
            ~callback:(fun () -> !scroll_to_transition t));
  menu#menu#popup ~button:3 ~time:(GdkEvent.Button.time ev)

let edge_event texte label ev =
  begin
    match ev with
      | `ENTER_NOTIFY _ -> 
        texte#grab_focus ();
        texte#set [(* `FILL_COLOR "red"; *) `WEIGHT 1000];
        (* update_vertex rtex Focus; *)
        refresh_display ()
      | `LEAVE_NOTIFY ev ->
      if not (Gdk.Convert.test_modifier `BUTTON1 (GdkEvent.Crossing.state ev))
      then begin
        texte#set [`FILL_COLOR "black"; `WEIGHT 0];
        (* update_vertex vertex Unfocus; *)
        refresh_display ()
      end
        
    | `BUTTON_RELEASE ev ->
      (* focus_rectangle#hide(); *)
      texte#ungrab (GdkEvent.Button.time ev);

    | `MOTION_NOTIFY ev -> 
      (* texte#set [`FILL_COLOR "red"]; *)
      incr refresh;
      let state = GdkEvent.Motion.state ev in
      if Gdk.Convert.test_modifier `BUTTON1 state  then
        begin
          let curs = Gdk.Cursor.create `FLEUR in
          focus_rectangle#show();
          texte#grab [`POINTER_MOTION; `BUTTON_RELEASE]
            curs (GdkEvent.Button.time ev);
        end
    | `BUTTON_PRESS ev ->  
      if (GdkEvent.Button.button ev) = 3
      then
        contextual_menu_text label ev
    | _ ->
      ()
  end;
  true

let set_vertex_event vertex =
  let item,ell,_ = H.find nodes vertex in 
  ignore (item#connect#event ~callback:(vertex_event vertex item ell))

let set_edge_event e = 
  let src = G.E.src e in 
  let dst = G.E.dst e in 
  let label = (G.E.label e).label in
  let _, _, texte = 
    H2.find successor_edges (src, dst) in 
  ignore (texte#connect#event ~callback:(edge_event texte label))


let () = set_vertex_event_fun := set_vertex_event

let set_canvas_event () =
  G.iter_vertex set_vertex_event !graph;
  G.iter_edges_e (set_edge_event) !graph


(* reset *)

let reset_table_and_canvas () =
  let l = canvas_root#get_items in
  List.iter (fun v -> trace v#destroy ()) l;
  H2.clear intern_edges;
  H2.clear successor_edges;
  reset_display canvas_root;
  origine := start_point;
  nb_selected := 0


let split_node_info x m v changed_l mode new_name =
  let var_find_or before after  =
    List.fold_left (fun acc (x, var_i) ->
      match var_i with 
        |None -> 
          (if x = before  then
              true
           else
              try
                let pos = Str.search_forward (Str.regexp "\\[") before 0 in
                let array_name = Str.global_replace (Str.regexp "[\n| ]+") ""
                  (Str.string_before before pos) in
                if array_name = x then
                  true
                else acc
              with Not_found -> acc)
        |Some l ->  
          if x = before then
            List.mem after l
          else
            try
              let pos = Str.search_forward (Str.regexp "\\[") before 0 in
              let array_name = Str.global_replace (Str.regexp "[\n| ]+") ""
                (Str.string_before before pos) in
              if array_name = x && List.mem after l then
                true
              else  acc
            with Not_found ->  acc) false !var_l
  in
  (let pos, eq = 
     try (Str.search_forward (Str.regexp "[=]") x 0, true)
     with Not_found -> 
       try
         (Str.search_forward (Str.regexp "[<>]") x 0, false)
       with Not_found -> failwith "Probleme format trace" in
   let pos = if eq then pos else pos - 1 in 
   let before = Str.global_replace (Str.regexp "[\n| ]+") ""
     (Str.string_before x pos) in
   let after =  Str.global_replace (Str.regexp "[\n| ]+") ""
     (Str.string_after x (pos + 1)) in
   let m =
     try
       if !mode_change then 
         (let a = Var_Map.find before m in
          let var_find = 
            (* if !mode_and then var_find_and before after *)
            (* else *) var_find_or before after in
          if a <> after && var_find then
            ((G.V.label v).vertex_mode <- VarChange;
             if a <> after then 
             (G.V.label v).num_label <- (G.V.label v).num_label ^ "\n" ^ before ^ " :\n"
             ^ a ^ " -> " ^ after
             else
               (G.V.label v).num_label <- (G.V.label v).num_label ^ "\n" ^ before ^ " :\n"
               ^ a 
););
       m
     with Not_found -> m in
   (before, after, m))
    
let rec build_map m v l mode new_name=
  let var_init before after m = 
    if not (Var_Map.mem before m) && 
      List.fold_left (fun acc (x, vars) ->
        match vars with 
          |None -> 
            if x = before then true else acc
          |Some var_l -> 
            if x = before && List.mem after var_l then true else acc
      ) false !var_l then 
      ((G.V.label v).vertex_mode <- VarInit;
       (G.V.label v).num_label <- 
         (G.V.label v).num_label ^ "\n" ^ before ^ " <- " ^ after);
  in 
  let changed_l = ref "" in
  match l with
    |[] -> m
    |y::[] ->
      (match Str.split (Str.regexp "\n") (String.trim y) with
        |[] -> failwith "pb format trace 2"
        |x::_ ->
          (try
             let before, after, m = split_node_info x m v changed_l mode new_name in
             var_init before after m;
             Var_Map.add before after m
           with Not_found -> failwith "erreur build map"))
    |x::s ->
      try
        let before, after, m = split_node_info x m v changed_l mode new_name in
        var_init before after m;
        build_map (Var_Map.add before after m) v s mode new_name
      with Not_found -> failwith "erreur build map"
        
        
let rec node_name = function
  |[] -> ""
  |x::[] ->
    (match Str.split (Str.regexp "\n") (String.trim x) with
      |[] -> failwith "pb format trace 2"
      |y::_ ->  y)
  |x::s -> (String.trim x)^"\n"^(node_name s)
    
let link_node before v after =
  let mode = ref true in 
  let new_name = ref "" in
  try
    (let arrow_pos = Str.search_forward (Str.regexp "->") before 0 in
     let transition = Str.string_before before arrow_pos in
     let node = Str.global_replace (Str.regexp "[\n| ]+") ""
       (Str.string_after before (arrow_pos + 2)) in
     let n = HT.find ht node in
     let e = G.E.create n (make_edge_info_label transition true) v in
     let map = build_map (G.V.label n).var_map v after mode new_name in 
     (G.V.label v).var_map <- map;
     if !mode_value then 
       (let label = ref "" in 
        let b = List.fold_left (fun acc (x, var_i) -> 
       match var_i with 
         |None -> false
         |Some l -> 
           try
             let var_val = Var_Map.find x map in
             if List.mem var_val l then 
               (label := !label ^ "\n" ^ x ^ ":\n" ^ var_val;
                acc)
             else false
           with Not_found -> false) true !var_l in
       if b then 
         begin
           (G.V.label v).vertex_mode <- VarChange;
           (G.V.label v).num_label <- (G.V.label v).num_label  ^ !label
         end
     );
     G.add_edge_e !graph e;
     Ed_display.add_edge canvas_root (n, v) (G.E.label e);
     set_edge_event e;
     ignore (Model.add_edge n v))
  with Not_found ->
    match !root with
      |None -> failwith "pb None"
      |Some x ->
        let e = G.E.create x (make_edge_info_label "" true) v in
        (G.V.label v).var_map <- build_map (Var_Map.empty) v after mode new_name;
        if not !mode then failwith "false";
        (G.V.label v).vertex_mode <- Unsafe;
        G.add_edge_e !graph e;
        Ed_display.add_edge canvas_root (x, v) (G.E.label e);
        set_edge_event e;
        ignore (Model.add_edge x v)
          
          
let create_node s unsafe_l  =
  let pos = Str.search_forward (Str.regexp "=") s 0 in
  let transition_list = Str.global_replace (Str.regexp "[\n| ]+") ""
    (String.trim (Str.string_before s pos)) in
  let var_values = Str.split (Str.regexp "&&") (Str.string_after s (pos + 1)) in
  let name = node_name var_values in
  let v =
    (** Si un seul etat unsafe et node courant = unsafe *)
    if !cpt = 1 && unsafe_l = 1  then
      (let vertex = G.V.create (make_node_info (string_of_int !cpt) name true) in
       root := Some vertex;
       ignore (Model.add_vertex_unsafe vertex);
       vertex)
    (** Si plusieurs etats unsafe et node courant = unsafe *)
    else if !cpt <= unsafe_l then
      (let vertex = G.V.create (make_node_info (string_of_int !cpt) name true) in
       ignore (Model.add_vertex_unsafe vertex);
       vertex)
    else
      (** Si node courant <> unsafe *)
      (let vertex = G.V.create (make_node_info (string_of_int !cpt) name true) in
       ignore (Model.add_vertex vertex);
       vertex) in
  link_node transition_list v var_values;
  (G.V.label v).label <- (G.V.label v).num_label;
  HT.add ht transition_list v;
  G.add_vertex !graph v;
  if (G.V.label v).vertex_mode = VarChange then
    color_edges v !root;
  Ed_display.add_node canvas_root v;
  !set_vertex_event_fun v;
  let tor = make_turtle !origine 0.0 in
  draw tor canvas_root vc renderer;
  incr cpt;
  Thread.delay 0.001

let rec list_to_node curr_node unsafe_l = function
  |[] -> ()
  |[x] ->
    (** Si == alors fin de la description des nodes *)
    (try
       let pos = Str.search_forward (Str.regexp "==") x 0 in
       let node_list = Str.string_before x pos in
       create_node node_list unsafe_l;
       raise End_trace
     with Not_found -> (curr_node := !curr_node ^ x))
  |x::s ->
    (** On complète curr_node et on crée un noeud *)
    curr_node := !curr_node ^ x;
    create_node !curr_node unsafe_l;
    (** Reinit curr_node *)
    curr_node := "";
    list_to_node curr_node unsafe_l s
   
   
let rec build_node curr_node str unsafe_l  =
  let str_l = Str.split (Str.regexp "node [0-9]+:") str in
  match str_l with
    |[] -> ()
    |[x] ->
      if !curr_node <> "" then
        create_node !curr_node unsafe_l;
      curr_node := x
    |x::s ->
      list_to_node curr_node unsafe_l str_l
       

(** Crée arbre à partir de la file *) 

let load_graph unsafe_l =
  try
    let curr_node = ref "" in
    while true do
      try
        if !kill_thread then raise KillThread;
        Mutex.lock m;
        while Queue.length graph_trace = 0 do
          Condition.wait c m
        done;
        let str = Queue.pop graph_trace in
        Mutex.unlock m;
        if Str.string_match (Str.regexp "==") str 0 then
          (build_node curr_node str unsafe_l ;
           raise End_trace)
        else if Str.string_match (Str.regexp "node [0-9]+:") str 0 then
          build_node curr_node str unsafe_l
        else
          curr_node := !curr_node ^ str
      with Queue.Empty ->  Mutex.unlock m;
    done
  with
    |End_trace -> (Mutex.lock m_end; end_load_graph := true;
                   Condition.signal c_end;
                   Mutex.unlock m_end)
    |KillThread -> ()


(** Met sortie cubicle dans la file *)

let show_tree file  =
  let ic = Unix.open_process_in ("cubicle -nocolor -v "^file) in
  try
    while true do
      if !kill_thread then raise KillThread;
      let s = input_line ic in
      Mutex.lock m;
      Queue.push (s^"\n") graph_trace;
      Condition.signal c;
      Mutex.unlock m;
    done
  with
    |End_of_file ->
      (ignore (Unix.close_process_in ic); 
       end_show_tree := true)
    |KillThread ->
      ignore (Unix.close_process_in ic)

(* let update_model () =  *)
(*   try *)
(*     while true do *)
(*       if !kill_thread || !end_show_tree || !end_load_graph then  *)
(*         raise KillThread; *)
(*       (\* Mutex.lock m_model; *\) *)
(*       (\* while Queue.length model = 0 do *\) *)
(*       (\*   Condition.wait c_model m *\) *)
(*         (\* done; *\) *)
(*         try *)
(*           Mutex.lock m_model;  *)
(*           let m = Queue.pop model in *)
(*           Mutex.unlock m_model;  *)
(*           (match m with *)
(*             |Node n -> (Model.add_vertex n; *)
(*                         Ed_display.add_node canvas_root n; *)
(*                         !set_vertex_event_fun n) *)
(*             |UnsafeNode n-> (Model.add_vertex_unsafe n; *)
(*                          Ed_display.add_node canvas_root n; *)
(*                          !set_vertex_event_fun n) *)
(*             |Edge (n1, n2) -> Model.add_edge n1 n2) *)
(*         with Queue.Empty -> (Printf.printf " " ; Mutex.unlock m_model); *)
(*     done  *)
(*   with  *)
(*     |KillThread -> (end_show_tree := false; end_load_graph := false; Mutex.unlock m_model) *)


let safe_or_unsafe () =
  while not (!end_load_graph && !end_show_tree) do
    Condition.wait c_end m
  done;
  let str = ref ""  in
  while Queue.length graph_trace <> 0 do
    str := !str ^ (Queue.pop graph_trace)
  done;
  (try
     (let _ = Str.search_forward (Str.regexp "UNSAFE") !str 0 in
      result_image#set_stock `DIALOG_ERROR;
      result_label#set_text "Unsafe")
   with Not_found ->
     (result_image#set_stock `APPLY;
      result_label#set_text "Safe"));
  end_load_graph := false;
  end_show_tree := false
    

let tree (file, unsafe_l) =
  Queue.clear graph_trace;
  ignore (Thread.create show_tree file);
  ignore (Thread.create load_graph unsafe_l) ;
  ignore (Thread.create safe_or_unsafe ())
    
let open_graph file unsafe_l =
  ignore (window#show ());
  Ed_graph.new_graph();
  set_canvas_event ();
  canvas#set_scroll_region ~x1:0. ~y1:0. ~x2:w ~y2:h ;
  ignore (stop_button#event#connect#button_press
            ~callback: (fun b -> kill_thread:= true; false));
  ignore (test_button#event#connect#button_press 
            ~callback: (fun b ->              
              path_between
                [("Exgntd", ["False"]); ("Curcmd", ["Reqs"])]  
                [("Curcmd", ["Reqe"])] !root;
              let tor = make_turtle !origine 0.0 in
              draw tor canvas_root vc renderer; true));
  GtkThread.async (fun () -> tree (file, unsafe_l)) ();
  draw (make_turtle_origine ()) canvas_root vc renderer;
  GtkThread.main ()
    

let init file nb_unsafe = 
  kill_thread := false;
  reset_table_and_canvas ();
  Ed_graph.new_graph ();
  cpt := 1;
  Model.reset();
  if nb_unsafe > 1 then
    (let v = (G.V.create (make_node_info "   " "   " true )) in
     root := Some v;
     G.add_vertex !graph v;
     Ed_display.add_node canvas_root v;
     !set_vertex_event_fun v;
     ignore (Model.add_vertex v))
  else
    root := None;
  open_graph file nb_unsafe
