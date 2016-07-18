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
(**************************************************************************)

(* This file is a contribution of Benjamin Vadon *)

open Format
open Ed_hyper
open Ed_graph
open Ed_display
open Ed_model



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


let ed_name = "Cubicle Trace View"


let canvas = 
  (GnoCanvas.canvas 
     ~aa:!aa 
     ~width:(truncate w)
     ~height:(truncate h)
     ~packing:(h_box#pack ~fill:true ~expand:true) ()  ~border_width:20) 

(* unit circle as roots of graph drawing *)
let (canvas_root, focus_rectangle) =
  let circle_group = GnoCanvas.group ~x:(w/.2.) ~y:(h/.2.) canvas#root in
  circle_group#lower_to_bottom ();
  let w2 = 2. in
  let circle = GnoCanvas.ellipse 
    ~props:[ `X1 (-.w/.2. +. w2); `Y1 (-.h/.2. +. w2); 
             `X2 (  w/.2. -. w2); `Y2 ( h/.2. -. w2) ;
             `FILL_COLOR color_circle ; `OUTLINE_COLOR "black"; 
             `WIDTH_PIXELS (truncate w2) ] circle_group 
  in circle_group#lower_to_bottom ();
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
    | Some r -> 
      try 
        Ed_draw.draw_graph r tortue;
        let center_node = Ed_display.draw_graph !root canvas in
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
      with Not_found -> ()

        
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

let refresh_display () =
  ignore (Ed_display.draw_graph !root canvas_root)

(* usual function ref, for vertex event *)
let set_vertex_event_fun = ref (fun _ -> ())


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
            let turtle = motion_turtle ellipse ev in
            draw turtle canvas_root vc renderer;
              end
        end
    | `BUTTON_PRESS ev -> () 
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

let edge_event texte arrow_line label src ev =
  begin
    match ev with
      | `ENTER_NOTIFY _ -> 
        texte#grab_focus ();
        texte#set [`WEIGHT 1000];
        ignore (Ed_display.draw_graph !root canvas_root)

      | `LEAVE_NOTIFY ev ->
        if not (Gdk.Convert.test_modifier `BUTTON1 (GdkEvent.Crossing.state ev))
        then begin
          texte#set [`FILL_COLOR "black"; `WEIGHT 400]; 
          ignore (Ed_display.draw_graph !root canvas_root)
       end
      | `BUTTON_RELEASE ev ->
        texte#ungrab (GdkEvent.Button.time ev);
      | `TWO_BUTTON_PRESS ev->
        if (GdkEvent.Button.button ev) = 1
        then 
          (mem_vertex := Some src;
           !scroll_to_transition label)       
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
  let _, arrow_line, texte = 
    H2.find successor_edges (src, dst) in 
  ignore (texte#connect#event ~callback:(edge_event texte arrow_line label e))

let () = set_vertex_event_fun := set_vertex_event

let set_canvas_event () =
  (* ignore(canvas_root#parent#connect#event ~callback:(fun e -> false)); *)
  G.iter_vertex set_vertex_event !graph;
  G.iter_edges_e (set_edge_event) !graph

(* reset *)

let reset_table_and_canvas () =
  let l = canvas_root#get_items in
  List.iter (fun v -> trace v#destroy ()) l;
  H2.clear intern_edges;
  H2.clear successor_edges;
  (* reset_display canvas_root; *)
  origine := start_point;
  nb_selected := 0
    
