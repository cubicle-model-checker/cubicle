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

open Ed_hyper
open Ed_graph

let nodes = H.create 500
let edges = H2.create 500

let nodes_pos = ref []
     
let label_edges_pos = ref []

let font = "lighter 17pt DejaVu Sans Mono"

let last_rectangle = ref None 

let create_canvas w h =
  let d = Dom_html.window##document in
  let c = Dom_html.createCanvas d in
  c##width <- w;
  c##height <- h;
  c

let screen_transform canvas =
  let w = canvas##width in
  let h = canvas##height in

  let rx = float w /. 2. in
  let ry = float h /. 2. in
  let dx = float w /. 2. in
  let dy = float h /. 2. in
  let rx = max 5. (rx (* -. offset *)) in
  let ry = max 5. (ry (* -. offset *)) in
(rx, ry, dx, dy)

let debug = ref false


let text_size_div =
  let doc = Dom_html.document in
  lazy
    (let d = Dom_html.createDiv doc in
     d##style##visibility <- Js.string "hidden";
     d##style##position <- Js.string "absolute";
     d##style##whiteSpace <- Js.string "nowrap";
     Dom.appendChild (doc##body) d;
     d)

let text_size font txt =
  let doc = Dom_html.document in
  let d = Lazy.force text_size_div in
  d##style##font <- font;
  let txt = doc##createTextNode (Js.string txt) in
  Dom.appendChild d txt;
  let res = (d##clientWidth, d##clientHeight) in
  Dom.removeChild d txt;
  res

let opt_style v default = Js.Optdef.get v (fun () -> default)

(* Original window size *)
let w = ref 1200.
let h = ref 800.
(* let (w,h) = ref (1200., 800.) *)

(* differents definitions *)
let color_circle = ""

let color_intern_edge = "grey69"
let color_successor_edge = "#bdbdbd" (* "grey38" *) (* "grey38" *)
let color_vertex = "#c0c0c0"


let color_varchange = "#98cfd6"
let color_varchange_focused = "#98cfd6"

let color_line_varchange = "#c35959" (* "#79a3a8" *) (* "red" *)

let color_initvar = "#9c98b1"
let color_initvar_focused = "#9c98b1"

let color_init = "#12FF00"

let color_unsafe = "#e93b3b"
let color_unsafe_focused = "#e93b3b"

let color_selected_intern_edge = "#9f1a1a" (* "#74885e" *)
let color_selected_successor_edge = "#9f1a1a"
let color_selected_vertex = "#9f1a1a"

let color_focused_intern_edge = "#4d51a9"
let color_focused_successor_edge = (* "#4d51a9" *) "#6d6d6d"
let color_focused_vertex =  "#4d51a9"

let color_selected_focused_intern_edge= "#e80000"
let color_selected_focused_vertex ="#e80000"
let color_selected_focused_successor_edge = "#e80000"

let color_text = "black"
let width_successor_edge = 2
let width_intern_edge = 2
let point_size_text = 20.


let get_edge_display = function 
  |Normal -> (color_successor_edge, false)
  |Selected -> (color_selected_successor_edge, false)
  |Focused -> (color_focused_successor_edge, false)
  |Selected_Focused -> (color_selected_focused_successor_edge, false)
  |HighlightPath | HighlightPath_Focused | InitPath -> (color_line_varchange, true)
  |Path -> ("#66ff66", false)
  |_ -> (color_successor_edge, false)

let get_vertex_display = function 
  |Normal -> (color_vertex, 0.5)
  |Selected -> (color_selected_vertex, 0.5)
  |Focused -> (color_focused_vertex, 2.5)
  |Selected_Focused -> (color_selected_focused_vertex, 2.5)
  |Init -> (color_init, 0.5)  
  |Init_Focused -> (color_unsafe, 2.5) 
  |Unsafe -> (color_unsafe, 0.5)
  |Unsafe_Focused -> (color_unsafe_focused, 2.5)
  |VarChange -> (color_varchange, 0.5)
  |VarChange_Focused -> (color_varchange_focused, 2.5)
  |_ -> (color_vertex, 0.5)

(* let get_vertex_color = function  *)
(*   |Normal ->  *)
(*   |Selected ->  *)
(*   |Selected_Focused ->  *)
(*   |HighlightPath | InitPath ->  *)
(*   |HighlightPath_Focused  *)
(*   |Path *)
(*   |_ ->  *)
  
let drawEllipse cx cy w h c mode = 
  c##beginPath();
  c##moveTo (cx, cy -. h/.2.);
  c##bezierCurveTo (cx +. (w/.2.), cy -. (h/.2.), cx +. (w/.2.), cy +. (h/.2.), cx, cy +. h/.2.);
  c##bezierCurveTo (cx -. w/.2., cy +. h/.2., cx -. w/.2., cy -. h/.2., cx, cy -. h/.2.);
  let (color, line_width) = get_vertex_display mode in 
  c##fillStyle <- (Js.string color);
  c##fill();
  c##lineWidth <- line_width;
  c##strokeStyle <- Js.string "black";
  c##stroke ();
  c##closePath()
   

(* GTK to hyperbolic coordinates *)
let to_turtle(x,y)=
  let zx,zy as r = ((float x*.(2./.(!w)) -. 1.),(1. -. float y *.(2./.(!h)))) in
  let zn = sqrt(zx*.zx +. zy*.zy) in
  if zn > rlimit then
    (rlimit*.zx/.zn, rlimit*.zy/.zn)
  else
    r

(* Hyperbolic to GTK coordinates *)
let from_turtle (x,y) =
  let screen_size = Printf.sprintf "screen size : %f, %f\n" !w !h in 
  let xzoom = (!w/.2.)
  and yzoom = (!h/.2.) in
  (truncate (x*.xzoom +. xzoom), truncate(yzoom -. y*.yzoom))


(* the middle of the screen used when init a graoh drawing *)
let start_point = to_turtle (truncate(!w/.2.), truncate(!h/.2.))

(* origine is a reference to the start point drawing for the graph in GTK coordinates *)
let origine = ref start_point

(* Current point in Hyperbolic view with an initialization in center of hyperbolic circle *)
let current_point = ref (0,0)

(* Change hyperbolic current point *)
let moveto_gtk x y = current_point := (x,y)

(* Change hyperbolic current point with turtle coordinates *)
let tmoveto_gtk turtle = 
  let (x,y)= from_turtle turtle.pos in
  moveto_gtk x y

(* Create a turtle with origine's coordinates *)
let make_turtle_origine () = 
  let (x,y) = let (x,y) = !origine in (truncate x, truncate y) in  
  moveto_gtk  x y;
  make_turtle !origine 0.0

(* Append turtle coordinates to line, set current point and return the "new" line *)
let tlineto_gtk turtle line =
  tmoveto_gtk turtle; 
  let (x,y) = !current_point in 
  List.append line [(float x); (float y) ]

let split_list l r =
  let length = truncate((float (List.length l))/.r) in  
  let rec f cpt = function
    |[] -> []
    |x::s when cpt >= length && cpt mod 2 = 0 -> []
    |x::s -> x::(f (cpt+1) s)
  in
 f 0 l

(* Set line points for a distance with a number of steps, 
   set current point to last line's point, by side-effect of tlineto_gtk,
   and return the final turtle *)
let draw_successor_edge e turtle distance steps c = 
  let src, dst = G.E.src e, G.E.dst e in
  let line = H2.find edges (src, dst) in
  let d = distance /. (float steps) in
  let rec list_points turtle liste = function
    | 0 -> (turtle,liste)
    | n ->let turt = advance turtle d in
          list_points turt (tlineto_gtk turt liste) (n-1)
  in
  let start =
    let (x,y) = from_turtle turtle.pos in
    [(float (x)); (float (y))] in
  let _,lpoints = list_points turtle start steps in
  let factor = (shrink_factor turtle.pos) in
  let r = factor *. point_size_text *. 0.03 in
  let points = Array.of_list lpoints in
  let l = truncate (float (Array.length points) /. 2.2) in
  let (x, y) =
    if l mod 2 = 0 then (l, l+1) else (l+1, l) in
  c##beginPath ();
  let (color, array) = get_edge_display (G.E.label e).edge_mode in 
  c##strokeStyle <- (Js.string color);
  c##lineWidth <- 2.;
  c##moveTo (points.(0), points.(1));
  for i = 2 to (Array.length points) - 1 do
    if i mod 2 = 0 then
      begin
        c##lineTo (points.(i), points.(i + 1));
        c##moveTo (points.(i), points.(i + 1))
      end
  done;

  c##stroke();
  c##closePath();
  if (G.E.label e).visible_label then 
    begin 
      match line with
        |(_,[],_) -> failwith "pb draw_successor_edge ed_display"
        |(o, [t], pos) ->
          let tw = (float t##width) *. r (* *. factor *. 0.8 *)  in
          let th = (float t##height) *. r (* *. factor *. 0.8  *)in
          c##drawImage_fromCanvasWithSize
            (t, points.(x) -. ( tw /. 2.) , points.(y) -. (th /. 2.) +. 30., tw , th);
          label_edges_pos := 
            {tx = points.(x) ; ty = points.(y) +. 30.;
              width = tw; height = th; edge = e } :: !label_edges_pos;
        |_ -> failwith "pb draw_successor_edge ed_display";
    end
      
      
  (* draw_line c (List.tl lpoints); *)
  (* c##stroke (); *)


type polaire = { radius : float; angle : float}
type cartesien = { x : float; y: float}

let pol_to_cart p =
  { 
    x = p.radius *. (cos p.angle);
    y = p.radius *. (sin p.angle)
  }

let cart_to_pol p =
  let radius = sqrt((p.x *. p.x) +.(p.y *. p.y)) in
  {
    radius = radius;
    angle = 2. *. ath ((p.y /. radius) /. (1. +. p.x /. radius))
  }

let test_rectangle x y vertex = 
  if float x > !w/.2. -. 80. && float x < !w/.2. +. 80.
    && float y > !h/.2. -. 60. && float y < !h/.2. +. 60.
  then
    begin
     ( match !last_rectangle with
        |None -> ()
        |Some node ->
          (let v = G.V.label node in
             v.label <- v.num_label;
             v.label_mode <- Num_Label;
           G.iter_succ_e (fun x -> let e = G.E.label x in
                                   e.visible_label <- false) !graph node));
          let v = G.V.label vertex in
      if v.label_mode = Num_Label then
        (v.label <- v.str_label;
         v.label_mode <- Str_Label;
         last_rectangle := Some vertex ;
         G.iter_succ_e (fun x -> let e = G.E.label x in
                                 e.visible_label <- true) !graph vertex);

    end

let tdraw_string_gtk v turtle c =
  let node_info = H.find nodes v in
  tmoveto_gtk turtle;
  let vertex = G.V.label v in
  let factor = (shrink_factor ((G.V.label v).turtle.pos)) in
  let r = factor *. point_size_text *. 0.03 in 
  let (x,y) = !current_point in 
  test_rectangle x y v;
  print_debug  (Js.string (G.V.label v).label);
  print_debug (x,y);
  let txt = 
    if vertex.label_mode = Num_Label then node_info.num
    else node_info.str in
  match txt with 
  |(_, [], _) -> failwith "pb tdraw_string_gtk in ed_display"
    |(o, [t], pos) -> 
    let tw = (float t##width) *. r (* *. factor *. 0.8 *)  in 
    let th = (float t##height) *. r(* *. factor *. 0.8  *)in 
    drawEllipse (float x) (float y) (tw +. 20.) (th +. 8.) c vertex.vertex_mode;
    c##drawImage_fromCanvasWithSize
      (t, float x -. ( tw /. 2.) , float y -. (th /. 2.), tw , th);
    nodes_pos :=(x, y, (tw +. th +. 28.)/. 4., v):: !nodes_pos;
    if vertex.label_mode = Num_Label then
      H.replace nodes v {node_info with num =  (o, [t], (x, y))}
    else 
      H.replace nodes v {node_info with str =  (o, [t], (x, y))}
  |(Some max_w, l, pos) -> 
    let fst::_ = l in 
    let max_tw = max_w *. r in
    let th = (float fst##height) *.r in 
    let lgth = List.length l in 
    let y_init = 
      if lgth mod 2 = 0 then
        (float y) -.((float(lgth/2)) *. th) 
      else 
        (float y) -. (float (lgth/2) +. 0.5) *. th in
    drawEllipse (float x) (float y) (max_tw +. 62.) (th *. float lgth +. 28.) c vertex.vertex_mode;
    List.iteri (fun i txt ->
      let tw = (float txt##width) *. r   in 
      let th = (float txt##height) *. r in 
      c##drawImage_fromCanvasWithSize
        (txt, float x -. ( max_tw /. 2.) , y_init  +. ((float i *. th) (* /. 2. *)), tw , th )) l;
    nodes_pos := (x, y, ((max_tw +. 16.) +. (th *. float lgth)) /. 4., v)::!nodes_pos;
    if vertex.label_mode = Num_Label then
      H.replace nodes v {node_info with num =  (Some max_w, l, (x,y))}
    else 
      H.replace nodes v {node_info with str =  (Some max_w, l, (x,y))}
    |_ -> ()
  
  
let compute_text s font = 
  let (w, h) = text_size (Js.string font) s in 
  let tdebug = Printf.sprintf "(%d, %d)\n" w h in 
  let w, h = w + 8, h + 8 in 
  let canvas = create_canvas w h in  
  let c = canvas##getContext (Dom_html._2d_) in 
  c##fillStyle <- Js.string "black";
  c##textAlign <- Js.string "center";
  c##textBaseline <- Js.string "middle";
  c##font <- Js.string font;
  c##fillText (Js.string s, float w /. 2., float h /. 2.);  
  canvas

let compute_multiline_text s font arr_lines = 
  let lines_l = ref [] in 
  let lgth = arr_lines##length in 
  let max_width = ref 0 in 
  for i = 0 to lgth - 1 do 
    let t = (Js.Optdef.get (Js.array_get arr_lines i) (fun () -> failwith "pb add_node optdef")) in
    let (w, h) = text_size (Js.string font) (Js.to_string t) in 
    let tdebug = Printf.sprintf "(%d, %d)\n" w h in 
      let w, h = w + 8, h + 8 in 
      let canvas = create_canvas w h in  
      let c = canvas##getContext (Dom_html._2d_) in 
      c##fillStyle <- Js.string "black";
      c##textAlign <- Js.string "center";
      c##textBaseline <- Js.string "middle";
      c##font <- Js.string font;
      if w > !max_width then max_width := w;
      c##fillText (t, float w /. 2., float h /. 2.);  
      lines_l := canvas :: !lines_l
  done;
  (!max_width, !lines_l)
   
let compute_node v label = 
  let lines = (Js.string label)##split (Js.string "\n") in 
  let arr_lines = Js.str_array lines in
  if arr_lines##length = 1 then 
    let canvas = compute_text label font in 
     None, [canvas], (0, 0);
  else 
    let max_width, lines = compute_multiline_text label font arr_lines in 
    (Some (float max_width), lines, (0, 0))


let add_node vertex = 
  let v = G.V.label vertex in
  H.add nodes vertex {str = compute_node v v.str_label; num = compute_node v v.num_label}

  
let add_edge edge font = 
  let e = G.E.label edge in
  let v = G.E.src edge in 
  let w = G.E.dst edge in 
  let vw = (v, w) in 
  let s = e.label in 
  let lines = (Js.string s)##split (Js.string "\n") in 
  let arr_lines = Js.str_array lines in
  if arr_lines##length = 1 then 
    let (w, h) = text_size (Js.string font) s in 
    let tdebug = Printf.sprintf "(%d, %d)\n" w h in 
    let w, h = w + 8, h + 8 in 
    let canvas = create_canvas w h in  
    let c = canvas##getContext (Dom_html._2d_) in 
    c##fillStyle <- Js.string "black";
    c##textAlign <- Js.string "center";
    c##textBaseline <- Js.string "middle";
    c##font <- Js.string font;
    c##fillText (Js.string s, float w /. 2., float h /. 2.);  
    H2.add edges vw (None, [canvas],(0, 0))
  else 
    let lines_l = ref [] in 
    let lgth = arr_lines##length in 
    let max_width = ref 0 in 
    for i = 0 to lgth - 1 do 
      let t = (Js.Optdef.get (Js.array_get arr_lines i) (fun () -> failwith "pb add_node optdef")) in
      let (w, h) = text_size (Js.string font) (Js.to_string t) in 
      let tdebug = Printf.sprintf "(%d, %d)\n" w h in 
      let w, h = w + 8, h + 8 in 
      let canvas = create_canvas w h in  
      let c = canvas##getContext (Dom_html._2d_) in 
      c##fillStyle <- Js.string "black";
      c##textAlign <- Js.string "center";
      c##textBaseline <- Js.string "middle";
      c##font <- Js.string font;
      if w > !max_width then max_width := w;
      c##fillText (t, float w /. 2., float h /. 2.);  
      lines_l := canvas :: !lines_l
    done;
    H2.add edges vw  (Some (float !max_width), !lines_l, (0, 0))

(* set origine to new mouse position and return associated turtle *)
let motion_turtle v (* mx1 my1 *) mx2 my2  = 
  let label = H.find nodes v in 
  let (_, _, (mx1, my1)) = 
    if (G.V.label v).label_mode = Str_Label then 
      label.str
    else 
      label.num
  in
  let z1 = to_turtle (mx1, my1) in
  let z2 = to_turtle (mx2, my2) in
  let (x,y) = drag_origin !origine z1 z2 in
  origine := (x,y);
  make_turtle !origine 0.0

        
(* graph drawing *)
let draw_graph root c =
  nodes_pos := [];
  label_edges_pos := [];
  (* G.iter_edges_e *)
  (*   (fun edge -> *)
  (*     let ( e : edge_info) = G.E.label edge in *)
  (*        draw_successor_edge edge e.edge_turtle e.edge_distance e.edge_steps c; *)
  (*   )!graph; *)
  
  G.iter_vertex
    (fun v ->
      let ( l : node_info) = G.V.label v in
      if l.visible = Visible then
        begin
          G.iter_succ_e 
            (fun  edge -> 
              let ( e : edge_info) = G.E.label edge in
              draw_successor_edge edge e.edge_turtle e.edge_distance e.edge_steps c) 
            !graph v;
          tdraw_string_gtk v l.turtle c               
        end 
 )!graph

    
let rec color_edges v root path_t =  
  match root with 
    |None -> ()
    |Some r -> 
      if r <> v then 
        begin
          G.iter_pred_e (fun edge ->
            (G.E.label edge).edge_mode <- path_t) !graph v;
          G.iter_pred (fun vertex -> color_edges vertex root path_t) !graph v;
        end



let set_path paths root = 
  List.iter ( fun p -> 
    List.iter (fun e -> (G.E.label e).edge_mode <- Path) p;
    try 
      let src_e = List.hd p in 
      let src_node = G.E.src src_e in 
      color_edges src_node root HighlightPath
    with Failure(_) -> ()
  ) paths


let path_between src_mode dst_mode  root =
  (** Pour tous les noeuds dans l'etat mode dst *)
  let dst_nodes  = find_nodes dst_mode in
  (** Pour tous les pred de ces noeuds *)
  List.iter (fun n ->
    let edge_list = G.pred_e !graph n in
    List.iter (fun e ->
      let paths = ref [] in
      (** On récupère les chemins partants de ces noeuds qui mène vers un noeud
          dans l'etat mode src *)
      get_path src_mode dst_mode [] e paths;
      set_path !paths root
    ) edge_list
  ) dst_nodes

let path_to src_node dst_mode root = 
  List.iter (fun e -> 
    let paths = ref [] in 
    get_path_to dst_mode [] e paths;
    (* set_path_to !paths ; *)
  ) (G.succ_e !graph src_node)



let color_path paths = 
  List.iter ( fun p ->
    List.iter (fun (e, m) -> (G.E.label e).edge_mode <- m ) p ) paths

let path_to e dst_mode root  = 
  let src_node = G.E.dst e in
  List.iter (fun e -> 
    (* Thread.delay 0.00001; *)
     (* print_newline(); *)
    if ((G.E.label e).edge_mode <> Path) then
      begin
        let paths = ref [] in 
        get_path_to dst_mode [] e paths;
        color_path !paths
      end
   ) (G.succ_e !graph src_node)
     


let reset_display () (* canvas *) = 
  G.iter_vertex (fun v -> 
    let vertex = (G.V.label v) in  
    (match vertex.vertex_mode with 
      |Unsafe | Normal | Init -> ()
      |_ -> vertex.vertex_mode <- Normal);
    vertex.label <- vertex.num_label;
  )
 !graph;
  G.iter_edges_e (fun e ->
    match   (G.E.label e).edge_mode with 
    |InitPath -> () 
    |_ -> 
      (G.E.label e).edge_mode <- Normal;
      (G.E.label e).label <- (G.E.label e).mem_label
  ) !graph
    
