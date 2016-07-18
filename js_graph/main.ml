open Ed_graph
open Ed_hyper 
open Ed_display

module Html = Dom_html

let json : < parse : Js.js_string Js.t -> 'a> Js.t = Js.Unsafe.pure_js_expr "JSON"

let root = ref (choose_root ())

let refresh = ref 0

let load_graph f =
  Ed_graph.load_graph f;
  root := choose_root ()

let create_canvas w h =
  let d = Html.window##document in
  let c = Html.createCanvas d in
  c##width <- w;
  c##height <- h;
  c

let draw_ellipse c w h  =  
  c##save ();
  let scale = 2. in
  let line_w = 2. in
  c##scale (2., 1.);
  c##beginPath();
  let pi = 4. *. (atan 1.) in
   c##translate ((float w)/.(2.*.scale), (float h)/.2.);
  c##arc(0., 0., ((float w)/.(2. *. scale)) -. (2. *. line_w), 0., 2.*.pi, Js.bool false);
  c##restore();
   (* c##translate(0., 0.); *)
   (* c##scale (1., 1.); *)
  c##lineWidth <- line_w;
  c##strokeStyle <- Js.string "black";
  c##stroke ()


let draw tortue c w h  = 
  match !root with
    |None -> Firebug.console##log (Js.string "none!");
    |Some r ->
      Ed_draw.draw_graph r tortue;
      Ed_display.draw_graph root c w h
  (* let pi = 4. *. (atan 1.) in  *)
  (* let w, h = float w, float h in  *)
  (* (\* c##beginPath(); *\) *)
  (* c##translate (w/.2., h/.2.); *)
  (* (\* c##moveTo(100., 150.); *\) *)
  (* (\* c##lineTo(450., 50.); *\) *)
  (* c##arc(0., 0., 50., 0., 2. *. pi, Js.bool false); *)
  (* c##restore(); *)
  (* c##lineWidth <- 5.; *)
  (* c##strokeStyle <- Js.string "ff0000"; *)
  (* c##stroke () *)

let refresh_draw canvas w h  = 
  refresh := 0;
  let tor = make_turtle !origine 0.0 in 
  draw tor canvas w h 
          
 
let start _ = 
  let doc = Html.document in
  let page = doc##documentElement in
  page##style##overflow <- Js.string "hidden";
  page##style##height <- Js.string "100%";
  doc##body##style##overflow <- Js.string "hidden";
  doc##body##style##margin <- Js.string "0px";
  doc##body##style##height <- Js.string "100%";
  let w = page##clientWidth in
  let h = page##clientHeight in
  let canvas = create_canvas w h in 
  let c  = canvas##getContext (Dom_html._2d_) in 
  Dom.appendChild doc##body canvas;
  Html.window##onresize <- Html.handler
    (fun _ ->
      let page = doc##documentElement in
      let w = page##clientWidth in
      let h = page##clientHeight in
      if w <> canvas##width || h <> canvas##height then
        begin
          canvas##width <- w;
          canvas##height <- h;
          Ed_display.w := float w;
          Ed_display.h := float h;
          draw_ellipse c w h;
          refresh_draw c w h
        end;
      Js._false
    );
  (* G.iter_vertex (fun v -> *)
  (*   let c = canvas##getContext (Html._2d_) in *)
  (*   let w = 100 in *)
  (*   let h = 100 in *)
  (*   let scale = 2. in *)
  (*   let line_w = 2. in *)
  (*   c##scale (2., 1.); *)
  (*   c##beginPath(); *)
  (*   let pi = 4. *. (atan 1.) in *)
  (*   c##arc(0., 0., ((float w)/.(2. *. scale)) -. (2. *. line_w), 0., 2.*.pi, Js.bool false); *)
  (*   c##lineWidth <- line_w; *)
  (*   c##strokeStyle <- Js.string "black"; *)
  (*   c##stroke ())!graph; *)
  draw_ellipse c  w h;
  Firebug.console##log (Js.string "appelle draw display");
  draw (make_turtle_origine ()) c w h 

let start _ =
  try
    (* let txt = (Html.createTextarea (Html.window##document)) in *)
    (* txt##value <- Js.string "Hello"; *)
    start ();
    Js._false
  with Html.Canvas_not_available ->
    Js._false
      
let _ = 
  (* load_graph "divisors12.gml"; *)
  Firebug.console##log (Js.string "dans le main");
  let vertex = G.V.create (make_node_info "test" "test") in
  G.add_vertex !graph vertex;
  let vertex2 = G.V.create (make_node_info "test" "test") in
  G.add_vertex !graph vertex2;
  let vertex3 = G.V.create (make_node_info "test" "test") in
  G.add_vertex !graph vertex3;
  let vertex4 = G.V.create (make_node_info "test" "test") in
  G.add_vertex !graph vertex4;
  let vertex5 = G.V.create (make_node_info "test" "test") in
  G.add_vertex !graph vertex5;
  G.add_edge_e !graph (G.E.create vertex (make_edge_info ()) vertex2);
  G.add_edge_e !graph (G.E.create vertex (make_edge_info ()) vertex3);
  G.add_edge_e !graph (G.E.create vertex2 (make_edge_info ()) vertex4);
  G.add_edge_e !graph (G.E.create vertex2 (make_edge_info ()) vertex5);
  root := Some vertex;
  Firebug.console##log (Js.string "add vertex");
  Html.window##onload <- Html.handler start
