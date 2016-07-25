open Ed_graph
open Ed_hyper 
open Ed_display

module Html = Dom_html

exception Match of string * Ed_graph.condition * string 

exception Found of (G.V.t * int * int)

exception End_trace 

exception KillThread

exception Found_label of G.E.t

let cpt = ref 1

let var_l = ref []

let mode_change = ref false

let context = ref None

let mode_value = ref false

let json : < parse : Js.js_string Js.t -> 'a> Js.t = Js.Unsafe.pure_js_expr "JSON"

let root = ref (choose_root ())

let refresh = ref 0

let end_load_graph = ref false

let sdiv z s = { x = z.x /. s; y = z.y /. s }

let sq_norm c = c.x *. c.x +. c.y *. c.y

let norm c = sqrt (sq_norm c)

module HTString  =
  (struct
    type t = string
    let equal x y = (String.trim x) = (String.trim y)
    let hash x  = Hashtbl.hash x
   end)

module HT = Hashtbl.Make (HTString)

let ht = HT.create 500

(* let screen_transform c *)
(*   Ed_graph.load_graph f; *)
(*   root := choose_root () *)

let do_refresh () =
  !refresh mod !refresh_rate = 0
  
let draw_ellipse c w h=  
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
  c##stroke ();
  c##closePath()


let draw turtle c rect = 
  match !root with
    |None -> print_debug (Js.string "none!");
    |Some r ->
      c##clearRect (0., 0., !w, !h);
      Ed_draw.draw_graph r turtle;
      if rect then 
        begin 
          c##beginPath ();
          c##fillStyle <- Js.string "#e0e0e0";
          c##fillRect (!w/.2. -. 80., !h/.2. -. 60.,  160., 120.);
          c##closePath();
        end ;
      Ed_display.draw_graph root c
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

let refresh_draw c rect = 
  refresh := 0;
  let tor = make_turtle !origine 0.0 in 
  draw tor c rect
          
 
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
  Ed_display.w := float w;
  Ed_display.h := float h;
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
          canvas##width <- w ;
          canvas##height <- h ;
          Ed_display.w := float w ;
          Ed_display.h := float h ;
          draw_ellipse c w h ;
          refresh_draw c false
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
  (* draw_ellipse c  w h; *)
  (* print_debug (Js.string "appelle draw display"); *)
  draw (make_turtle_origine ()) c false;
  canvas


let dist xa ya xb yb = 
  sqrt ((xb -. xa) *. (xb -. xa) +. (yb -. ya) *. (yb -. ya))

let handle_drag element move stop click =
  let fuzz = 4 in
  element##onmousedown <- Html.handler
    (fun ev ->
       let x0 = ev##clientX and y0 = ev##clientY in
       let started = ref false in
       let node = 
         try 
           List.iter (fun (x, y, r, v) -> 
             if dist (float x) (float y) (float x0) (float y0) <= r then 
               raise (Found (v, x, y))) !nodes_pos;
           None
         with Found(v, _, _) -> Some v
       in match node with 
         |None -> Js._true
         |Some v -> 
           let c1 =
             Html.addEventListener Html.document Html.Event.mousemove
               (Html.handler
                  (fun ev ->
                 let x = ev##clientX and y = ev##clientY in
                 if
                   not !started && (abs (x - x0) > fuzz || abs (y - y0) > fuzz)
                 then begin
                   started := true;
                   element##style##cursor <- Js.string "move"
                 end;
                 if !started then move v x0 y0 x y;
                 Html.stopPropagation ev;
                 Js._true))
           Js._true
       in
       let c2 = ref Js.null in
       c2 := Js.some
         (Html.addEventListener Html.document Html.Event.mouseup
            (Html.handler
               (fun ev ->
                  Html.removeEventListener c1;
                  Js.Opt.iter !c2 Html.removeEventListener;
                  if !started then begin
                    element##style##cursor <- Js.string "";
                    stop ev##clientX ev##clientY
                  end else
                    click ev##clientX ev##clientY;
                  Js._true))
            Js._true);
Js._true)

let string_before str i =
  if i < 0 || i >= (Js.string str)##length then
    raise (Invalid_argument "index out of bounds")
  else
    let s = (Js.string str)##slice (0, i) in
    Js.to_string s

let string_after str i =
  if i < 0 || i >= (Js.string str)##length then
    raise (Invalid_argument "index out of bounds")
  else
    let js_str = Js.string str in
    let s = js_str##slice (i, js_str##length) in
    Js.to_string s

let search_forward r s pos = 
  match Regexp.search_forward (Regexp.regexp r) s pos with
  |None -> raise Not_found
  |Some (i, _) -> i

let find_node ev last_visited canvas = 
  let x0 = ev##clientX and y0 = ev##clientY in
  let node = 
    try 
      List.iter (fun (x, y, r, v) -> 
        if dist (float x) (float y) (float x0) (float y0) <= r then 
          raise (Found (v, x, y))) !nodes_pos;
      None
    with Found(v, x, y) -> Some (v, x, y)
  in
  (match node with 
  |None ->
    (match !last_visited with 
    |None -> ()
    |Some v -> 
      begin 
        last_visited := None;
        update_vertex v Unfocus;
        refresh_draw (canvas##getContext (Dom_html._2d_)) false;
      end);
  |Some (vertex, x, y) -> 
    begin
      last_visited := Some vertex;
      update_vertex vertex Focus; 
      refresh_draw (canvas##getContext (Dom_html._2d_)) false;
    end)

let find_label ev last_visited canvas = 
  let x0 = ev##clientX and y0 = ev##clientY in
  let label = 
    try 
      List.iter (fun x -> 
        let x0 = ev##clientX and y0 = ev##clientY in
        if (float x0 >= x.tx -. x.width /. 2.) && (float x0 <= x.tx +. x.width /. 2.) 
          && (float y0 >= x.ty -. x.height /. 2.) && (float y0 <= x.ty +. x.height /. 2.) then 
          raise (Found_label (x.edge))) !label_edges_pos;
      None
    with Found_label(e) -> Some e
  in
  (match label with 
  |None ->
    (match !last_visited with 
    |None -> ()
    |Some e -> 
      begin 
        let src, dst = G.E.src e, G.E.dst e in
        last_visited := None;
        H2.remove edges (src, dst); 
        Ed_display.add_edge e Ed_display.font;
        refresh_draw (canvas##getContext (Dom_html._2d_)) false
      end);
  |Some e -> 
    begin
      let src, dst = G.E.src e , G.E.dst e in
      last_visited := Some e;
      H2.remove edges (src, dst); 
      add_edge e "600 18pt sans-serif" ;
      refresh_draw (canvas##getContext (Dom_html._2d_)) false;
    end)


let match_atom x sep length t = 
  try 
    let pos = search_forward sep x 0 in
    let before = Regexp.global_replace (Regexp.regexp "[\n|\r|\s| ]+") 
      (string_before x pos) "" in
    let after =  Regexp.global_replace (Regexp.regexp "[\n|\r|\s| ]+") 
      (string_after x (pos + length)) "" in
    try
      ignore (float_of_string before);
      raise (Match (after, t , before))
    with Failure(_) -> 
      raise (Match (before, t , after))
  with Not_found -> () 
    
let get_expr e = 
  try 
      match_atom e ">=" 2  Ed_graph.GreaterEq;
      match_atom e "<=" 2  Ed_graph.LessEq;
      match_atom e "<>" 2  Ed_graph.NEq;
      match_atom e ">"  1  Ed_graph.Greater;
      match_atom e "<"  1  Ed_graph.Less;
      match_atom e "="  1  Ed_graph.Eq;
      failwith "problem with trace format"
  with Match(a, t, b) -> (a, t, b) 

let split_node_info x m v changed_l mode new_name =
  let var_find_or before after  =
    List.fold_left (fun acc (x, (var_i,_)) ->
      match var_i with 
        |[] -> 
          (if x = before  then
              true
           else
              try
                let pos = search_forward "\\[" before 0 in
                let array_name = Regexp.global_replace (Regexp.regexp "[\n|\s|\r| ]+") 
                  (string_before before pos) "" in
                if array_name = x then
                  true
                else acc
              with Not_found -> acc)
        |l ->  
          if x = before then
            List.mem after l
          else
            try
              let pos = search_forward "\\[" before 0 in
              let array_name = Regexp.global_replace (Regexp.regexp "[\n| ]+") 
                (string_before before pos) "" in
              if array_name = x && List.mem after l then
                true
              else  acc
            with Not_found ->  acc) false !var_l
  in   
  (let before, t, after = get_expr x in
   let m =
     try
       if !mode_change then 
         (let (a, _) = Var_Map.find before m in
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
   (before, t, after, m))
    
let rec build_map m v l mode new_name=
  (* let var_init before after m =  *)
  (*   if not (Var_Map.mem before m) &&  *)
  (*     List.fold_left (fun acc (x, vars) -> *)
  (*       match vars with  *)
  (*       |[] ->  *)
  (*         if x = before then true else acc *)
  (*       |var_l ->  *)
  (*           if x = before && List.mem after var_l then true else acc *)
  (*     ) false !var_l then  *)
  (*     ((G.V.label v).vertex_mode <- VarInit; *)
  (*      (G.V.label v).num_label <-  *)
  (*        (G.V.label v).num_label ^ "\n" ^ before ^ " <- " ^ after); *)
  (* in *) 
  let changed_l = ref "" in
  match l with
    |[] -> m
    |y::[] ->
      (match Regexp.split (Regexp.regexp "\\n") (String.trim y) with
        |[] -> failwith "pb format trace 2"
        |x::_ ->
          (try
             let before, t, after, m = split_node_info x m v changed_l mode new_name in
             (* var_init before after m; *)
             Var_Map.add before (after, t) m
           with Not_found -> failwith "erreur build map"))
    |x::s ->
      try
        let before, t,  after, m = split_node_info x m v changed_l mode new_name in
        (* var_init before after m; *)
        build_map (Var_Map.add before (after, t) m) v s mode new_name
      with Not_found -> failwith "erreur build map"
        
        
let rec node_name = function
  |[] -> ""
  |x::[] ->
    (match Regexp.split (Regexp.regexp "[\\n|\\r]") (String.trim x) with
      |[] -> failwith "pb format trace 2"
      |y::_ ->  y)
  |x::s -> (String.trim x)^"\n"^(node_name s)
    
let link_node before v after  =
  (* print_debug (Js.string "AFTER"); *)
  (* print_debug (Js.string after) *)
  let mode = ref true in 
  let new_name = ref "" in
  try
    (let arrow_pos = search_forward  "->" before 0 in
     (* print_debug (Js.string (string_of_int (arrow_pos))); *)
     let transition = string_before before arrow_pos in
     (* print_debug (Js.string ("Transition bef :"^transition)); *)
     let node = Regexp.global_replace (Regexp.regexp "(\n| )+")
       (string_after before (arrow_pos + 2)) "" in
     (* print_debug (Js.string ("Node :"^node)); *)
     let n = HT.find ht node in
     (* print_debug (Js.string ("TRANSITION NAME :"^transition)); *)
     let e = G.E.create n (make_edge_info_label transition true) v in
     (* print_debug (Js.string "transition name \n"); *)
     (* print_debug (Js.string (transition^"\n")); *)
     let map = build_map (Var_Map.empty)(* (G.V.label n).var_map *) v after mode new_name in 
     (G.V.label v).var_map <- map;
     if !mode_value then 
       (let label = ref "" in 
        let b = List.fold_left (fun acc (x, (var_i,_)) -> 
       match var_i with 
         |[]-> false
         |l -> 
           try
             let (var_val, _) = Var_Map.find x map in
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
     Ed_display.add_edge e (Ed_display.font)
)
  with Not_found -> 
    match !root with
      |None -> failwith "pb None"
      |Some x ->
        print_debug (Js.string "not found link node");
        let e = G.E.create x (make_edge_info_label "" true) v in
        (G.V.label v).var_map <- build_map (Var_Map.empty) v after mode new_name;
        if not !mode then failwith "false";
        (G.V.label v).vertex_mode <- Unsafe;
        G.add_edge_e !graph e;
        Ed_display.add_edge e (Ed_display.font)
          
          
let create_node s unsafe_l =
  (* Printf.printf "create node %s\n" s; *)
  print_debug (Js.string ("create node :"^s));
  let pos = search_forward ("=") s 0 in
  (* print_debug (Js.string ("list transitions "^ (String.trim (string_before s pos)))); *)
  let transition_list = Regexp.global_replace (Regexp.regexp " |\n|\r") 
    (String.trim (string_before s pos)) "" in
  (* print_debug (Js.string ("list transitions "^ transition_list)); *)
  let var_values = Regexp.split (Regexp.regexp "&&") (string_after s (pos + 1)) in
  let name = node_name var_values in
  let (v, unsafe) =
    if !cpt = 1 && unsafe_l = 1  then
      (let vertex = G.V.create (make_node_info (string_of_int !cpt) name) in
       root := Some vertex;
       (vertex, true))
    (** Si plusieurs etats unsafe et node courant = unsafe *)
    else if !cpt <= unsafe_l then
      (let vertex = G.V.create (make_node_info (string_of_int !cpt) name) in
       (vertex, true))
    else
      (** Si node courant <> unsafe *)
      (let vertex = G.V.create (make_node_info (string_of_int !cpt) name) in
       (vertex, false)) in
  link_node transition_list v var_values;
  (G.V.label v).label <- (G.V.label v).num_label;
  print_debug (Js.string transition_list);
  HT.add ht transition_list v;
  G.add_vertex !graph v;
  if (G.V.label v).vertex_mode = VarChange || (G.V.label v).vertex_mode = Init then
    color_edges v !root HighlightPath;
  Ed_display.add_node v;
  (match !context with 
  |None -> ()
  |Some c -> 
    refresh_draw c false);
  incr cpt;
   v

let rec list_to_node curr_node unsafe_l = function
  |[] -> ()
  |[x] ->
    (** Si == alors fin de la description des nodes *)
    (try
       let pos = search_forward ("==") x 0 in
       let node_list = string_before x pos in
       ignore (create_node node_list unsafe_l);
       raise End_trace
     with Not_found -> (curr_node := !curr_node ^ x))
  |x::s ->
    (** On complète curr_node et on crée un noeud *)
    curr_node := !curr_node ^ x;
    ignore (create_node !curr_node unsafe_l);
    (** Reinit curr_node *)
    curr_node := "";
    list_to_node curr_node unsafe_l s
   

let remove_empty_str l = 
  List.fold_left (fun acc x -> if x = "" then acc else x::acc) [] l
   
let rec build_node curr_node str unsafe_l  =
  let str_l = remove_empty_str (Regexp.split (Regexp.regexp "node [0-9]+:") str) in
  (* print_debug (Js.string "BUILDNODE"); *)
  (* print_debug (Js.string ("STR : "^str)); *)
  (* print_debug (Js.string ("CURR NODE : *"^(!curr_node)^"*")); *)
  (* print_debug (Js.string "BUILDNODE"); *)
  match str_l with
  |[] -> ()
    |[x] ->
      (* print_debug (Js.string ("curr_node dans build_node"^(!curr_node))); *)
      if !curr_node <> "" then
        ignore (create_node !curr_node unsafe_l);
      curr_node := x
    |x::s ->
      List.iter (fun x -> print_debug (Js.string ("print_list : *"^x^"*"))) str_l;
      (* print_debug (Js.string ("mult l curr_node dans build_node"^(!curr_node))); *)
      list_to_node curr_node unsafe_l str_l

let get_storage () =
  match Js.Optdef.to_option Dom_html.window##localStorage with
  | None -> (print_debug (Js.string "storage not found") ; raise Not_found)
  | Some t -> t 

     
  
let rec f (l, i, curr_node, unsafe_l, str) =
  (* print_debug (Js.string "dans f"); *)
  (* try *)
    (* print_debug (Js.string (str)); *)
    if (Regexp.string_match (Regexp.regexp "==") str 0) <> None then
      (build_node curr_node str unsafe_l ;
       raise End_trace)
    else if (Regexp.string_match (Regexp.regexp "node [0-9]+:") str 0) <> None then
      (build_node curr_node str unsafe_l)
    else
      curr_node := !curr_node ^ str
  (* with End_trace -> end_load_graph := true *)
       

let rec build_line (l, i, str, curr_node, unsafe_l) () = 
  (* print_debug (Js.string "dans build line"); *)
  (* Firebug.console##log (Js.string !str); *)
  try 
    (* Firebug.console##log (Js.string "build_line"); *)
  if l##length = 0 then 
    ignore (Html.window##setTimeout (Js.wrap_callback (build_line (l, i, str, curr_node, unsafe_l)), 0.))
  else
    begin 
      let key = Js.string (string_of_int i) in
      let s = l##getItem (key) in
      l##removeItem (key);
      let stro = Js.Opt.to_option s in
      match stro with
      |None -> ignore (Html.window##setTimeout (Js.wrap_callback (build_line (l, i, str, curr_node, unsafe_l)), 0.))
      |Some s ->
        let o_str = Js.to_string s in 
        str := !str ^ o_str;
        if (Regexp.string_match (Regexp.regexp "\n") o_str 0) <> None then
          ( f (l, i + 1, curr_node, unsafe_l, !str);
            str := "");
        ignore (Html.window##setTimeout (Js.wrap_callback (build_line (l, i + 1, str, curr_node, unsafe_l)), 0.))
    end
  with End_trace -> 
    (Firebug.console##log (Js.string "end load graph");
    (* ( *)
    (* let safe_str = ref "" in  *)
    (* for j = i to l##length do  *)
    (*   let key = Js.string (string_of_int i) in  *)
    (*   let s = l##getItem (key) in  *)
    (*   l##removeItem (key); *)
    (*   let stro = Js.Opt.to_option s in *)
    (*   match stro with *)
    (*     |None -> () *)
    (*     |Some s -> *)
    (*       let o_str = Js.to_string s in  *)
    (*       safe_str := !safe_str ^ o_str; *)
    (* done; *)
    (* if (Regexp.string_match (Regexp.regexp "==") str 0) <> None *)
    end_load_graph := true)
    
let load_graph unsafe_l =
  try
    (* print_debug (Js.string "load_graph"); *)
    let curr_node = ref "" in
    let str = ref "" in
    let l = get_storage () in
    ignore (build_line (l,1,str,curr_node, unsafe_l) ()) 
  with
  |End_trace -> end_load_graph := true
  |KillThread -> ()

let start _ =

  let last_node_visited = ref None in 
  let last_label_visited = ref None in
  try
    let canvas = start () in
    context := Some (canvas##getContext (Dom_html._2d_));
    let i = ref 0 in
  handle_drag canvas
      (fun v x0 y0 x1 y1 -> 
        incr refresh;
        if do_refresh()
        then 
          begin
            let turtle = motion_turtle v (* x y *) x1 y1 in
            let c  = canvas##getContext (Dom_html._2d_) in 
            draw turtle c true
        end
      ) (fun _ _ -> ()) (fun _ _ -> ());
    canvas##onmousemove <- Html.handler
      (fun ev ->      
        find_label ev last_label_visited canvas;
        find_node ev last_node_visited canvas;
        Js._false
        
);
    canvas##ondblclick <- Html.handler 
      (fun ev -> 
        match !last_node_visited with 
          |None -> Js._false
          |Some vertex -> 
            let v = G.V.label vertex in 
            if v.label_mode = Num_Label then
              (v.label <- v.str_label;
               v.label_mode <- Str_Label;
               G.iter_succ_e (fun x -> let e = G.E.label x in 
                                       e.visible_label <- true) !graph vertex)
            else
              (v.label <- v.num_label;
               v.label_mode <- Num_Label;
               G.iter_succ_e (fun x -> let e = G.E.label x in 
                                       e.visible_label <- false) !graph vertex);
            refresh_draw (canvas##getContext (Dom_html._2d_)) false;
           Js._false
      );
    (* let storageEvent = Dom_html.Event.make "storage" in  *)
    (* let ev_id = Dom_html.addEventListener Dom_html.window storageEvent *)
    (*   (Html.handler (fun ev ->  *)
    (*     let a = ev##key in  *)
    (*     print_debug (Js.string "storage event"); Js._false)) Js._false in *)
    (* print_debug (Js.string "dans start"); *)
    let l = get_storage () in 
    load_graph 1;
    Js._false;  
  with Html.Canvas_not_available ->
    Js._false

    (* let rec f () =  *)
    (*   if l##length <> 0 then  *)
    (*     begin *)
    (*       let key = Js.string (string_of_int !i) in  *)
    (*       let s = l##getItem (key) in  *)
    (*       l##removeItem (key); *)
    (*       incr i; *)
    (*       let str = Js.Opt.to_option s in *)
    (*       match str with  *)
    (*       |None -> raise Not_found *)
    (*       |Some s -> print_debug (s) *)
    (*     end; *)
    (*   if !i < 1000 then  *)
    (*     ignore (Html.window##setTimeout (Js.wrap_callback (f), 0.)) in *)
    (* (\* f (); *\) *)
      
let _ = 
  
  print_debug (Js.string "add vertex");
  Html.window##onload <- Html.handler ( Html.window##blur (); Html.window##focus(); start) 
