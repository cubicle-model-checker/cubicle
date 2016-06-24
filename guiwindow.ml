open Psystem_parser
open Gdk.Color
open GdkEvent.Button
open Ed_tracegraph
open Lexing
open Options
open Format


exception CursorNotOverText 
exception FileError
exception KillThread

let last_search_iter = ref None 

let kill_thread = ref false

let wd = if gui_debug then 1600 else 1000

module M = Map.Make (String)


let var_l = ref M.empty 

let window =
  let _ = GMain.init () in
  let wnd = GWindow.window 
    ~title:"Cubicle GUI" 
    ~position:`CENTER 
    ~resizable:true 
    ~width:wd ~height:800 () in 
  let _ = wnd#connect#destroy ~callback:(GMain.quit) in
  wnd 

let cubicle  = 
  let manager = GSourceView2.source_language_manager ~default:true in 
  match manager#language "cubicle" with 
  | None -> None
  | some -> some

let box = GPack.vbox ~packing:window#add ()

let toolbox_frame = GBin.frame ~border_width:8 ~packing:(box#pack ~expand:false ~fill:false) ()

let toolbox = GPack.hbox ~packing:(toolbox_frame#add) ()

let toolbar =
  let t = GButton.toolbar ~tooltips:true ~packing:toolbox#add ()
  in t#set_icon_size `DIALOG; t

let run_button = toolbar#insert_button
  ~text:" Run Cubicle"
  ~icon:(GMisc.image ~stock:`EXECUTE ~icon_size:`LARGE_TOOLBAR ())#coerce ()
  
let stop_button =
  toolbar#insert_button
    ~text:" Abort"
    ~icon:(GMisc.image ~stock:`STOP  ~icon_size:`LARGE_TOOLBAR())#coerce ()

let save_button = toolbar#insert_button
  ~text:" Save"
  ~icon:(GMisc.image ~stock:`SAVE ~icon_size:`LARGE_TOOLBAR ())#coerce ()

let edit_button = toolbar#insert_toggle_button
          ~text:" Edit File"
          ~icon:(GMisc.image ~stock:`EDIT ~icon_size:`LARGE_TOOLBAR ())#coerce ()
   
let resultbox, result_image, result_label =
  toolbar#insert_space ();
  let hbox = GPack.hbox () in
  let result_image = GMisc.image ~icon_size:`LARGE_TOOLBAR
     ~packing:hbox#add () in
  let result_label = GMisc.label ~text:" " ~packing:hbox#add () in
  ignore(toolbar#insert_widget hbox#coerce); hbox, result_image, result_label

let toolsearch =
  let t =  GButton.toolbar ~tooltips:true ~packing:(toolbox#pack ~fill:true) () in
  t#set_icon_size `DIALOG; t

let search_box =
  let sb = GPack.hbox ~spacing:5 ~border_width:5 () in
  ignore(GMisc.image ~icon_size:`LARGE_TOOLBAR
	   ~stock:`FIND ~packing:sb#add ());sb

let search_bar =
  let sb = GEdit.entry ~packing:(search_box#add) () in
  ignore (toolsearch#insert_widget search_box#coerce); sb

let next_button = toolsearch#insert_button
  ~text:" Next"
  ~icon:(GMisc.image ~stock:`GO_DOWN ~icon_size:`SMALL_TOOLBAR())#coerce ()

let previous_button = toolsearch#insert_button
  ~text:" Previous"
  ~icon:(GMisc.image ~stock:`GO_UP ~icon_size:`SMALL_TOOLBAR())#coerce ()
                                              
let trace_button = GButton.button ~label:"Trace" 
  ~packing:(toolbox#add) ()

(** Debug mode *)
let show_file_button = GButton.button ~label:"Show new file"
  ~packing:(toolbox#add (* ~expand:false ~fill:false *)) ~show:(gui_debug)()

(** Debug mode *)
let execute_button2 = GButton.button ~label:"Run original file"
  ~packing:(toolbox#add) ~show:(gui_debug)()
  
let debug_box = GPack.hbox ~packing:box#add ()

let source_box1 = GPack.vbox ~packing:(debug_box#pack ~expand:true ~fill:true) ()

(** Debug mode *)
let source_box2 = GPack.vbox ~packing:debug_box#add ~show:(gui_debug)() 

let source_frame1 = GBin.frame  ~border_width:10  ~packing:(source_box1#pack) ()

let source_frame2 = GBin.frame  ~border_width:10  ~packing:(source_box2#pack) ()

let e_box = GBin.event_box ~height:500 ~packing:(source_frame1#add) ()

(** Debug mode *)
let e_box2 = GBin.event_box ~height:500 ~packing:(source_frame2#add) ()
 
let result_frame = GBin.frame ~border_width:10 ~packing:(source_box1#pack ~expand:true ~fill:true) ()

let result_frame2 = GBin.frame ~border_width:10 ~packing:(source_box2#pack ~expand:true ~fill:true) ()

let result_scroll = GBin.scrolled_window 
  ~hpolicy:`ALWAYS 
  ~vpolicy:`ALWAYS 
  ~border_width:5
  ~packing: result_frame#add()

let result_text1 =  
  let t = GSourceView2.source_view 
    ~packing:result_scroll#add () in 
  t#set_editable false;
  t#set_cursor_visible false;
  t

let scroll = GBin.scrolled_window 
  ~hpolicy:`ALWAYS 
  ~vpolicy:`ALWAYS 
  ~packing: e_box#add ()

(** Debug mode *)
let scroll2 = GBin.scrolled_window 
  ~hpolicy:`ALWAYS 
  ~vpolicy:`ALWAYS 
  ~packing: e_box2#add  () 

(** Debug mode *)
let result_scroll2 = GBin.scrolled_window 
  ~hpolicy:`ALWAYS 
  ~vpolicy:`ALWAYS 
  ~border_width:5
  ~packing: result_frame2#add () 

(** Debug mode *)
let result_text2 =  GSourceView2.source_view 
  ~packing:result_scroll2#add ()

let source = 
  let src = GSourceView2.source_view 
    ~auto_indent:true 
    ~indent_on_tab:true
    ~indent_width:2 
    ~insert_spaces_instead_of_tabs:true 
    ~right_margin_position:80 
    ~border_width:5
    ~show_line_numbers:true 
    ~packing:scroll#add () in 
  src#misc#modify_font_by_name "Monospace"; 
  let buf = src#source_buffer in 
  if cubicle <> None then 
    buf#set_language cubicle; 
  buf#set_highlight_syntax true; 
  src 

let save_session s file b = 
  parse_linact !s;
  let l = !inact_l in
  let oc = open_out file in 
  if l == [] then Printf.fprintf oc "vide" else
    List.iter (fun (s, e) -> Printf.fprintf oc "%d %d " s e) l;
  close_out oc;
  true

let confirm s file e =
  (if GToolbox.question_box
    ~title:"Save session" ~buttons:["Cancel"; "Save"]
    ~default:2 ~icon:(GMisc.image ~stock:`SAVE  ~icon_size:`DIALOG ())
    "Would you like to save the session ?" = 2 then
      let _ = save_session s file e in ());
  false
 
let list_to_string l  =  
  List.fold_right (fun x acc -> acc ^ x ^ "\n") l ""

let add_value_var l = 
  List.iter (fun (x, e) -> 
    if e#text = "" then 
      Ed_main.var_l := (x, None)::!Ed_main.var_l
    else
      let str_l = Str.split (Str.regexp ";") e#text in 
      Ed_main.var_l := (x, Some (str_l))::!Ed_main.var_l) l

let select_var l new_path ast =
  let t_edit_l = ref [] in
  let wnd = GWindow.window
    ~title:"Watch variables"
    ~position:`CENTER
    ~resizable:false ()  in
  let v_box = GPack.vbox
    ~border_width:5
    ~packing:(wnd#add) () in
  let table_fr = GBin.frame
    ~border_width:10
    ~packing:(v_box#pack ~expand:true ~fill:true) () in
  let table = GPack.table
    ~columns:2
    ~rows:(List.length !Ed_main.var_l)
    ~row_spacings:5
    ~col_spacings:10
    ~packing:(table_fr#add) () in
  let cpt = ref 0 in
  M.iter (fun x y ->
    let label = GMisc.label ~text:x () in
    let text_entry = GEdit.entry () in
    t_edit_l := (x, text_entry) :: !t_edit_l;
    table#attach 0 !cpt (label#coerce);
    table#attach 1 !cpt (text_entry#coerce);
    incr cpt) !var_l ;
  let button_box = GPack.button_box
    ~packing:(v_box#pack) `HORIZONTAL () in
  let button_cancel = GButton.button
    ~label:"Cancel"
    ~stock:`CANCEL
    ~packing:(button_box#add)() in
  let button_show = GButton.button
    ~label:"Show Graph"
    ~stock:`APPLY
    ~packing:(button_box#add)() in
  ignore (button_show#event#connect#button_press 
            ~callback:(fun b -> 
              add_value_var !t_edit_l;
              wnd#destroy ();
              Ed_main.init new_path (punsafe_length (!ast)); true));
  ignore (button_cancel#event#connect#button_press
            ~callback:(fun b -> wnd#destroy (); true));
  wnd#show ()


let select_var_none new_path ast =
  if GToolbox.question_box
    ~title:"List" ~buttons:["Add"; "Show trace"]
    ~default:2
    ~icon:(GMisc.image ~stock:`DIALOG_QUESTION  ~icon_size:`DIALOG ())
     "No variables.\n(Add with right click)" = 2 then
    Ed_main.init new_path (punsafe_length (!ast))

  
(* Debug mode*)
let source2 = 
  let src = GSourceView2.source_view 
    ~auto_indent:true 
    ~indent_on_tab:true
    ~indent_width:2 
    ~insert_spaces_instead_of_tabs:true 
    ~right_margin_position:80 
    ~border_width:5
    ~show_line_numbers:true 
    ~packing:scroll2#add () in 
  src#misc#modify_font_by_name "Monospace"; 
  src#set_editable false;
  let buf = src#source_buffer in 
  buf#set_language cubicle; 
  buf#set_highlight_syntax true; 
  src 
    
let read_file path =
  let c_in = open_in path in
  let str = really_input_string c_in (in_channel_length c_in) in
  Glib.Convert.locale_to_utf8 str

let get_mouse_coordinates m =
  let mouse_x = truncate (GdkEvent.Motion.x m) in
  let mouse_y = truncate (GdkEvent.Motion.y m) in 
  mouse_x, mouse_y

(** Envoie a Psystem_parser la position courante du curseur dans le buffer *)
let get_buffer_coordinates m = 
  let mouse_x, mouse_y = get_mouse_coordinates m in 
  let buffer_x, buffer_y = source#window_to_buffer_coords `TEXT mouse_x mouse_y in 
  let iter = source#get_iter_at_location buffer_x buffer_y in 
  if not iter#inside_sentence then 
    (buffer_l := -1;
     buffer_c := -1;
     raise CursorNotOverText);
  buffer_l := 1 + iter#line; 
  buffer_c := iter#offset

let rec apply_tag = function 
  |[] -> ()
  |(t_id, start, stop)::s -> 
    let start_iter = source#source_buffer#get_iter (`OFFSET start) in 
    let stop_iter = source#source_buffer#get_iter (`OFFSET stop) in 
    (match t_id with 
    |Comment ->  
      source#source_buffer#apply_tag_by_name "delete"
        ~start:start_iter ~stop:stop_iter;
      source#source_buffer#apply_tag_by_name "dark"
        ~start:start_iter ~stop:stop_iter;
    |Hover -> 
      source#source_buffer#apply_tag_by_name "gray_background" 
        ~start:start_iter ~stop:stop_iter; apply_tag s
    |UndoComment -> 
      source#source_buffer#remove_tag_by_name "delete"
        ~start:start_iter ~stop:stop_iter;
      source#source_buffer#remove_tag_by_name "dark"
        ~start:start_iter ~stop:stop_iter
    |UndoHover -> 
      source#source_buffer#remove_tag_by_name "gray_background" 
        ~start:start_iter ~stop:stop_iter
    |Var -> 
      begin
        source#source_buffer#apply_tag_by_name "var"
          ~start:start_iter ~stop:stop_iter;
        let str =  (source#source_buffer#get_text ~start:start_iter ~stop:stop_iter() ) in
        if M.mem str !var_l then 
          (let (be, en) = M.find str !var_l in
            if be = start && en = stop then
              var_l := M.remove str !var_l ;
            source#source_buffer#remove_tag_by_name "var"
              ~start:start_iter ~stop:stop_iter)
        else 
          var_l := M.add str (start, stop) !var_l          
      (* let m =  Ed_main.Var_L.add (Ed_main.var_l) in () *)
        (* Ed_main.var_l := (source#source_buffer#get_text ~start:start_iter ~stop:stop_iter() ) :: !Ed_main.var_l *)
      end
);
    apply_tag s

(** Parcourt l'AST pour trouver dans les bornes de quelle loc se trouve le curseur *)
let find_in_ast s edit m  = 
  if !edit then 
    false
  else 
    try 
      get_buffer_coordinates m;
      apply_tag (parse_psystem !s);
      false
    with CursorNotOverText  -> (apply_tag (cancel_last_visited ()); false)

(** Appelé après un clic de souris pour commenter *)
let modify_ast ast edit b = 
    if !edit then false
    else 
      if (GdkEvent.Button.button b) = 3 && !buffer_l <> -1 && !buffer_c <> -1 then 
        (apply_tag (parse_var !ast); true)
      else 
        (if !buffer_l <> -1 && !buffer_c <> -1 then
            apply_tag (parse_psystem_m !ast );
         true)

(** Sauvegarde du fichier envoyé à Cubicle *)      
let save_execute_file s file b =
  let oc = open_out file in
  Printf.fprintf oc "%s" (Psystem_printer.psystem_to_string !s);
  close_out oc;
  true

let show_file s new_name save_name b = 
  let _ = save_session s save_name new_name in
  source2#source_buffer#set_text (read_file new_name);
  true

(** Appelé après edit sur le fichier, indique erreurs dans le fichier *)
let open_show_file ast new_file edit = 
  let ic = open_in new_file in
  let lb = from_channel ic in
  (try 
     ast := Parser.system Lexer.token lb;
     source#source_buffer#set_text (read_file new_file);
     edit := false;
   with 
   |Parsing.Parse_error -> 
     let (start, stop) = (lexeme_start lb, lexeme_end lb) in
     let start_iter = source#source_buffer#get_iter (`OFFSET start) in 
     let stop_iter = source#source_buffer#get_iter (`OFFSET stop) in 
     source#source_buffer#apply_tag_by_name "error" 
       ~start:start_iter ~stop:stop_iter;
     result_text1#buffer#set_text "syntax error";
     close_in ic;
     raise FileError
   |Lexer.Lexical_error s ->
     let (start, stop) = (lexeme_start lb, lexeme_end lb) in
     let start_iter = source#source_buffer#get_iter (`OFFSET start) in 
     let stop_iter = source#source_buffer#get_iter (`OFFSET stop) in 
     source#source_buffer#apply_tag_by_name "error" 
       ~start:start_iter ~stop:stop_iter;
     result_text1#buffer#set_text ("lexical error : "^s);
     close_in ic;
     raise FileError
   |Typing.Error (e,loc) ->
     let (start, stop) = (lexeme_start lb, lexeme_end lb) in
     let start_iter = source#source_buffer#get_iter (`OFFSET start) in
     let stop_iter = source#source_buffer#get_iter (`OFFSET stop) in
     source#source_buffer#apply_tag_by_name "error"
       ~start:start_iter ~stop:stop_iter;
     result_text1#buffer#set_text ("typing error : ");
     close_in ic;
     raise FileError)  

(** Autorise les modifications quand on entre dans le mode edition,
   parse et affiche le fichier, interdit les modifications en sortant du mode edition *) 
let edit_mode ast new_file button edit m =
  if button#active then 
    ( edit := true;
      (*source#source_buffer#set_text (Psystem_printer.psystem_to_string !ast);*)
      source#set_editable true;
      source#set_cursor_visible true; )
  else 
    ( let oc = open_out new_file in
      let str =  source#source_buffer#get_text  () in 
      Printf.fprintf oc "%s" str;
      close_out oc;
      try
        (open_show_file ast new_file edit;
         result_text1#buffer#set_text "")
      with FileError -> button#set_active true)

let safe_or_unsafe () = 
  let str = result_text1#buffer#get_text () in 
  try 
    (let _ = Str.search_forward (Str.regexp "UNSAFE") str 0 in
    result_image#set_stock `DIALOG_ERROR;
    result_label#set_text "Unsafe" )
  with Not_found ->
    (result_image#set_stock `APPLY;
     result_label#set_text "Safe")
      
let get_trace (buffer, file) = 
  let ic = Unix.open_process_in ("cubicle -nocolor "^file) in
  result_text1#buffer#set_text "";
  try
    while true do
      if !kill_thread then
        (kill_thread := false;
         raise KillThread);
      let s = (input_line ic)^"\n" in
      result_text1#buffer#insert s;
      ignore (result_text1#scroll_to_iter ~use_align:true ~yalign:0.5 (result_text1#buffer#end_iter))
    done
  with
  |End_of_file ->
    (ignore (Unix.close_process_in ic);
     safe_or_unsafe ())
  |KillThread -> ignore (Unix.close_process_in ic) 

  
let execute buffer file b  =
  ignore (Thread.create get_trace (buffer, file))

let search b = 
  let start_iter = source#source_buffer#start_iter in 
  let stop_iter = source#source_buffer#end_iter in
  let last_search = ref start_iter in
  let str = search_bar#text in
  source#source_buffer#remove_tag_by_name "search"
    ~start:start_iter ~stop:stop_iter;
  source#source_buffer#remove_tag_by_name "search_next"
    ~start:start_iter ~stop:stop_iter;
  let rec f () =  
    let search_res = !last_search#forward_search str in
    match search_res with 
    |None -> ()
    |Some (start, stop) -> 
      (source#source_buffer#apply_tag_by_name "search"
         ~start:start ~stop:stop; last_search := stop;   last_search_iter := None;
       f ()) in 
  f()

let search_next b = 
  let start_iter = source#source_buffer#start_iter in
  let stop_iter = source#source_buffer#end_iter in
  let s_iter =  
  match !last_search_iter with
    |None -> start_iter
    |Some (_, x) -> x in
  let str = search_bar#text in
  source#source_buffer#remove_tag_by_name "search_next"
    ~start:start_iter ~stop:stop_iter;
  let search_res = s_iter#forward_search str in
  (match search_res with 
  |None -> last_search_iter := None 
  |Some (start, stop) ->
    last_search_iter := Some (start, stop);
    ignore (source#scroll_to_iter ~use_align:true ~yalign:0.5 start);
    source#source_buffer#apply_tag_by_name "search_next"
      ~start:start ~stop:stop);
  true

let search_previous b = 
  let start_iter = source#source_buffer#start_iter in
  let stop_iter = source#source_buffer#end_iter in
  let s_iter = match !last_search_iter with 
    |None -> stop_iter
    |Some (x,_) -> x in 
  let str = search_bar#text in
  source#source_buffer#remove_tag_by_name "search_next"
    ~start:start_iter ~stop:stop_iter;
  let search_res = s_iter#backward_search str in
  (match search_res with 
  |None -> last_search_iter := None 
  |Some (start, stop) -> 
    last_search_iter := Some (start, stop);
    ignore (source#scroll_to_iter ~use_align:true ~yalign:0.5 stop);
    source#source_buffer#apply_tag_by_name "search_next"
      ~start:start ~stop:stop);
  true

(** Coordonées fichier sauvegarde session *)
let rec list_position l = 
  match l with 
    |[] |_::[] -> []
    |x::y::s -> (int_of_string x, int_of_string y)::list_position s

let open_file inter_path save_path ast = 
  (try
     let ic = open_in inter_path in
     let lb = from_channel ic in
     ast := Parser.system Lexer.token lb;
     close_in ic;
     let str = read_file save_path in 
     let fl = Str.split (Str.regexp "[ \t]+") str in
     let pos_l = list_position fl in
     inact_l := pos_l;
     parse_init !ast;
     source#source_buffer#set_text (read_file inter_path);
     apply_tag (parse_psystem !ast);
   with Sys_error(_) -> Printf.printf "pas de fichier %s" inter_path);;


let open_window s  = 
  let ast = ref s in
  let edit = ref false in 
  let file_name = Options.file in 
  let new_path = (String.sub file_name 0 ((String.length file_name) - 4))^"mod.cub" in
  let save_path = (String.sub file_name 0 ((String.length file_name) - 4))^"save" in
  let inter_path = (String.sub file_name 0 ((String.length file_name) - 4))^"inter.cub" in
  source#source_buffer#set_text (read_file file_name); 
  let map = Gdk.Color.get_system_colormap () in 
  let light_gray = Gdk.Color.alloc ~colormap:map (`NAME "light gray") in
  let gray = Gdk.Color.alloc ~colormap:map (`NAME "gray") in 
  ignore (source#source_buffer#create_tag 
            ~name:"gray_background" [`BACKGROUND_GDK light_gray]);
  ignore (source#source_buffer#create_tag ~name:"delete" [`BACKGROUND_GDK light_gray]);
  ignore (source#source_buffer#create_tag ~name:"dark" [`FOREGROUND_GDK gray]);
  ignore (source#source_buffer#create_tag ~name:"error" [`BACKGROUND "red"]);
  ignore (source#source_buffer#create_tag ~name:"search" [`BACKGROUND "yellow"]);
  ignore (source#source_buffer#create_tag ~name:"search_next" [`BACKGROUND "orange"]);
  ignore (source#source_buffer#create_tag ~name:"var" [`BACKGROUND "pink"]);
  source#event#add [`BUTTON_PRESS; `KEY_PRESS];   
  source#set_editable false;
  open_file inter_path save_path ast;
  ignore (source#event#connect#motion_notify ~callback:(find_in_ast ast edit));
  ignore (source#event#connect#button_press ~callback:(modify_ast ast edit));
  ignore (save_button#event#connect#button_press 
            ~callback:(save_session ast save_path));
  ignore (run_button#connect#clicked 
            ~callback:(fun b -> 
              let _ = save_execute_file ast new_path b in 
              execute result_text1#buffer new_path b));
  ignore (execute_button2#event#connect#button_press
            ~callback:(fun b -> execute result_text2#buffer file_name b; true));
  ignore (edit_button#connect#toggled
            ~callback:(edit_mode ast inter_path edit_button edit));
  ignore (search_bar#connect#changed
            ~callback:(search));
  ignore (next_button#event#connect#button_press

            ~callback:(search_next));
  ignore (previous_button#event#connect#button_press
            ~callback:(search_previous));
  ignore (show_file_button#event#connect#button_press 
            ~callback: (fun b -> source2#source_buffer#set_text (Psystem_printer.psystem_to_string !ast); true));
  ignore (stop_button#event#connect#button_press
            ~callback: (fun b -> kill_thread:= true; true));
  ignore (trace_button#event#connect#button_press ~callback: (fun b ->
    let _ = save_execute_file ast new_path b in  
    Ed_main.var_l := [];
    if M.cardinal !var_l = 0 then 
      select_var_none new_path ast
    else  
      select_var !Ed_main.var_l new_path ast; true)); 
  ignore (window#event#connect#delete (confirm ast save_path));
  window#show ();
  GtkThread.main ()

