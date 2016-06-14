open Psystem_parser
open Gdk.Color
open GdkEvent.Button
open Lexing
open Options
open Format


exception NotBuffer

let last_search_iter = ref None 

let wd = if gui_debug then 1600 else 800 

let window =
  let _ = GMain.init () in
  let wnd = GWindow.window 
    ~title:"Cubicle GUI" 
    ~position:`CENTER 
    ~resizable:true 
    ~width:wd ~height:800 () in 
  let _ = wnd#connect#destroy (GMain.quit) in
  wnd 


let ocaml = 
  let manager = GSourceView2.source_language_manager ~default:true in 
  match manager#language "cubicle" with 
    | None -> failwith "La coloration syntaxique pour OCaml n'est pas disponible !" 
    | some -> some

let box = GPack.vbox ~packing:window#add ()

let button_box = GPack.hbox ~spacing:5 ~packing:(box#pack ~expand:false ~fill:false) ()

let execute_button = GButton.button ~label:"Run" ~stock:`EXECUTE ~packing:(button_box#pack ~expand:false ~fill:false)()

let show_file_button = GButton.button ~label:"Show new file" ~packing:(button_box#pack ~expand:false ~fill:false) ~show:(gui_debug)()

let execute_button2 = GButton.button ~label:"Run new file" ~packing:(button_box#pack ~expand:false ~fill:false) ~show:(gui_debug)()

let save_button = GButton.button ~label:"Save new file" ~stock:`SAVE ~packing:(button_box#pack ~expand:false ~fill:false)() 

let edit_button = GButton.toggle_button  ~stock:`EDIT ~packing:(button_box#pack ~expand:false ~fill:false)()

let search_bar = GEdit.entry ~packing:(button_box#pack  ~expand:false) ~width:150()

(* let search_button = GButton.button ~stock:`FIND ~packing:(button_box#pack) () *)

let next_button = GButton.button  ~stock:`GO_DOWN ~packing:(button_box#pack ~expand:false ~fill:false)()

let previous_button = GButton.button  ~stock:`GO_UP ~packing:(button_box#pack ~expand:false ~fill:false)()

let trace_button = GButton.button ~label:"trace" ~packing:(button_box#pack ~expand:false ~fill:false)()
  
let b = GPack.hbox ~packing:box#add ()

let b1 = GPack.vbox ~packing:b#add ()

let b2 = GPack.vbox ~packing:b#add ~show:(gui_debug)() 

let e_box = GBin.event_box ~height:600 ~packing:(b1#pack ~expand:false ~fill:false ) ()

let t_scroll = GBin.scrolled_window 
  ~hpolicy:`ALWAYS 
  ~vpolicy:`ALWAYS 
  ~packing: b1#add()

let text1 =  GSourceView2.source_view ~packing:t_scroll#add ()

let e_box2 = GBin.event_box ~height:600 ~packing:(b2#pack ~expand:false ~fill:false) ()

let t_scroll2 = GBin.scrolled_window 
  ~hpolicy:`ALWAYS 
  ~vpolicy:`ALWAYS 
  ~packing: b2#add () 

let text2 =  GSourceView2.source_view ~packing:t_scroll2#add ()

let scroll = GBin.scrolled_window 
  ~hpolicy:`ALWAYS 
  ~vpolicy:`ALWAYS 
  ~packing: e_box#add ()

let scroll2 = GBin.scrolled_window 
  ~hpolicy:`ALWAYS 
  ~vpolicy:`ALWAYS 
  ~packing: e_box2#add  () 
  
let source = 
  let src = GSourceView2.source_view 
    ~auto_indent:true 
    ~indent_on_tab:true
    ~indent_width:2 
    ~insert_spaces_instead_of_tabs:true 
    ~right_margin_position:80 
    ~show_line_numbers:true 
    ~packing:scroll#add () in 
  src#misc#modify_font_by_name "Monospace"; 
  let buf = src#source_buffer in 
  buf#set_language ocaml; 
  buf#set_highlight_syntax true; 
  src 
let source2 = 
  let src = GSourceView2.source_view 
    ~auto_indent:true 
    ~indent_on_tab:true
    ~indent_width:2 
    ~insert_spaces_instead_of_tabs:true 
    ~right_margin_position:80 
    ~show_line_numbers:true 
    ~packing:scroll2#add () in 
  src#misc#modify_font_by_name "Monospace"; 
  let buf = src#source_buffer in 
  buf#set_language ocaml; 
  buf#set_highlight_syntax true; 
  src 
    
let read_file path =
  let c_in = open_in path in
  let str = really_input_string c_in (in_channel_length c_in) in 
  Glib.Convert.locale_to_utf8 str

let read_channel c = 
  let str = really_input_string c (in_channel_length c) in 
  Glib.Convert.locale_to_utf8 str

let get_mouse_coordinates m =
  let mouse_x = truncate (GdkEvent.Motion.x m) in
  let mouse_y = truncate (GdkEvent.Motion.y m) in 
  mouse_x, mouse_y

let get_buffer_coordinates m = 
  let mouse_x, mouse_y = get_mouse_coordinates m in 
  let buffer_x, buffer_y = source#window_to_buffer_coords `TEXT mouse_x mouse_y in 
  let iter = source#get_iter_at_location buffer_x buffer_y in 
  buffer_l := 1 + iter#line; 
  buffer_c := iter#offset


let get_buffer_coordinates m = 
  let mouse_x, mouse_y = get_mouse_coordinates m in 
  let buffer_x, buffer_y = source#window_to_buffer_coords `TEXT mouse_x mouse_y in 
  let iter = source#get_iter_at_location buffer_x buffer_y in 
  if not iter#inside_sentence then 
    (buffer_l := -1;
     buffer_c := -1;
     raise NotBuffer);
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
      |UndoHover -> source#source_buffer#remove_tag_by_name "gray_background" 
        ~start:start_iter ~stop:stop_iter);
    apply_tag s

let find_in_ast s edit m  = 
  if !edit then 
    false
  else 
    try 
      get_buffer_coordinates m;
      apply_tag (parse_psystem !s);
      false
    with NotBuffer -> (apply_tag (cancel_last_visited ()); false)

let modify_ast ast edit b = 
  if !edit then false
  else 
    (* if GdkEvent.get_type b = `TWO_BUTTON_PRESS then *)
    (*  (entry_window#show (); *)
    (*   (* compare_motion_double buffer ; *) *)
    (*    true) *)
    (* else *)
    (if !buffer_l <> -1 && !buffer_l <> -1 then
        apply_tag (parse_psystem_m !ast );
     true)
      
let save_ex_file s file b =
  let oc = open_out file in
  Printf.fprintf oc "%s" (Psystem_printer.psystem_to_string !s);
  close_out oc;
  true

let save_file s file b = 
  parse_linact !s;
  let l = !inact_l in
  let oc = open_out file in 
  if l == [] then Printf.fprintf oc "vide" else
  List.iter (fun (s, e) -> Printf.fprintf oc "%d %d " s e) l;
  close_out oc;
  (* let _ = save_ex_file s newfile b in *)
  true



let confirm s file  e =
  let dlg = GWindow.message_dialog
    ~message:"<big> Save current session </big>"
    ~parent:window
    ~destroy_with_parent:true
    ~use_markup:true
    ~message_type:`QUESTION
    ~position:`CENTER_ON_PARENT
    ~buttons:GWindow.Buttons.yes_no () in
  let res = dlg#run () = `YES  in
  let _ = if res then save_file s file e else true in
  dlg#destroy ();
  false

    

let show_file s new_name save_name b = 
  let _ = save_file s save_name new_name in
  source2#source_buffer#set_text (read_file new_name);
  true

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
      text1#buffer#set_text "syntax error"
    |Lexer.Lexical_error s ->
      let (start, stop) = (lexeme_start lb, lexeme_end lb) in
      let start_iter = source#source_buffer#get_iter (`OFFSET start) in 
      let stop_iter = source#source_buffer#get_iter (`OFFSET stop) in 
      source#source_buffer#apply_tag_by_name "error" 
        ~start:start_iter ~stop:stop_iter;
      text1#buffer#set_text ("lexical error : "^s)
    |Typing.Error (e,loc) ->
      let (start, stop) = (lexeme_start lb, lexeme_end lb) in
      let start_iter = source#source_buffer#get_iter (`OFFSET start) in
      let stop_iter = source#source_buffer#get_iter (`OFFSET stop) in
      source#source_buffer#apply_tag_by_name "error"
        ~start:start_iter ~stop:stop_iter;
      text1#buffer#set_text ("typing error : "));
      close_in ic
      

let edit_mode ast new_file button edit m =
  if button#active then 
    ( 
      edit := true;
      source#set_editable true;
      source#set_cursor_visible true; 
    )
  else 
    ( let oc = open_out new_file in
      let str =  source#source_buffer#get_text  () in 
      Printf.fprintf oc "%s" str;
      close_out oc;
      open_show_file ast new_file edit

    )

let execute buffer file  b  =
     (let ic = Unix.open_process_in ("cubicle -nocolor "^file) in
   let str = ref "" in
   try
     while true do
       str := !str^"\n"^input_line ic;
       buffer#set_text (Glib.Convert.locale_to_utf8 !str)
     done
   with
       End_of_file ->
         close_in ic); true

let show_tree b = 
    (let ic = Unix.open_process_in ("cubicle -nocolor -v "^file) in
     let str = ref "" in
     try
       while true do
       str := !str^"\n"^input_line ic;
       done
     with
         End_of_file ->
           close_in ic;  Ed_main.open_graph !str );
  true
          


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
  let s_iter = match !last_search_iter with 
    |None -> start_iter
    |Some (_, x) -> x in 
  let stop_iter = source#source_buffer#end_iter in
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

let rec list_position l = 
  match l with 
    |[] -> []
    |x::[] -> []
    |x::y::s -> (int_of_string x, int_of_string y)::list_position s

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
  ignore (source#source_buffer#create_tag ~name:"gray_background" [`BACKGROUND_GDK light_gray]);
  ignore (source#source_buffer#create_tag ~name:"delete" [`BACKGROUND_GDK light_gray]);
  ignore (source#source_buffer#create_tag ~name:"dark" [`FOREGROUND_GDK gray]);
  ignore (source#source_buffer#create_tag ~name:"error" [`BACKGROUND "red"]);
  ignore (source#source_buffer#create_tag ~name:"search" [`BACKGROUND "yellow"]);
  ignore (source#source_buffer#create_tag ~name:"search_next" [`BACKGROUND "orange"]);
  (* t1#set_priority 0; *)
  (* t2#set_priority 1; *)
  source#event#add [`BUTTON_PRESS;`KEY_PRESS];   
  source#set_editable false;

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
  with Sys_error(_) -> Printf.printf "pas de fichier %s" inter_path);

  ignore (source#event#connect#motion_notify ~callback:(find_in_ast ast edit));
  ignore (source#event#connect#button_press ~callback:(modify_ast ast edit));
  ignore (save_button#event#connect#button_press 
    ~callback:(save_file ast save_path));
  ignore (execute_button#event#connect#button_press 
    ~callback:(fun b -> 
      let _ = save_ex_file ast new_path b in 
      execute text1#buffer new_path b));

  ignore (execute_button2#event#connect#button_press
    ~callback:(execute text2#buffer file_name ));

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

  ignore (trace_button#event#connect#button_press ~callback: (show_tree));

  ignore (window#event#connect#delete (confirm ast save_path));
  window#show ();
  GMain.main ()


