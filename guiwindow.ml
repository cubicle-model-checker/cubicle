open Psystem_parser
open Gdk.Color
open GdkEvent.Button
open Lexing
open Options


exception NotBuffer

let window =
  let _ = GMain.init () in
  let wnd = GWindow.window 
    ~title:"Cubicle GUI" 
    ~position:`CENTER 
    ~resizable:true 
    ~width:1600 ~height:800 () in 
  let _ = wnd#connect#destroy GMain.quit in
  wnd 
 
  
let ocaml = 
  let manager = GSourceView2.source_language_manager ~default:true in 
  match manager#language "cubicle" with 
    | None -> failwith "La coloration syntaxique pour OCaml n'est pas disponible !" 
    | some -> some

let box = GPack.vbox ~packing:window#add ()

let button_box = GPack.hbox ~packing:(box#pack ~expand:false ~fill:false) ()

let execute_button = GButton.button ~label:"Run" ~packing:(button_box#pack ~expand:false ~fill:false)()

let show_file_button = GButton.button ~label:"Show new file" ~packing:(button_box#pack ~expand:false ~fill:false)()

let execute_button2 = GButton.button ~label:"Run new file" ~packing:(button_box#pack ~expand:false ~fill:false)()

let save_button = GButton.button ~label:"Save new file" ~stock:`SAVE ~packing:(button_box#pack ~expand:false ~fill:false)() 

let edit_button = GButton.toggle_button ~label:"Edit" ~stock:`EDIT ~packing:(button_box#pack ~expand:false ~fill:false)()
  
let b = GPack.hbox ~packing:box#add ()

let b1 = GPack.vbox ~packing:b#add ()

let b2 = GPack.vbox ~packing:b#add () 

let e_box = GBin.event_box ~height:550 ~packing:(b1#pack ~expand:false ~fill:false) ()

let t_scroll = GBin.scrolled_window 
  ~hpolicy:`ALWAYS 
  ~vpolicy:`ALWAYS 
  ~packing: b1#add()

let text1 =  GSourceView2.source_view ~packing:t_scroll#add ()

let e_box2 = GBin.event_box ~height:550 ~packing:(b2#pack ~expand:false ~fill:false) ()

let t_scroll2 = GBin.scrolled_window 
  ~hpolicy:`ALWAYS 
  ~vpolicy:`ALWAYS 
  ~packing: b2#add  () 

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
      true
    with NotBuffer -> (apply_tag (cancel_last_visited ()); false)

let modify_ast ast file edit b = 
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
      
let save_file s file b = 
  let oc = open_out file in 
  Printf.fprintf oc "%s" (Psystem_printer.psystem_to_string !s);
  close_out oc;
  true

let show_file s new_name b = 
  let _ = save_file s new_name b in
  source2#source_buffer#set_text (read_file new_name);
  true


let edit_mode ast new_file button edit m =
  if button#active then 
    (edit := true;
     source#set_editable true;
     source#set_cursor_visible true;
)
  else 
    ( let oc = open_out new_file in
      let str =  source#source_buffer#get_text () in 
      Printf.fprintf oc "%s" str;
      close_out oc;
     let ic = open_in new_file in
     let lb = from_channel ic in
     (try 
        (* let mark_l = int_to_mark !inact_l in *)
        ast := Parser.system Lexer.token lb;
        (* let l = mark_to_tag mark_l in *)
        source#source_buffer#set_text (read_file new_file);
        (* apply_tag_mark l; *)
        edit := false;
         with Parsing.Parse_error -> 
        (let (start, stop) = (lexeme_start lb, lexeme_end lb) in
         let start_iter = source#source_buffer#get_iter (`OFFSET start) in 
         let stop_iter = source#source_buffer#get_iter (`OFFSET stop) in 
        source#source_buffer#apply_tag_by_name "error" 
          ~start:start_iter ~stop:stop_iter
        ););
     
        source#set_editable false;
        source#set_cursor_visible false;
    )



let execute buffer file b = 
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

let open_window s  = 
  let ast = ref s in
  let edit = ref false in 
  let file_name = Options.file in 
  let new_file_name = (String.sub file_name 0 ((String.length file_name) - 4))^"mod.cub" in
  let inter_file_name = (String.sub file_name 0 ((String.length file_name) - 4))^"inter.cub" in
  source#source_buffer#set_text (read_file file_name); 
  let map = Gdk.Color.get_system_colormap () in 
  let light_gray = Gdk.Color.alloc ~colormap:map (`NAME "light gray") in
  let gray = Gdk.Color.alloc ~colormap:map (`NAME "gray") in 

  let t1 = (source#source_buffer#create_tag 
              ~name:"gray_background" [`BACKGROUND_GDK light_gray]) in
  let t2 = (source#source_buffer#create_tag 
              ~name:"delete" [`BACKGROUND_GDK light_gray]) in
  let t3 = (source#source_buffer#create_tag 
              ~name:"dark" [`FOREGROUND_GDK gray]) in
  let t3 = (source#source_buffer#create_tag 
              ~name:"error" [`BACKGROUND "red"]) in
  t1#set_priority 0;
  t2#set_priority 1;
  source#event#add [`BUTTON_PRESS;`KEY_PRESS];   
  source#event#connect#motion_notify
    ~callback:(find_in_ast ast  edit);
source#event#connect#button_press
    ~callback:(modify_ast ast inter_file_name edit);

  save_button#event#connect#button_press 
    ~callback:(save_file ast new_file_name);

  execute_button#event#connect#button_press 
    ~callback:(execute text1#buffer file_name);

  execute_button2#event#connect#button_press
    ~callback:(execute text2#buffer new_file_name);

  edit_button#connect#toggled
    ~callback:(edit_mode ast  inter_file_name edit_button edit);

  show_file_button#event#connect#button_press 
    ~callback: (show_file ast new_file_name);
  window#show (); 
  GMain.main ()


