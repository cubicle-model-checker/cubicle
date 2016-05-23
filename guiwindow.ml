open Astparser
open Gdk.Color

let window =
  GMain.init ();
  let wnd = GWindow.window 
    ~title:"Cubicle GUI" 
    ~position:`CENTER 
    ~resizable:false  
    ~width:800 ~height:600 () in 
  wnd#connect#destroy GMain.quit; 
  wnd 
 
let ocaml = 
  let manager = GSourceView2.source_language_manager ~default:true in 
  match manager#language "objective-caml" with 
  | None -> failwith "La coloration syntaxique pour OCaml n'est pas disponible !" 
  | some -> some

let box = GPack.vbox ~packing:window#add ()

let button_box = GPack.hbox ~packing:(box#pack ~expand:false ~fill:false) ()

let execute_button = GButton.button ~label:"Run"  ~packing:(button_box#pack ~expand:false ~fill:false)()

let e_box = GBin.event_box ~packing:box#add () 

let scroll = GBin.scrolled_window 
  ~hpolicy:`ALWAYS 
  ~vpolicy:`ALWAYS 
  ~packing:e_box#add () 
 
let source = 
  let src = GSourceView2.source_view 
    ~draw_spaces:[`SPACE] 
    ~auto_indent:true 
    ~indent_on_tab:true
    ~indent_width:2 
    ~insert_spaces_instead_of_tabs:true 
    ~right_margin_position:80 
    ~show_line_numbers:true 
    ~packing:scroll#add () in 
  src#misc#modify_font_by_name "Monospace 10"; 
  let buf = src#source_buffer in 
  buf#set_language ocaml; 
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

let get_buffer_coordinates m = 
  let mouse_x, mouse_y = get_mouse_coordinates m in 
  let buffer_x, buffer_y = source#window_to_buffer_coords `TEXT mouse_x mouse_y in 
  let iter = source#get_iter_at_location buffer_x buffer_y in 
  buffer_l := 1 + iter#line; 
  buffer_c := iter#offset


let find_in_ast s buffer m = 
  get_buffer_coordinates m;
  parse_ast s buffer; 
  true

let modify_ast s buffer b = 
  parse_modify_ast s buffer;
  true
  
let open_window s  = 
  source#source_buffer#set_text (read_file Options.file); 
    let map = get_system_colormap () in
       source#source_buffer#create_tag ~name:"gray_background" [`BACKGROUND_GDK (alloc map (`NAME "pink"))];
    source#event#add [`BUTTON_PRESS];
    source#event#connect#motion_notify ~callback:(find_in_ast s source#source_buffer);
    source#event#connect#button_press ~callback:(modify_ast s source#source_buffer);
  window#show (); 
  GMain.main ()
