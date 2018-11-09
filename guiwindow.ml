open Psystem_parser
open Gdk.Color
open GdkEvent.Button
open Lexing
open Options
open Format


exception CursorNotOverText
exception FileError
exception KillThread
exception Value_mode_error
exception Match

let last_search_iter = ref None

let trans_args = ref []

let kill_thread = ref false

let wd = if double then 1600 else 1000

module M = Map.Make (String)

let var_map = ref M.empty

let window =
  let _ = GMain.init () in
  let wnd = GWindow.window
    ~title:"Cubicle GUI"
    ~position:`CENTER
    ~resizable:true
    ~width:wd
    ~height:800 () in
  let _ = wnd#connect#destroy ~callback:(GMain.quit) in
  wnd

let cubicle  =
  let manager = GSourceView2.source_language_manager ~default:true in
  match manager#language "cubicle" with
    | None -> None
    | some -> some

let box = GPack.vbox ~homogeneous:false ~border_width:0 ~packing:window#add ()

(* let menu_bar = GMenu.menu_bar *)
(*   ~packing:(box#pack ~expand:false ~fill:false)() *)

(* let create_menu label menubar = *)
(*   let item = GMenu.menu_item ~label ~packing:menubar#append () in *)
(*   GMenu.menu ~packing:item#set_submenu () *)

(* let options_menu, trace_menu  =  *)
(*   let o_menu= create_menu "Options" menu_bar in  *)
(*   GToolbox.build_menu o_menu *)
(*     ~entries:[`C ("Options 1", false, fun _ -> () ); *)
(*               `C ("Options 2", false, fun _ -> () )]; *)
(*   let t_menu = create_menu "Display trace" menu_bar in *)
(*   GToolbox.build_menu t_menu *)
(*     ~entries:[`I ("Commented file", fun () -> () ); *)
(*               `I ("Original file", fun () -> () )]; *)
(*   o_menu, t_menu *)


let toolbox_frame = GBin.frame ~border_width:8 ~packing:(box#pack ~expand:false ~fill:false) ()

let toolbox = GPack.hbox ~packing:(toolbox_frame#add) ()

let toolbar =
  let t = GButton.toolbar ~tooltips:false ~packing:toolbox#add ()
  in t#set_icon_size `DIALOG; t

let run_button = toolbar#insert_button
  ~text:" Run Cubicle"
  ~icon:(GMisc.image ~stock:`EXECUTE ~icon_size:`LARGE_TOOLBAR ())#coerce ()

let stop_button =
  toolbar#insert_button
    ~text:" Abort"
    ~icon:(GMisc.image ~stock:`STOP ~icon_size:`LARGE_TOOLBAR ())#coerce ()

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
  ignore(toolbar#insert_widget hbox#coerce);
  toolbar#insert_space ();
  hbox, result_image, result_label

let toolsearch =
  let t = GButton.toolbar ~tooltips:true ~packing:(toolbox#pack ~fill:false ~expand:false) () in
  t#set_icon_size `DIALOG; t

let search_box =
  let sb = GPack.hbox ~spacing:5 ~border_width:5 () in
  ignore(GMisc.image ~icon_size:`LARGE_TOOLBAR
	   ~stock:`FIND ~packing:sb#add ());sb

let search_bar =
  let sb = GEdit.entry ~packing:(search_box#add) () in
  ignore (toolbar#insert_widget search_box#coerce); sb

let next_button = toolbar#insert_button
  ~text:" Next"
  ~icon:(GMisc.image ~stock:`GO_DOWN ~icon_size:`SMALL_TOOLBAR())#coerce ()

let previous_button = toolbar#insert_button
  ~text:" Previous"
  ~icon:(GMisc.image ~stock:`GO_UP ~icon_size:`SMALL_TOOLBAR())#coerce ()


let trace_button = toolbar#insert_button ~text:"Display trace" ()

(* ~icon:( *)
(* GButton.button ~label:"Trace"  *)
  (* ~packing:(toolbar#add (\* ~expand:false ~fill:false *\)) () *)

(** Debug mode *)
(* let show_file_button = GButton.button ~label:"Display file with comments" *)
(*   ~packing:(toolbox#add (\* ~expand:false ~fill:false *\)) ~show:(double)() *)

(** Debug mode *)

let execute_button2 = toolbar#insert_button ~text:"Run original file"
 ~icon:(GMisc.image ~stock:`EXECUTE ~icon_size:`LARGE_TOOLBAR ())#coerce ()
  (* ~packing:(toolbar#add (\* ~expand:false ~fill:false *\)) ~show:(double)() *)

let debug_box =  GPack.paned `HORIZONTAL ~show:true ~packing:(box#add) ()
(* GPack.hbox ~packing:box#add () *)

let source_box1 = GPack.vbox ~packing:(debug_box#add1 (* ~expand:true *) (* ~fill:true *)) ()

(** Debug mode *)
let source_box2 = GPack.vbox ~packing:debug_box#add2  ~show:(double)()

let source_frame1 = GBin.frame  ~border_width:10
  ~packing:(source_box1#pack ~expand:true ~fill:true) ()

let source_frame2 = GBin.frame  ~border_width:10
  ~packing:(source_box2#pack ~expand:true ~fill:true) ()

let pane1 = GPack.paned `VERTICAL  ~show:true ~packing:(source_frame1#add) ()

(** Debug mode *)
let pane2 = GPack.paned `VERTICAL  ~show:true ~packing:(source_frame2#add) ()

(* let result_frame = GBin.frame ~border_width:10 ~height:200 *)
(*   ~packing:(source_box1#pack ~expand:false ~fill:true) () *)

(* let result_frame2 = GBin.frame ~border_width:10 ~height:200 *)
(*   ~packing:(source_box2#pack ~expand:false ~fill:true) () *)

let result_scroll = GBin.scrolled_window
  ~hpolicy:`ALWAYS
  ~vpolicy:`ALWAYS
  ~border_width:5
  ~packing: pane1#add2 ()

let result_text1 =
  let t = GSourceView2.source_view
    ~packing: result_scroll#add () in
  t#set_editable false;
  t#set_cursor_visible false;
  t#misc#modify_font_by_name ("DejaVu Sans Mono "^(string_of_float Options.source_font_size));
 t

let scroll =
  let s =
    GBin.scrolled_window
      ~hpolicy:`ALWAYS
      ~vpolicy:`ALWAYS
      ~width:(wd/2)
      ~height:600
      ~packing:(pane1#add1) () in
  s

(** Debug mode *)
let scroll2 = GBin.scrolled_window
  (* ~hpolicy:`ALWAYS  *)
  ~vpolicy:`ALWAYS
  ~width: (wd/2)
  ~height:600
  ~packing:(pane2#add1)   ()

(** Debug mode *)
let result_scroll2 = GBin.scrolled_window
  ~hpolicy:`ALWAYS
  ~vpolicy:`ALWAYS
  ~border_width:5
  ~packing: (* result_frame2 *)(pane2#pack2 ~resize:true ~shrink:true)  ()

(** Debug mode *)
let result_text2 =
  let t = GSourceView2.source_view
    ~packing:result_scroll2#add () in
  t#misc#modify_font_by_name ("DejaVu Sans Mono "^(string_of_float Options.source_font_size));
  t

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
  src#misc#modify_font_by_name ("DejaVu Sans Mono "^(string_of_float Options.source_font_size));
  let buf = src#source_buffer in
  if cubicle <> None then
    buf#set_language cubicle;
  buf#set_highlight_syntax true;
  src

let save_session s file b =
  parse_linact !s;
  let l = !inact_l in
  let oc = open_out  file in
  if l == [] then Printf.fprintf oc "vide" else
    List.iter (fun (s, e) -> Printf.fprintf oc "%d %d " s e) l;
  close_out oc;
  true

let confirm s file e =
  (if GToolbox.question_box
      ~title:"Save session" ~buttons:["Quit"; "Save"]
      ~default:2 ~icon:(GMisc.image ~stock:`SAVE  ~icon_size:`DIALOG ())
      "Would you like to save the session ?" = 2 then
      let _ = save_session s file e in ());
  false

let list_to_string l  =
  List.fold_right (fun x acc -> acc ^ x ^ "\n") l ""

(* let match_condition s sep l t = *)
(*   let arg_list = !trans_args in *)
(*   try *)
(*     ignore (Str.search_forward sep s 0); *)
(*     (match Str.split sep s with *)
(*       |a::b::[] -> *)
(*         (let a = String.trim a in *)
(*          let b = String.trim b in *)
(*          try *)
(*            let open_b = (Str.search_forward (Str.regexp "\\[") a  0) + 1 in *)
(*            let close_b = Str.search_forward (Str.regexp "\\]") a 0 in *)
(*            let arg = String.sub a open_b  (close_b - open_b) in *)
(*            List.iter (fun (_, x) -> print_string x; print_newline ()) arg_list; *)
(*            let (r, _) = List.find (fun (_, x) -> x = arg) arg_list in *)
(*            let new_var = Str.replace_first (Str.regexp "\\[n\\]") ("["^r^"]") a in *)
(*            Ed_main.var_l := (new_var, ([b], t))::!Ed_main.var_l *)
(*          with Not_found -> (Ed_main.var_l := (a, ([b], t))::!Ed_main.var_l)) *)
(*       |_ -> failwith "pb match_condition guiwindow"); *)
(*     raise Match *)
(*   with Not_found -> () *)

let match_condition s sep l t =
  let arg_list = !trans_args in
  try
    ignore (Str.search_forward sep s 0);
    (match Str.split sep s with
      |a::b::[] ->
        (let a, b =
          try
            ignore (float_of_string (String.trim a));
            print_endline (b^"TEST"^a);
            (String.trim b, String.trim a)
          with Failure(_) -> (String.trim a, String.trim b) in
          try
            let open_b = (Str.search_forward (Str.regexp "\\[") a  0) + 1 in
            let close_b = Str.search_forward (Str.regexp "\\]") a 0 in
            let arg = String.sub a open_b  (close_b - open_b) in
            let (r, _) = List.find (fun (_, x) -> x = arg) arg_list in
           (* Printf.printf "var : %s\n" r;  *)
           (* print_newline (); *)
            let new_var = Str.replace_first (Str.regexp "\\[.*\\]") ("["^r^"]") a in
            l := (new_var, ([b], t)) :: !l
          with Not_found ->
            try
              let (r, n) = List.find (fun (_, x) -> x = b) arg_list in
              l := (a, ([r], t)) :: !l
            with Not_found -> l := (a, ([b], t)) :: !l)
      |_ -> failwith "pb match_condition guiwindow");
    raise Match
  with Not_found -> ()

let mode_var () =
  let condition_list = ref [] in
  M.iter (fun x _ ->
    try
      match_condition x (Str.regexp ">=") condition_list Ed_graph.GreaterEq;
      match_condition x (Str.regexp "<=") condition_list Ed_graph.LessEq;
      match_condition x (Str.regexp "<>") condition_list Ed_graph.NEq;
      match_condition x (Str.regexp ">")  condition_list Ed_graph.Greater;
      match_condition x (Str.regexp "<")  condition_list Ed_graph.Less;
      match_condition x (Str.regexp "=")  condition_list Ed_graph.Eq;
      failwith "pb format mode_var guiwindow"
    with Match -> ()
  ) !var_map;
  !condition_list


let add_value_var l =
  try
    List.iter (fun (x, e) ->
      if e#text = "" then
        (if !Ed_main.mode_value then
            begin
              GToolbox.message_box
                ~title:"Error" "Please enter a value or choose change mode";
              raise Value_mode_error
            end;
         Ed_main.var_l := (x, ([], Ed_graph.Eq))::!Ed_main.var_l)
      else
        let str_l = Str.split (Str.regexp ";") e#text in
        let str_l = (str_l, Ed_graph.Eq) in
        Ed_main.var_l := (x, str_l)::!Ed_main.var_l) l;
    var_map := M.empty;
    true
  with Value_mode_error -> false

let scroll_to_transition ast t =
  var_map := M.empty;
  match Str.split (Str.regexp "(") t with
    |[] -> failwith "pb transition"
    |str::_ ->
      let open_p = (Str.search_forward (Str.regexp "(") t  0) + 1 in
      let close_p = Str.search_forward (Str.regexp ")") t 0 in
      let args = String.sub t open_p  (close_p - open_p) in
      let arg_list = Str.split (Str.regexp ",") args in
      let list = List.map2 (fun proc arg_name -> (proc, arg_name))
        arg_list (get_transition_args str !ast) in
      trans_args := list;
      let start, stop = find_transition_ast str !ast in
      let start_iter = source#source_buffer#get_iter(`OFFSET start) in
      let stop_iter = source#source_buffer#get_iter (`OFFSET stop) in
      window#present ();
      source#source_buffer#apply_tag_by_name "search" ~start:start_iter
        ~stop:stop_iter;
      ignore (source#scroll_to_iter ~use_align:true ~yalign:0.2 start_iter)


let select_var l new_path ast open_graph =
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
    ~rows:(M.cardinal !var_map)
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
    incr cpt) !var_map ;
  let h_box = GPack.hbox ~packing:(v_box#pack) () in
  let radio_button_box =  GPack.button_box
    ~packing:(h_box#pack) `VERTICAL () in
  let button_box = GPack.button_box
    ~packing:(v_box#pack) `HORIZONTAL () in
  let button_cancel = GButton.button
    ~label:"Cancel"
    ~stock:`CANCEL
    ~packing:(button_box#add) () in
  let button_value = GButton.radio_button
    ~label:"Watch variable value"
    ~packing:(radio_button_box#add) () in
  let button_change = GButton.radio_button
    ~group:button_value#group ~label:"Watch variable change"
    ~packing:(radio_button_box#add)() in
  let button_show = GButton.button
    ~label:"Show Graph"
    ~stock:`APPLY
    ~packing:(button_box#add) () in
  wnd#show();
  (ignore (button_show#event#connect#button_press
             ~callback:(fun b ->
               if button_change#active then
                 (Ed_main.mode_value := false;
                  Ed_main.mode_change := true)
               else
                 (Ed_main.mode_value := true;
                  Ed_main.mode_change := false);
               if add_value_var !t_edit_l || !Ed_main.mode_change then
                 ( wnd#destroy ();
                   source#source_buffer#remove_tag_by_name "var"
                     ~start:(source#source_buffer#start_iter) ~stop:(source#source_buffer#end_iter);
                   open_graph := true;
                   Ed_main.init new_path (punsafe_length (!ast)) open_graph
                 );
               true);

   );
   ignore (button_cancel#event#connect#button_press
             ~callback:(fun b -> wnd#destroy (); true));
   Ed_main.mode_change := false;
   Ed_main.mode_value := false;
   var_map := M.empty;
   Ed_main.var_l := []
  )


let select_var_none new_path ast open_graph=
  if GToolbox.question_box
    ~title:"List" ~buttons:["Add"; "Show trace"]
    ~default:2
    ~icon:(GMisc.image ~stock:`DIALOG_QUESTION  ~icon_size:`DIALOG ())
    "No variables.\n(Add with right click)" = 2 then
    (Ed_main.scroll_to_transition := scroll_to_transition ast;
     open_graph := true;
     Ed_main.init new_path (punsafe_length (!ast)) open_graph;
    )


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
  src#misc#modify_font_by_name ("DejaVu Sans Mono "^(string_of_float Options.source_font_size));
  src#set_editable false;
  let buf = src#source_buffer in
  buf#set_language cubicle;
  buf#set_highlight_syntax true;
  src

let read_file path =
  let c_in = open_in path in
  let str = really_input_string c_in (in_channel_length c_in) in
  close_in c_in;
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
          if M.mem str !var_map then
            (let (be, en) = M.find str !var_map in
             if be = start && en = stop then
               var_map := M.remove str !var_map ;
             source#source_buffer#remove_tag_by_name "var"
               ~start:start_iter ~stop:stop_iter)
          else
            var_map := M.add str (start, stop) !var_map
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
            begin
              apply_tag (parse_psystem_m !ast);
              source2#source_buffer#set_text (Psystem_printer.psystem_to_string !ast)
            end;
         true)

(** Sauvegarde du fichier envoyé à Cubicle *)
let save_execute_file s file b =
  if edit_button#active then
    (GToolbox.message_box ~title:"Edit mode" "Please exit edit mode before running cubicle"
       ~icon:((GMisc.image ~stock:`DIALOG_WARNING ~icon_size:`DIALOG ())#coerce) ~ok:"ok" ;
     false)
  else
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
    ( (* let c = source#source_buffer#cursor_position in  *)
      let oc = open_out new_file in
      let str =  source#source_buffer#get_text  () in
      Printf.fprintf oc "%s" str;
      close_out oc;
      try
        (open_show_file ast new_file edit;
         (* ignore (source#scroll_to_iter (source#source_buffer#get_iter (`OFFSET !buffer_c))); *)
(* result_text1#buffer#set_text "" *))
      with FileError -> button#set_active true)

let safe_or_unsafe (res_t:GSourceView2.source_view) =
  let str = res_t#buffer#get_text () in
  try
    (let _ = Str.search_forward (Str.regexp "UNSAFE") str 0 in
     result_image#set_stock `DIALOG_ERROR;
     result_label#set_text "Unsafe")
  with Not_found ->
    try
      (let _ = Str.search_forward (Str.regexp "SAFE") str 0 in
       result_image#set_stock `APPLY;
       result_label#set_text "Safe")
    with Not_found ->
      ( result_image#set_stock `DIALOG_ERROR;
       result_label#set_text "Error")


let rec read_loop (res_t:GSourceView2.source_view) pid descr_l  =
    let ready_read, _ , _ = Unix.select descr_l [] [] (0.1) in
    if !kill_thread then
       (Unix.kill pid Sys.sigint;
        kill_thread := false;
       raise KillThread);
    match ready_read with
    |[] -> ()
    |fd_l ->
      (List.iter (fun fd ->
        let str = Bytes.make 1000 ' ' in
        let n = (Unix.read fd str 0 1000) in
        res_t#buffer#insert (String.sub (Bytes.to_string str) 0 n);
        ignore (res_t#scroll_to_iter ~use_align:true ~yalign:0.5 (res_t#buffer#end_iter))) fd_l;
       read_loop res_t pid descr_l)

let get_trace (res_t, file) =
  res_t#buffer#set_text "";
  let inc, in_fd  = Unix.pipe () in
  let outc, out_fd  = Unix.pipe () in
  let errc, err_fd = Unix.pipe () in
  let pid = Unix.create_process "cubicle" [|"cubicle";"-nocolor"; file|]
  inc out_fd err_fd  in
  (try
    read_loop res_t pid [outc];
    read_loop res_t pid [outc];
    read_loop res_t pid [errc];
    safe_or_unsafe res_t
  with KillThread ->
    read_loop res_t pid [outc];
    read_loop res_t pid [errc];
    safe_or_unsafe res_t;
    kill_thread := false);
  Unix.close inc; Unix.close in_fd;
  Unix.close outc; Unix.close out_fd;
  Unix.close errc; Unix.close err_fd

let execute res_t file b  =
  GtkThread.async (fun () -> ignore (Thread.create get_trace (res_t, file))) ()

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
   with Sys_error(_) -> () (* Printf.printf "pas de fichier %s" inter_path *));
    try
     let str = read_file save_path in
     let fl = Str.split (Str.regexp "[ \t]+") str in
     let pos_l = list_position fl in
     inact_l := pos_l;
     parse_init !ast;
     source#source_buffer#set_text (read_file inter_path);
     apply_tag (parse_psystem !ast);
   with Sys_error(_) -> ()

let open_window s  =
  let open_graph = ref false in
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
  (* source#event#add [`BUTTON_PRESS; `KEY_PRESS];    *)
  source#set_editable false;
  open_file inter_path save_path ast;
  ignore (source#event#connect#motion_notify ~callback:(find_in_ast ast edit));
  ignore (source#event#connect#button_press ~callback:(modify_ast ast edit ));
  ignore (save_button#event#connect#button_press
            ~callback:(save_session ast save_path));
  ignore (run_button#event#connect#button_press
            ~callback:(fun b ->
              if  save_execute_file ast new_path b then
              execute result_text1 new_path b; true));
  ignore (execute_button2#event#connect#button_press
            ~callback:(fun b -> execute result_text2 file_name b; true));
  ignore (edit_button#connect#toggled
            ~callback:(edit_mode ast inter_path edit_button edit));
  ignore (search_bar#connect#changed
            ~callback:(search));
  ignore (next_button#event#connect#button_press
            ~callback:(search_next));
  ignore (previous_button#event#connect#button_press
            ~callback:(search_previous));
  (* ignore (show_file_button#event#connect#button_press  *)
  (*           ~callback: (fun b -> source2#source_buffer#set_text (Psystem_printer.psystem_to_string !ast); true)); *)
  ignore (stop_button#event#connect#button_press
            ~callback: (fun b -> kill_thread:= true; true));
  ignore (trace_button#event#connect#button_press ~callback: (fun b ->
    let _ = save_execute_file ast new_path b in
    Ed_main.var_l := [];
    if !open_graph then
      (source#source_buffer#remove_tag_by_name "var"
         ~start:(source#source_buffer#start_iter) ~stop:(source#source_buffer#end_iter);
       source#source_buffer#remove_tag_by_name "search"
         ~start:(source#source_buffer#start_iter) ~stop:(source#source_buffer#end_iter);
       Ed_main.path_to_loop (mode_var());
       var_map := M.empty
      )
    else
      if M.cardinal !var_map = 0 then
        (Ed_main.mode_value := false;
         Ed_main.mode_change := false;
         select_var_none new_path ast open_graph )
      else
        select_var !Ed_main.var_l new_path ast open_graph ;
    true));
  ignore (window#event#connect#delete (confirm ast save_path));
  window#show ();
  GtkThread.main ()
