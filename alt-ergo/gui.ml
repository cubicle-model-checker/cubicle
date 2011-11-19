open Why_ptree
open Why_annoted
open Why_connected

open Lexing
open Format
open Options

let () = 
  try let _ = GMain.init () in ()
  with Gtk.Error s -> eprintf "%s@." s

(* GTK *)

let window_width = 950
let window_height = 800
let show_discharged = ref false


let w = 
  GWindow.window
    ~title:"AltGr-Ergo"
    ~allow_grow:true
    ~allow_shrink:true
    ~width:window_width
    ~height:window_height ()
  
let quit () =
  GMain.quit ()


let pop_error ?(error=false) ~message () =
  let pop_w = GWindow.dialog
    ~title:(if error then "Error" else "Warning")
    ~allow_grow:true
    ~width:400 ()
  in
  let bbox = GPack.button_box `HORIZONTAL ~border_width:5 ~layout:`END
    ~child_height:20 ~child_width:85 ~spacing:10
    ~packing:pop_w#action_area#add () in
  
  let button_ok = GButton.button ~packing:bbox#add () in
  let phbox = GPack.hbox ~packing:button_ok#add () in
  ignore(GMisc.image ~stock:`OK ~packing:phbox#add ());
  ignore(GMisc.label ~text:"OK" ~packing:phbox#add ());
  
  let hbox = GPack.hbox ~border_width:5 ~packing:pop_w#vbox#pack () in
  
  ignore(GMisc.image ~stock:(if error then `DIALOG_ERROR else `DIALOG_WARNING)
	   ~icon_size:`DIALOG ~packing:hbox#pack ());
  ignore(GMisc.label ~text:message
	   ~xalign:0. ~xpad:10 ~packing:hbox#add ());
  ignore(button_ok#connect#clicked ~callback: pop_w#destroy);
  pop_w#show ()



let update_status image label buttonclean env d s steps =
  let satmode = !smtfile or !smt2file or !satmode in 
  match s with
    | Frontend.Unsat dep ->
	let time = Frontend.Time.get () in
	if not satmode then Loc.report d.st_loc;
	if satmode then printf "@{<C.F_Red>unsat@}@."
	else printf "@{<C.F_Green>Valid@} (%2.4f) (%Ld)@." time steps;
	if proof then begin 
	  printf "Proof:\n%a@." Explanation.print_proof dep;
	  show_used_lemmas env dep
	end;
	image#set_stock `YES;
	label#set_text (sprintf "  Valid (%2.4f)" time);
	buttonclean#misc#show ();
	ignore(buttonclean#connect#clicked 
		 ~callback:(fun () -> prune_unused env))
	  
    | Frontend.Inconsistent ->
	if not satmode then 
	  (Loc.report d.st_loc; 
	   fprintf fmt "Inconsistent assumption@.")
	else printf "unsat@.";
	image#set_stock `EXECUTE;
	label#set_text "  Inconsistent assumption"
	  
    | Frontend.Unknown ->
	if not satmode then
	  (Loc.report d.st_loc; printf "I don't know.@.")
	else printf "unknown@.";
	image#set_stock `NO;
	label#set_text (sprintf "  I don't know (%2.4f)" (Frontend.Time.get()))
	  
    | Frontend.Sat  ->
	if not satmode then Loc.report d.st_loc;
	if satmode then printf "unknown (sat)@." 
	else printf "I don't know@.";
	image#set_stock `NO;
	label#set_text
	  (sprintf "  I don't know (sat) (%2.4f)" (Frontend.Time.get()))


exception Abort_thread

let interrupt = ref None

let vt_signal =
  match Sys.os_type with
    | "Win32" -> Sys.sigterm
    | _ -> Sys.sigvtalrm

let force_interrupt old_action_ref n =
  (* This function is called just before the thread's timeslice ends *)
  if Some(Thread.id(Thread.self())) = !interrupt then
    raise Abort_thread;
  match !old_action_ref with
    | Sys.Signal_handle f -> f n
    | _ -> fprintf fmt "Not in threaded mode@."


let rec run buttonrun buttonstop buttonclean image label thread env () =
  (* Install the signal handler: *)
  let old_action_ref = ref Sys.Signal_ignore in
  let old_action = 
    Sys.signal vt_signal (Sys.Signal_handle (force_interrupt old_action_ref)) in
  old_action_ref := old_action;
  
  image#set_stock `EXECUTE;
  label#set_text "  ...";
  buttonstop#misc#show ();
  buttonrun#misc#hide ();
  buttonclean#misc#hide ();
  clear_used_lemmas_tags env;
    
  let ast = to_ast env.ast in
  if debug then fprintf fmt "AST : \n-----\n%a@." print_typed_decl_list ast;

  (*List.iter (fprintf err_formatter "%a@." print_typed_decl) ast;*)
  let ast_pruned =
    if select > 0 then Pruning.split_and_prune select ast
    else [List.map (fun f -> f,true) ast] in

  let chan = Event.new_channel () in
  
  ignore (Thread.create
    (fun () ->
       (* Thread.yield (); *)
       ignore (Event.sync (Event.receive chan));
       if debug then fprintf fmt "Waiting thread : signal recieved@.";
       buttonstop#misc#hide ();
       buttonrun#misc#show ()
    ) ());

  let runth = (Thread.create
    (fun () ->
       (try
	  (* Thread.yield (); *)
	  if debug then fprintf fmt "Starting alt-ergo thread@.";
	  Frontend.Time.start ();
	  List.iter 
	    (fun dcl ->
	       (* Thread.yield (); *)
	      (* if debug then fprintf fmt "AST2 : \n-----\n%a@." print_typed_decl_list (let a::_ =  ast_pruned in (List.map (fun (f,_) -> f) a)); *)
	       let cnf = Cnf.make dcl in
	       ignore (Queue.fold
			 (Frontend.process_decl 
			    (update_status image label buttonclean env))
			 (Sat.empty,true, Explanation.empty) cnf)
	    ) ast_pruned
	with 
	  | Abort_thread ->
	      if debug then fprintf fmt "alt-ergo thread terminated@.";
	      image#set_stock `DIALOG_QUESTION;
	      label#set_text "  Process aborted";
	      buttonstop#misc#hide ();
	      buttonrun#misc#show ()
	  |  e -> 
	      let message = sprintf "Error: %s" (Printexc.to_string e) in
	      if debug then fprintf fmt "alt-ergo thread terminated@.";
	      image#set_stock `DIALOG_ERROR;
	      label#set_text (" "^message);
	      buttonstop#misc#hide ();
	      buttonrun#misc#show ();
	      fprintf fmt "%s@." message;
	      pop_error ~error:true ~message ()
       );
       if debug then fprintf fmt "Send done signal to waiting thread@.";
       Event.sync (Event.send chan true)
    ) ()) in
  thread := Some runth


let rec kill_thread buttonrun buttonstop image label thread () =
  match !thread with 
    | Some r -> 
	interrupt :=  Some (Thread.id r);
	Thread.join r
    | _ -> 
	interrupt := None

let remove_context env () =
  List.iter
    (fun (td, _) ->
       match td.c with
	 | APredicate_def (_, _, _, _) ->
	     toggle_prune_nodep td td.tag
	 | AAxiom (_, s, _) when String.length s = 0 || s.[0] <> '_' ->
	     toggle_prune_nodep td td.tag
	 | _ -> ()
    ) env.ast


let toggle_ctrl env key =
  if GdkEvent.Key.hardware_keycode key = 37 then
    (env.ctrl <- not env.ctrl; true)
  else false


let _ =
  ignore(w#connect#destroy ~callback:quit);

  let lmanager = GSourceView2.source_language_manager ~default:true in
  let source_language = lmanager#language "alt-ergo" in

  let smanager = GSourceView2.source_style_scheme_manager ~default:true in
  let scheme = smanager#style_scheme "tango" in

  let lb = from_channel cin in
  let typed_ast, _ = 
    try Frontend.open_file !file lb
    with
      | Why_lexer.Lexical_error s -> 
	  Loc.report (lexeme_start_p lb, lexeme_end_p lb);
	  printf "lexical error: %s\n@." s;
	  exit 1
      | Parsing.Parse_error ->
	  let  loc = (lexeme_start_p lb, lexeme_end_p lb) in
	  Loc.report loc;
          printf "syntax error\n@.";
	exit 1
      | Common.Error(e,l) -> 
	  Loc.report l; 
	  printf "typing error: %a\n@." Common.report e;
	  exit 1
  in


  let notebook = 
    GPack.notebook ~border_width:0 ~tab_pos:`BOTTOM
      ~show_border:false 
      ~enable_popup:true 
      ~scrollable:true
      ~packing:w#add () in

  List.iter
    (fun l ->
       
       let buf1 = match source_language with 
	 | Some language -> GSourceView2.source_buffer ~language
	     ~highlight_syntax:true ~highlight_matching_brackets:true ()
	 | None -> GSourceView2.source_buffer () in

       let buf2 = match source_language with 
	 | Some language -> GSourceView2.source_buffer ~language
	     ~highlight_syntax:true ~highlight_matching_brackets:true ()
	 | None -> GSourceView2.source_buffer () in

       buf1#set_style_scheme scheme;
       buf2#set_style_scheme scheme;

       let annoted_ast = annot buf1 l in
       if debug then fprintf fmt "Computing dependancies ... ";
       let dep = make_dep annoted_ast in
       if debug then fprintf fmt "Done@.";

       
       let text = List.fold_left
	 (fun _ (td,_) ->
	    match td.c with
	      | AGoal (_, s, _) -> "goal "^s
	      | _ -> "Empty"
	 ) "" annoted_ast in

       let label = GMisc.label ~text () in
       let append g = 
	 ignore(notebook#append_page ~tab_label:label#coerce g); () in
       
       let eventBox = GBin.event_box ~border_width:0 ~packing:append () in
       
       
       let vbox = GPack.vbox 
	 ~homogeneous:false ~border_width:0 ~packing:eventBox#add () in

       let rbox = GPack.vbox ~border_width:0 ~packing:vbox#add () in


       let toolbar = GButton.toolbar ~tooltips:true ~packing:rbox#pack () in
       toolbar#set_icon_size `DIALOG;
       
       let hb = GPack.paned `HORIZONTAL 
	 ~border_width:3 ~packing:rbox#add () in

       let fr1 = GBin.frame ~shadow_type:`ETCHED_OUT
	 ~width:(60 * window_width / 100) ~packing:hb#add1 () in
       let fr2 = GBin.frame ~shadow_type:`ETCHED_OUT
	 ~packing:hb#add2 () in

       let st = GMisc.statusbar ~has_resize_grip:false ~border_width:0 
	 ~packing:vbox#pack () in  
       let st_ctx = st#new_context ~name:"Type" in

       let env = create_env buf1 buf2 st_ctx annoted_ast dep in
       connect env;

       ignore (toolbar#insert_toggle_button
	 ~text:" Remove context"
	 ~icon:(GMisc.image ~stock:`CUT ~icon_size:`LARGE_TOOLBAR ())#coerce
	 ~callback:(remove_context env) ());

       let sw1 = GBin.scrolled_window
	    ~vpolicy:`AUTOMATIC 
	    ~hpolicy:`AUTOMATIC
	    ~packing:fr1#add () 
       in
       let tv1 = GSourceView2.source_view ~source_buffer:buf1 ~packing:(sw1#add)
	 ~show_line_numbers:true ~wrap_mode:`NONE() in
       let _ = tv1#misc#modify_font monospace_font in
       let _ = tv1#set_editable false in
       add_to_buffer env.buffer env.ast;

       let sw2 = GBin.scrolled_window
	    ~vpolicy:`AUTOMATIC 
	    ~hpolicy:`AUTOMATIC
	    ~packing:fr2#add () 
       in
       let tv2 = GSourceView2.source_view ~source_buffer:buf2 ~packing:(sw2#add)
	 ~show_line_numbers:false ~wrap_mode:`NONE() in
       let _ = tv2#misc#modify_font monospace_font in
       let _ = tv2#set_editable false in

       let buttonrun = toolbar#insert_button
	 ~text:" Run Alt-Ergo"
	 ~icon:(GMisc.image ~stock:`EXECUTE  ~icon_size:`LARGE_TOOLBAR()
	 )#coerce () in

       let buttonstop = toolbar#insert_button
	 ~text:" Abort"
	 ~icon:(GMisc.image ~stock:`STOP  ~icon_size:`LARGE_TOOLBAR()
	 )#coerce () in
	buttonstop#misc#hide ();

       toolbar#insert_space ();

       let resultbox = GPack.hbox () in
       let result_image = GMisc.image ~icon_size:`LARGE_TOOLBAR
	 ~stock:`DIALOG_QUESTION ~packing:resultbox#add () in
       let result_label = GMisc.label
	 ~text:" " ~packing:resultbox#add () in
       
       ignore(toolbar#insert_widget resultbox#coerce);
       
       let buttonclean = toolbar#insert_button
	 ~text:" Clean unused"
	 ~icon:(GMisc.image ~stock:`CLEAR  ~icon_size:`LARGE_TOOLBAR()
	 )#coerce () in
	buttonclean#misc#hide ();


       let thread = ref None in
       
       ignore(buttonrun#connect#clicked 
	 ~callback:(run buttonrun buttonstop buttonclean
		      result_image result_label thread env));

       ignore(buttonstop#connect#clicked 
	 ~callback:(kill_thread buttonrun buttonstop 
		      result_image result_label thread));

       ignore(eventBox#event#connect#key_press
		~callback:(toggle_ctrl env));

       ignore(eventBox#event#connect#key_release
		~callback:(toggle_ctrl env))
       
    ) typed_ast;

  w#show ();
  GtkThread.main ();
