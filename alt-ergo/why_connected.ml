open Why_annoted

open Lexing
open Format
open Options

    
let rec prune r t dep =
  r.pruned <- true;
  t#set_property (`FOREGROUND "light gray");
  let deps = match find_tag_inversedeps dep t  with 
    | None -> []
    | Some d -> d in
  List.iter (fun d -> prune d d.tag dep) deps

let rec unprune r t dep =
  r.pruned <- false;
  t#set_property (`FOREGROUND_SET false);
  let deps = match find_tag_deps dep t  with 
    | None -> []
    | Some d -> d in
  List.iter (fun d -> unprune d d.tag dep) deps

let prune_nodep r t =
  r.pruned <- true;
  t#set_property (`FOREGROUND "light gray")

let incorrect_prune_nodep r t =
  r.pruned <- true;
  t#set_property (`FOREGROUND "tomato")

let unprune_nodep r t =
  r.pruned <- false;
  t#set_property (`FOREGROUND_SET false)

let toggle_incorrect_prune r t =
  if r.pruned then unprune_nodep r t
  else incorrect_prune_nodep r t

let toggle_prune_nodep r t =
  if r.pruned then unprune_nodep r t
  else prune_nodep r t

let search_using t sbuf env =
  List.iter (fun t -> t#set_property (`BACKGROUND_SET false)) env.search_tags;
  match find t sbuf env.ast with
    | None -> ()
    | Some an -> match an with
	| AD (r,_) ->
	  let tags = findtags_using r.c env.ast in
	  env.search_tags <- tags;
	  List.iter (fun t -> t#set_property (`BACKGROUND "gold")) tags
	| AT {c = at} | AF ({c = AFatom (AApred at)}, _) ->
	  let tags = findtags_dep at env.ast in
	  env.search_tags <- tags;
	  List.iter (fun t -> t#set_property (`BACKGROUND "orange")) tags
	| AF _ | QF _ -> ()
    

(* let hand_cursor () = Gdk.Cursor.create `TARGET *)
    
(* let arrow_cursor () = Gdk.Cursor.create `ARROW *)

let tag_callback t env sbuf ~origin:y z i =
  match GdkEvent.get_type z with
    | `MOTION_NOTIFY ->
        if List.mem env.last_tag env.search_tags then 
          env.last_tag#set_properties 
	    [`BACKGROUND "gold"; `UNDERLINE_SET false]
	(* else if List.mem env.last_tag env.proof_tags then  *)
        (*   env.last_tag#set_properties  *)
	(*     [`BACKGROUND "lime green"; `UNDERLINE_SET false] *)
	(* else if List.mem env.last_tag env.proof_toptags then  *)
        (*   env.last_tag#set_properties  *)
	(*     [`BACKGROUND "pale green"; `UNDERLINE_SET false] *)
	else
          env.last_tag#set_properties 
	    [`BACKGROUND_SET false; `UNDERLINE_SET false];
        if env.ctrl then
	  begin
	    t#set_properties 
	      [`BACKGROUND "turquoise1"; `UNDERLINE `SINGLE]
	  end
	else
	  begin
	    t#set_property (`BACKGROUND "light blue")
	  end;                         
	env.last_tag <- t;
	true
    | `TWO_BUTTON_PRESS ->
	begin
	  match find t sbuf env.ast with
	    | None -> ()
	    | Some an -> match an with
		| AD (r,_) ->
		  if env.ctrl then 
		    if r.pruned then unprune r t env.dep 
		    else prune r t env.dep
		  else toggle_prune_nodep r t
		| AF (r, Some parent) ->
		  begin match parent.c, parent.polarity with
		    | AFop (AOPand, _), false | AFop (AOPor, _), true
		    | AFop (AOPimp, _), true | AFop (AOPiff, _), _ ->
		        toggle_incorrect_prune r t
		    | _ -> toggle_prune_nodep r t
		  end
		| AF (r, None) -> toggle_prune_nodep r t
		| AT r -> toggle_prune_nodep r t
		| QF _ -> ()
	end;
	true
    | `BUTTON_PRESS ->
	let z = GdkEvent.Button.cast z in
	if GdkEvent.Button.button z = 1 then
	  if env.ctrl then
	    (search_using t sbuf env;
	     true)
	  else
	  begin
	    let tyt = match find t sbuf env.ast with
	      | Some (AT at) ->
		  fprintf str_formatter ": %a" Ty.print at.c.at_ty;
		  flush_str_formatter ()
	      | Some (AF _) -> ": formula"
	      | Some (QF _) -> ": quantified formula"
	      | Some (AD ({c = AAxiom _}, _)) -> ": Axiom"
	      | Some (AD ({c = AGoal _}, _)) -> ": Goal"
	      | Some (AD ({c = ALogic _}, _)) -> ": Logic declaration"
	      | Some (AD ({c = APredicate_def _}, _)) -> ": Predicate definition"
	      | Some (AD ({c = AFunction_def _}, _)) -> ": Function definition"
	      | Some (AD ({c = ATypeDecl _}, _)) -> ": Type declaration"
	      | _ -> "" in
	    env.st_ctx#pop ();
	    ignore(env.st_ctx#push tyt);
	    true
	  end
	else false
    | _ -> false


let term_callback t env sbuf ~origin:y z i =
  if tag_callback t env sbuf ~origin:y z i = true then true
  else
    match GdkEvent.get_type z with
      | `BUTTON_PRESS ->
	  let z = GdkEvent.Button.cast z in
	  if GdkEvent.Button.button z = 1 then
	    begin
	      let tyt = match find t sbuf env.ast with
		| Some (AT at) ->
		    fprintf str_formatter ": %a" Ty.print at.c.at_ty;
		    flush_str_formatter ()
		| _ -> "" in
	      env.st_ctx#pop ();
	      ignore(env.st_ctx#push tyt);
	      true
	    end
	  else false
      | _ -> false
	  

let rec list_uquant_vars_in_form = function
  | AFatom _ -> []
  | AFop (op, aafl) ->
      List.fold_left (fun l aaf -> l@(list_uquant_vars_in_form aaf.c)) [] aafl
  | AFforall aqf ->
      let l = list_uquant_vars_in_form aqf.c.aqf_form.c in
      if aqf.polarity then
	aqf.c.aqf_bvars@l
      else l
  | AFexists aqf ->
      let l = list_uquant_vars_in_form aqf.c.aqf_form.c in
      if not aqf.polarity then
	aqf.c.aqf_bvars@l
      else l
  | AFlet (upvars, s, at, aaf) ->
      list_uquant_vars_in_form aaf.c
  | AFnamed (_, aaf) ->
      list_uquant_vars_in_form aaf.c

let rec list_vars_in_form = function
  | AFatom _ -> []
  | AFop (op, aafl) ->
      List.fold_left (fun l aaf -> l@(list_vars_in_form aaf.c)) [] aafl
  | AFforall aqf | AFexists aqf ->
      aqf.c.aqf_bvars@(list_vars_in_form aqf.c.aqf_form.c)
  | AFlet (upvars, s, at, aaf) ->
      list_vars_in_form aaf.c
  | AFnamed (_, aaf) ->
      list_vars_in_form aaf.c

let rec is_quantified_term vars at =
  match at.at_desc with
  | ATconst _ -> false
  | ATvar s ->
      List.fold_left 
	(fun b (s',_) -> b || (Symbols.equal s s')) false vars
  | ATapp (_, atl) ->
      List.fold_left
	(fun b at -> b || is_quantified_term vars at) false atl
  | ATget (at1, at2)
  | ATconcat (at1, at2)
  | ATinfix (at1, _, at2) ->
      is_quantified_term vars at1
      || is_quantified_term vars at2
  | ATprefix (_, at) ->
      is_quantified_term vars at
  | ATextract (at1, at2, at3)
  | ATset (at1, at2, at3) ->
      is_quantified_term vars at1
      || is_quantified_term vars at2
      || is_quantified_term vars at3
  | ATlet (s', at1, at2) ->
      let nvars =
	List.filter (fun (s'',_) -> not (Symbols.equal s' s'')) vars in
      is_quantified_term vars at1
      || is_quantified_term nvars at2

let unquantify_aaterm (buffer:sbuffer) at =
  new_annot buffer at.c (Why_typing.new_id ()) (tag buffer)

let unquantify_aatom (buffer:sbuffer) = function
  | AAtrue -> AAtrue
  | AAfalse -> AAfalse
  | AAeq aatl -> AAeq (List.map (unquantify_aaterm buffer) aatl)
  | AAneq aatl -> AAneq (List.map (unquantify_aaterm buffer) aatl)
  | AAdistinct aatl -> AAdistinct (List.map (unquantify_aaterm buffer) aatl)
  | AAle aatl -> AAle (List.map (unquantify_aaterm buffer) aatl)
  | AAlt aatl -> AAlt (List.map (unquantify_aaterm buffer) aatl)
  | AApred a -> AApred a
  | AAbuilt (h,aatl) -> AAbuilt (h, (List.map (unquantify_aaterm buffer) aatl))
         

let rec aterm_used_vars goal_vars at =
  match at.at_desc with
    | ATconst _ -> []
    | ATvar s ->
	(try [List.find (fun (s',_) -> Symbols.equal s s') goal_vars]
	 with Not_found ->  [])
    | ATapp (_, atl) ->
	List.fold_left (fun l at -> aterm_used_vars goal_vars at @ l) [] atl
    | ATprefix (_, at) | ATlet (_, _, at) -> aterm_used_vars goal_vars at
    | ATinfix (at1, _, at2) | ATget (at1, at2) | ATconcat (at1, at2) ->
	(aterm_used_vars goal_vars at1)@(aterm_used_vars goal_vars at2)
    | ATset (at1, at2, at3) | ATextract (at1, at2, at3) ->
	(aterm_used_vars goal_vars at1)@
	  (aterm_used_vars goal_vars at2)@
	  (aterm_used_vars goal_vars at3)


let rec unquantify_aform (buffer:sbuffer) tyenv vars_entries 
    used_vars goal_vars f pol =
  let ptag = (tag buffer) in
  let c, ve, goal_used = match f, pol with

    | AFatom aa, _ -> 
      AFatom (unquantify_aatom buffer aa), vars_entries, []

    | AFop (op, afl), _ ->
      let nafl, ve, goal_used = 
	List.fold_left (fun (nafl, ve, gu) af ->
	  let res, ve, gu' = unquantify_aform buffer tyenv ve used_vars 
	    goal_vars af.c af.polarity 
	in
	(res::nafl, ve, gu'@gu))
	([], vars_entries, []) afl in
      AFop (op, List.rev nafl), ve, goal_used

    | AFforall aaqf, true | AFexists aaqf, false ->
      let {aqf_bvars = bv; aqf_upvars = uv; aqf_triggers = atll; aqf_form = af}=
	aaqf.c in
      let nbv, used, goal_used, ve, _, lets =
	List.fold_left (fun (nbv, used, goal_used, ve, uplet, lets) v ->
	  let ((s, _) as v'), e = List.hd ve in
	  let cdr_ve = List.tl ve in
	  assert (v = v');
	  if e#text = "" then 
	    (v'::nbv, used, goal_used, cdr_ve, v'::uplet, lets)
	  else
	    let lb = Lexing.from_string e#text in
	    let lexpr = Why_parser.lexpr Why_lexer.token lb in
	    let at, gu =
	      try 
		let tt = Why_typing.term tyenv uplet lexpr in
		annot_of_tterm buffer tt, []
	      with Common.Error _ ->
		let gv = List.fold_left (fun acc v ->
		  if List.mem v uplet then acc
		  else v::acc) [] goal_vars
		in
		let tt = Why_typing.term tyenv (uplet@gv) lexpr in
		let at = annot_of_tterm buffer tt in
		at, aterm_used_vars gv at.c
	    in
	    (nbv, v'::used, gu@goal_used, cdr_ve, 
	     v'::uplet, (uplet, s, at)::lets))
	  ([], [], [], vars_entries, uv, []) bv in
      let aform, ve, gu =
	unquantify_aform buffer tyenv ve used goal_vars af.c af.polarity
      in
      let goal_used = gu@goal_used in
      let add_lets afc lets =
	List.fold_left
	  (fun af (u, s, at) -> 
	    new_annot buffer (AFlet (u, s, at.c, af))
	      (Why_typing.new_id ()) (tag buffer))
	  afc lets in
      if nbv = [] then (add_lets aform lets).c, ve, goal_used
      else 
	let aqf_triggers = 
	  List.map (List.map (unquantify_aaterm buffer)) atll in
	let aqf_triggers = List.filter
	  (fun aatl ->
	    (* TODO : change nbv with something else *)
	    List.filter (fun aat -> is_quantified_term nbv aat.c) aatl <> []
	  ) aqf_triggers in
	if aqf_triggers = [] then (add_lets aform lets).c, ve, goal_used
	else 
	  let c =
	    { aqf_bvars = nbv;
	      aqf_upvars = List.filter (fun v -> not (List.mem v used_vars)) uv;
	      aqf_triggers =  aqf_triggers;
	      aqf_form =  add_lets aform lets} in
	  (match f with
	    | AFforall _ -> 
	      AFforall (new_annot buffer c (Why_typing.new_id ()) (tag buffer)),
	      ve, goal_used
	    | AFexists _ -> 
	      AFexists (new_annot buffer c (Why_typing.new_id ()) (tag buffer)),
	      ve, goal_used
	    | _ -> assert false)

    | AFforall aaqf, false | AFexists aaqf, true ->
      let naqf_form, ve, goal_used =
	unquantify_aform buffer tyenv vars_entries used_vars goal_vars
	aaqf.c.aqf_form.c aaqf.c.aqf_form.polarity in
      let c = { aaqf.c with aqf_form = naqf_form } in
      (match f with
	| AFforall _ -> 
	  AFforall (new_annot buffer c (Why_typing.new_id ()) (tag buffer)),
	  ve, goal_used
	| AFexists _ -> 
	  AFexists (new_annot buffer c (Why_typing.new_id ()) (tag buffer)),
	  ve, goal_used
	| _ -> assert false)

    | AFlet (uv, s, at, aaf), _ ->
      let naaf, ve, goal_used = 
	unquantify_aform buffer tyenv vars_entries used_vars goal_vars
	  aaf.c aaf.polarity
      in
      AFlet (List.filter (fun v -> not (List.mem v used_vars)) uv, s, at, naaf),
      ve, goal_used

    | AFnamed (n, aaf), _ ->
      let naaf, ve, goal_used =
	unquantify_aform buffer tyenv vars_entries used_vars goal_vars
	  aaf.c aaf.polarity 
      in
      AFnamed (n, naaf), ve, goal_used
  in
  new_annot buffer c (Why_typing.new_id ()) ptag, ve, goal_used


let make_instance (buffer:sbuffer) vars (entries:GEdit.entry list)
    afc goal_form tyenv =
  let goal_vars = list_vars_in_form goal_form.c in
  if debug then List.iter (fun (v,e) ->
    eprintf "%a -> %s@." Symbols.print (fst v) e#text)
    (List.combine vars (List.rev entries));
  let aform, _, goal_used = 
    unquantify_aform buffer tyenv (List.combine vars (List.rev entries)) [] 
      goal_vars afc true
  in
  aform, goal_used
  



exception UncoveredVar of (Symbols.t * Ty.t)

type nestedq = Forall of aform annoted | Exists of aform annoted

let rec least_nested_form used_vars af =
  match used_vars, af.c with
    | [], _ -> Exists af
    | v::r, AFatom _ -> raise(UncoveredVar v)
    | v::r, AFop (op, aafl) ->
	let rec least_list = function
	   | [] -> raise(UncoveredVar v)
	   | af::l ->
	       try least_nested_form used_vars af
	       with UncoveredVar _ -> least_list l
	in least_list aafl
    | _, AFforall aqf ->
	let not_covered = List.fold_left
	  (fun l v ->
	     if List.mem v aqf.c.aqf_bvars then l else v::l (*XXX*)
	  ) [] used_vars in
	if not_covered = [] then Forall aqf.c.aqf_form
	else least_nested_form not_covered aqf.c.aqf_form
    | _, AFexists aqf ->
	let not_covered = List.fold_left
	  (fun l v ->
	     if List.mem v aqf.c.aqf_bvars then l else v::l (*XXX*)
	  ) [] used_vars in
	if not_covered = [] then Exists aqf.c.aqf_form
	else least_nested_form not_covered aqf.c.aqf_form
    | _, AFlet (upvars, s, at, af) ->
	least_nested_form used_vars af
    | _, AFnamed (_, af) -> 
	least_nested_form used_vars af

let rec add_instance env vars entries af aname =
  let ptag =  (tag env.inst_buffer) in
  let goal_form, tyenv, loc =
    let rec find_goal = function
      | [] -> raise Not_found
      | [gt] -> gt
      | x::r -> find_goal r in
    let g, tyenv = find_goal env.ast in
    match g.c with
      | AGoal (loc, _, f) -> f, tyenv, loc
      | _ -> raise Not_found
  in
  let instance, used_vars =
    make_instance env.inst_buffer vars entries af goal_form tyenv in
  let ln_form = least_nested_form used_vars goal_form in
  env.inst_buffer#place_cursor  ~where:env.inst_buffer#end_iter;
  if ln_form = Exists goal_form then begin
    let hy = AAxiom (loc, (sprintf "%s%s" "_instance_" aname), instance.c) in
    let ahy = new_annot env.inst_buffer hy instance.id ptag in
    let rev_ast = List.rev env.ast in
    let rev_ast = match rev_ast with 
      | (g,te)::l -> (g,te)::(ahy, te)::l
      | _ -> assert false
    in
    env.ast <- List.rev rev_ast;
    connect_tag env env.inst_buffer ahy.tag;
    connect_aaform env env.inst_buffer instance;
    add_to_buffer env.inst_buffer [ahy, tyenv] 
  end
  else begin
    let instance = new_annot env.inst_buffer instance.c instance.id ptag in
    begin match ln_form with 
      | Exists lnf ->
	lnf.c <- 
	  AFop 
	  (AOPand, 
	   [instance; {lnf with c = lnf.c}])
      | Forall lnf ->
	lnf.c <- 
	  AFop 
	  (AOPimp, 
	   [instance; {lnf with c = lnf.c}])
    end;
    env.inst_buffer#insert ~tags:[instance.tag] ("instance "^aname^": \n");
    connect_aaform env env.inst_buffer instance;
    env.inst_buffer#insert (String.make indent_size ' ');
    add_aaform env.inst_buffer 1 [] instance;
    env.inst_buffer#insert "\n\n";
  end
    
  

and popup_axiom t env offset () =
    let pop_w = GWindow.dialog
    ~title:"Instantiate axiom"
    ~allow_grow:true
    ~width:400 ()
    (* ~icon:(GdkPixbuf.from_xpm_data Logo.xpm_logo) ()  *)
    in
  let bbox = GPack.button_box `HORIZONTAL ~border_width:5 ~layout:`END
    ~child_height:20 ~child_width:85 ~spacing:10
    ~packing:pop_w#action_area#add () in

  let button_ok = GButton.button ~packing:bbox#add () in
  let phbox = GPack.hbox ~packing:button_ok#add () in
  ignore(GMisc.image ~stock:`OK ~packing:phbox#add ());
  ignore(GMisc.label ~text:"OK" ~packing:phbox#add ());

  let button_cancel = GButton.button ~packing:bbox#add () in
  let phbox = GPack.hbox ~packing:button_cancel#add () in
  ignore(GMisc.image ~stock:`CANCEL ~packing:phbox#add ());
  ignore(GMisc.label ~text:"Cancel" ~packing:phbox#add ());
  
  let vars, entries, af, aname = (match find t env.buffer env.ast with
    | Some (AD (atd, tyenv)) -> 
      begin
	  match atd.c with
	    | AAxiom (_, aname, af) ->
		pop_w#set_title ("Instantiate axiom "^aname)
	    | APredicate_def (_, aname,_ , af) ->
		pop_w#set_title ("Instantiate predicate "^aname)
	    | _ -> assert false
      end;
      begin
	  match atd.c with
	    | AAxiom (_, aname, af)
	    | APredicate_def (_, aname,_ , af) ->
		let vars = list_uquant_vars_in_form af in
		let rows = List.length vars in
		let table = GPack.table ~rows ~columns:2 ~homogeneous:false
		  ~border_width:5 ~packing:pop_w#vbox#add () in
		let entries,_ = List.fold_left
		  (fun (entries,i) (s,ty) ->
		     fprintf str_formatter "%a : %a = " 
		       Symbols.print s Ty.print ty;
		     let text = flush_str_formatter () in
		     ignore(
		       GMisc.label ~text ~xalign:1.0
			 ~packing:(table#attach ~left:0 ~top:i) ());
		     let entries =
		       (GEdit.entry ~text:""
			  ~packing:(table#attach ~left:1 ~top:i
				      ~expand:`BOTH ~shrink:`BOTH) ()
		       )::entries in
		     entries, i+1
		  ) ([],0) vars in
		vars, entries, af, aname
	    | _ -> assert false
	end
    | _ -> assert false)
  in
    		
  let errors_l = GMisc.label ~text:"" ~packing:pop_w#vbox#pack () in
  errors_l#misc#modify_fg [`NORMAL, `NAME "red"];
  errors_l#misc#hide ();
  
  ignore(button_ok#connect#clicked ~callback:
	   (fun () ->
	      try
		add_instance env vars entries af aname;
		pop_w#destroy ()
		  
	      with 
		| Why_lexer.Lexical_error s -> 
		    errors_l#set_text ("Lexical error");
		    errors_l#misc#show ()
		| Parsing.Parse_error ->
		    errors_l#set_text ("Syntax error");
		    errors_l#misc#show ()
		| Common.Error (e,_) ->
		    fprintf str_formatter "Typing error : %a" Common.report e;
		    errors_l#set_text (flush_str_formatter ());
		    errors_l#misc#show ()
	   ));
  
  ignore(button_cancel#connect#clicked ~callback: pop_w#destroy);
  pop_w#show ()


and axiom_callback t env ~origin:y z i =
  let ni = new GText.iter i in
  let offset = ni#offset in
  if tag_callback t env env.buffer ~origin:y z i = true then true
  else
    begin
      match GdkEvent.get_type z with
	| `BUTTON_PRESS ->
	    let z = GdkEvent.Button.cast z in
	    if GdkEvent.Button.button z = 3 then
	      let menu = GMenu.menu () in
	      let image = GMisc.image ~stock:`ADD () in
	      let menuitem = GMenu.image_menu_item ~image
		~label:"Instanciate axiom ..." ~packing:menu#append () in
	      ignore(menuitem#connect#activate
		       ~callback:(popup_axiom t env offset));
	      menu#popup ~button:3 ~time:(GdkEvent.Button.time z);
	      true
	    else
	      false
	| _ -> false
    end








and popup_trigger t env (sbuf:sbuffer) offset () =
    let pop_w = GWindow.dialog
    ~title:"Add new (multi) trigger"
    ~allow_grow:true
    ~width:400 ()
    (* ~icon:(GdkPixbuf.from_xpm_data Logo.xpm_logo) ()  *)
    in
  let bbox = GPack.button_box `HORIZONTAL ~border_width:5 ~layout:`END
    ~child_height:20 ~child_width:85 ~spacing:10
    ~packing:pop_w#action_area#add () in
  
  let button_ok = GButton.button ~packing:bbox#add () in
  let phbox = GPack.hbox ~packing:button_ok#add () in
  ignore(GMisc.image ~stock:`OK ~packing:phbox#add ());
  ignore(GMisc.label ~text:"OK" ~packing:phbox#add ());

  let button_cancel = GButton.button ~packing:bbox#add () in
  let phbox = GPack.hbox ~packing:button_cancel#add () in
  ignore(GMisc.image ~stock:`CANCEL ~packing:phbox#add ());
  ignore(GMisc.label ~text:"Cancel" ~packing:phbox#add ());

  let lmanager = GSourceView2.source_language_manager ~default:true in
  let source_language = lmanager#language "alt-ergo" in
  let buf1 = match source_language with 
    | Some language -> GSourceView2.source_buffer ~language
	~highlight_syntax:true ~highlight_matching_brackets:true ()
    | None -> GSourceView2.source_buffer () in
  let sw1 = GBin.scrolled_window
    ~vpolicy:`AUTOMATIC 
    ~hpolicy:`AUTOMATIC
    ~packing:pop_w#vbox#add () in
  let tv1 = GSourceView2.source_view ~source_buffer:buf1 ~packing:(sw1#add) 
	 ~show_line_numbers:true ~wrap_mode:`CHAR() in
  let _ = tv1#misc#modify_font monospace_font in
  let _ = tv1#set_editable true in
		
  let errors_l = GMisc.label ~text:"" ~packing:pop_w#vbox#pack () in
  errors_l#misc#modify_fg [`NORMAL, `NAME "red"];
  errors_l#misc#hide ();
    
  ignore(button_ok#connect#clicked
    ~callback: 
    (fun () ->
       let iter = sbuf#get_iter (`OFFSET offset) in
       try begin
	 match sbuf#forward_iter_to_source_mark ~category:"trigger" iter with
	   | true ->
	       begin
		 match find_decl t sbuf env.ast, find t sbuf env.ast with
		   | Some (AD (_, tyenv)), Some (QF qf) ->
		       
		       (* let iter = sbuf#get_iter_at_marker m in *)
		       let tags = iter#tags in
		       let iter = sbuf#get_iter
			 (`OFFSET (iter#offset - 2)) in
		       let str = buf1#get_text () in
		       
		       let lb = Lexing.from_string str in
		       let lexprs = Why_parser.trigger Why_lexer.token lb in
		       let atl = List.fold_right
			 (fun lexpr l->
			    let tt = Why_typing.term tyenv
			      (qf.c.aqf_upvars@qf.c.aqf_bvars) lexpr in
			    let at = annot_of_tterm sbuf tt in
			    at.tag#set_priority (t#priority - 1);
			    connect_aaterm env sbuf connect_tag at;
			    at::l
			 ) lexprs [] in		       
		       sbuf#insert ~iter ~tags " | ";
		       add_aaterm_list_at sbuf tags iter "," atl;
		       qf.c.aqf_triggers <- qf.c.aqf_triggers@[atl];
		   | _ -> assert false
	       end
	   | false -> ()
       end;
	 pop_w#destroy ()
       with 
    | Why_lexer.Lexical_error s -> 
	errors_l#set_text ("Lexical error");
	errors_l#misc#show ()
    | Parsing.Parse_error ->
	errors_l#set_text ("Syntax error");
	errors_l#misc#show ()
    | Common.Error (e,_) ->
	fprintf str_formatter "Typing error : %a" Common.report e;
	errors_l#set_text (flush_str_formatter ());
	errors_l#misc#show ()
    ));
  ignore(button_cancel#connect#clicked ~callback: pop_w#destroy);
  pop_w#show ()

and triggers_callback t env sbuf ~origin:y z i =
  
  let ni = new GText.iter i in
  let offset = ni#offset in
  if tag_callback t env sbuf ~origin:y z i = true then true
  else
    begin
      match GdkEvent.get_type z with
	| `BUTTON_PRESS ->
	    let z = GdkEvent.Button.cast z in
	    if GdkEvent.Button.button z = 3 then
	      let menu = GMenu.menu () in
	      let image = GMisc.image ~stock:`ADD () in
	      let menuitem = GMenu.image_menu_item ~image
		~label:"Add trigger(s) ..." ~packing:menu#append () in
	      ignore(menuitem#connect#activate
		       ~callback:(popup_trigger t env sbuf offset));
	      menu#popup ~button:3 ~time:(GdkEvent.Button.time z);
	      true
	    else
	      false
	| _ -> false
    end


(* let triggers_tag (buffer:sbuffer) = *)
(*   let t = buffer#create_tag [`EDITABLE true; `BACKGROUND "orange"] in *)
(*   ignore (t#connect#event ~callback:(set_mark t buffer)); *)
(*   (\* ignore (t#connect#event ~callback:(fetch_text t buffer)); *\) *)
(*   t *)
  

and connect_tag env sbuf t =
  ignore (t#connect#event ~callback:(tag_callback t env sbuf))

and connect_term env sbuf t =
  ignore (t#connect#event ~callback:(term_callback t env sbuf))

and connect_trigger_tag env sbuf t =
  ignore (t#connect#event ~callback:(triggers_callback t env sbuf))

and connect_axiom_tag env t =
  ignore (t#connect#event ~callback:(axiom_callback t env))

and connect_aterm env sbuf 
    { at_desc = at_desc } =
  connect_at_desc env sbuf at_desc

and connect_aterm_list env sbuf atl =
  List.iter (connect_aterm env sbuf) atl

and connect_aaterm env sbuf connect_tag aat =
  connect_tag env sbuf aat.tag;
  connect_aterm env sbuf aat.c

and connect_aaterm_list env sbuf 
    connect_tag aatl =
  List.iter (connect_aaterm env sbuf connect_tag) aatl

and connect_at_desc env sbuf = function
    | ATconst _ | ATvar _ -> ()
    | ATapp (s, atl) -> connect_aterm_list env sbuf atl
    | ATinfix (t1, _, t2) | ATget (t1, t2)
    | ATconcat (t1, t2) | ATlet (_, t1, t2) ->
	connect_aterm env sbuf t1;
	connect_aterm env sbuf t2
    | ATprefix (_, t) -> connect_aterm env sbuf t
    | ATset (t1,t2,t3) | ATextract (t1,t2,t3) ->
	connect_aterm env sbuf t1;
	connect_aterm env sbuf t2;
	connect_aterm env sbuf t3
	
and connect_aatom env sbuf aa =
  match aa with
    | AAtrue
    | AAfalse -> ()

    | AAeq atl
    | AAneq atl
    | AAdistinct atl
    | AAle atl
    | AAlt atl
    | AAbuilt (_, atl) -> connect_aaterm_list env sbuf connect_tag atl

    | AApred at -> connect_aterm env sbuf at

and connect_quant_form env sbuf
    {aqf_triggers = trs; aqf_form = aaf } =
  connect_triggers env sbuf trs;
  connect_aaform env sbuf aaf

and connect_triggers env sbuf trs =
  List.iter (connect_aaterm_list env sbuf connect_tag) trs
      
and connect_aform env sbuf = function
  | AFatom a -> connect_aatom env sbuf a
  | AFop (op, afl) -> connect_aaform_list env sbuf afl
  | AFforall aqf
  | AFexists aqf -> 
      connect_trigger_tag env sbuf aqf.tag;
      connect_quant_form env sbuf aqf.c
  | AFlet (vs, s, t, aaf) ->
      connect_aterm env sbuf t;      
      connect_aform env sbuf aaf.c
  | AFnamed (_, aaf) ->
      connect_aform env sbuf aaf.c

and connect_aaform_list env sbuf aafl =
  List.iter (connect_aaform env sbuf) aafl

and connect_aaform env sbuf aaf =
  connect_tag env sbuf aaf.tag;
  connect_aform env sbuf aaf.c

let connect_atyped_decl env td =
  match td.c with
    | APredicate_def (_, _, _, af)
    | AAxiom (_, _, af) ->
	connect_axiom_tag env td.tag;
	connect_aform env env.buffer af
    | ARewriting (_, _, arwtl) ->
	connect_tag env env.buffer td.tag
	(* TODO *)
    | AGoal (_, _, aaf) ->
	connect_tag env env.buffer td.tag;
	connect_aform env env.buffer aaf.c
    | AFunction_def (_, _, _, _, af) ->
	connect_tag env env.buffer td.tag;
	connect_aform env env.buffer af	
    | ALogic _
    | ATypeDecl _ ->
	connect_tag env env.buffer td.tag
	
let connect env =
  List.iter (fun (t, _) -> connect_atyped_decl env t) env.ast

let clear_used_lemmas_tags env =
  List.iter (fun t -> t#set_property (`BACKGROUND_SET false)) env.proof_tags;
  List.iter (fun t -> t#set_property (`BACKGROUND_SET false)) env.proof_toptags;
  env.proof_tags <- [];
  env.proof_toptags <- []
  

let show_used_lemmas env expl =
  let atags,ftags = findtags_proof expl env.ast in
  clear_used_lemmas_tags env;
  List.iter (fun t -> t#set_property (`BACKGROUND "pale green")) atags;
  List.iter (fun t -> t#set_property (`BACKGROUND "green")) ftags;
  env.proof_tags <- ftags;
  env.proof_toptags <- atags
  

(* More efficient but invariant broken when using user instanciated axioms
let prune_unused env expl =
  let ids = match Explanation.ids_of expl with
    | None -> []
    | Some ids -> List.sort Pervasives.compare ids 
  in
  let prune_top d = match d.c with
    | ATypeDecl _ | AGoal _ | ALogic _ -> ()
    | _ -> prune_nodep d d.tag
  in
  let rec aux dont ast ids =
    match ast, ids with
      | [], _ | _, [] -> ()
	
      | (d, _)::rast, id::rids ->
	if id = d.id then (* is d *)
	  aux false rast rids
	else if id < d.id then (* in d *)
	  aux true ast rids
      	else (* not in d *)
      	  begin
	    if not dont then prune_top d;
      	    aux false rast ids
      	  end
  in
  aux false env.ast ids
*)

let prune_unused env =
  let prune_top d = match d.c with
    | ATypeDecl _ | AGoal _ | ALogic _ -> ()
    | _ -> prune_nodep d d.tag
  in
  List.iter (fun (d, _) -> 
    if not (List.mem d.ptag env.proof_toptags) 
      && not (List.mem d.ptag env.proof_tags) 
    then prune_top d
  ) env.ast
