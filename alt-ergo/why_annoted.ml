open Why_ptree

open Lexing
open Format
open Options

let indent_size = 4
let monospace_font = Pango.Font.from_string "mono"
let general_font = Pango.Font.from_string "sans"

type sbuffer = GSourceView2.source_buffer

type 'a annoted =
    { mutable c : 'a; 
      mutable pruned : bool;
      mutable polarity : bool;
      tag : GText.tag;
      ptag : GText.tag;
      id : int;
      buf : sbuffer }

type aterm = 
    { at_ty : Ty.t; at_desc : at_desc }

and at_desc = 
  | ATconst of tconstant
  | ATvar of Symbols.t
  | ATapp of Symbols.t * aterm list
  | ATinfix of aterm * Symbols.t * aterm
  | ATprefix of Symbols.t * aterm 
  | ATget of aterm * aterm
  | ATset of aterm * aterm * aterm
  | ATextract of aterm * aterm * aterm
  | ATconcat of aterm * aterm
  | ATlet of Symbols.t * aterm * aterm
      

type aatom = 
  | AAtrue
  | AAfalse
  | AAeq of aterm annoted list
  | AAneq of aterm annoted list
  | AAdistinct of aterm annoted list
  | AAle of aterm annoted list
  | AAlt of aterm annoted list
  | AApred of aterm
  | AAbuilt of Hstring.t * aterm annoted list

type aoplogic =
    AOPand |AOPor | AOPimp | AOPnot | AOPif of aterm | AOPiff 

type aquant_form = {       
  aqf_bvars : (Symbols.t * Ty.t) list ;
  aqf_upvars : (Symbols.t * Ty.t) list ;
  mutable aqf_triggers : aterm annoted list list ;
  aqf_form : aform annoted
}

and aform =
  | AFatom of aatom
  | AFop of aoplogic * aform annoted list
  | AFforall of aquant_form annoted
  | AFexists of aquant_form annoted
  | AFlet of (Symbols.t * Ty.t) list * Symbols.t * aterm * aform annoted
  | AFnamed of Hstring.t * aform annoted

type atyped_decl = 
  | AAxiom of loc * string * aform
  | ARewriting of loc * string * ((aterm rwt_rule) annoted) list
  | AGoal of loc * string * aform annoted
  | ALogic of loc * string list * plogic_type
  | APredicate_def of loc * string * (string * ppure_type) list * aform
  | AFunction_def 
      of loc * string * (string * ppure_type) list * ppure_type * aform
  | ATypeDecl of loc * string list * string * string list


type annoted_node =
  | AD of (atyped_decl annoted * Why_typing.env)
  | AF of aform annoted * aform annoted option
  | AT of aterm annoted
  | QF of aquant_form annoted



module MDep = Map.Make (
  struct
    type t = atyped_decl annoted
    let compare = compare
  end)


type env = {
  buffer : sbuffer;
  inst_buffer : sbuffer;
  st_ctx : GMisc.statusbar_context;
  mutable ast : (atyped_decl annoted * Why_typing.env) list;
  mutable ctrl : bool;
  mutable last_tag : GText.tag;
  mutable search_tags : GText.tag list;
  mutable proof_tags : GText.tag list;
  mutable proof_toptags : GText.tag list;
  dep : (atyped_decl annoted list * atyped_decl annoted list) MDep.t
}

let create_env buf1 (buf2:sbuffer) st_ctx ast dep  =
  let titag = buf2#create_tag [`WEIGHT `BOLD; `UNDERLINE `SINGLE] in
  buf2#insert ~tags:[titag] "User instantiated axioms:\n\n";
  {
    buffer = buf1;
    inst_buffer = buf2;
    st_ctx = st_ctx;
    ast = ast;
    dep = dep;
    ctrl = false;
    last_tag = GText.tag ();
    search_tags = [];
    proof_tags = [];
    proof_toptags = [];
  }


let tag (buffer:sbuffer) = buffer#create_tag []

let new_annot (buffer:sbuffer) c id ptag =
  { c = c; pruned = false; tag = (tag buffer); 
    ptag = ptag;id = id; polarity = true; buf = buffer }


let rec findin_aterm tag buffer { at_desc = at_desc } =
  findin_at_desc tag buffer at_desc

and findin_aterm_list tag buffer atl =
  List.fold_left
    (fun r at -> match r with
       | None -> findin_aterm tag buffer at
       | Some _ -> r
    ) None atl

and findin_aaterm tag buffer aat =
  let goodbuf =  aat.buf#get_oid = buffer#get_oid in
  let c = compare tag#priority aat.tag#priority in
  if goodbuf && c = 0 then Some (AT aat)
  else if goodbuf && c > 0 then None
  else findin_aterm tag buffer aat.c

and findin_aaterm_list tag buffer aatl =
  List.fold_left
    (fun r aat -> match r with
       | None -> findin_aaterm tag buffer aat
       | Some _ -> r
    ) None aatl

and findin_at_desc tag buffer = function
    | ATconst _
    | ATvar _ -> None
    | ATapp (s, atl) -> findin_aterm_list tag buffer atl
    | ATinfix (t1, _, t2) | ATget (t1,t2)
    | ATconcat (t1, t2) | ATlet (_, t1, t2) ->
	let r = findin_aterm tag buffer t1 in
	if r = None then findin_aterm tag buffer t2
	else r
    | ATprefix (_,t) -> findin_aterm tag buffer t
    | ATset (t1, t2, t3) | ATextract (t1, t2, t3)  ->
	let r = findin_aterm tag buffer t1 in
	if r = None then
	  let r = findin_aterm tag buffer t2 in
	  if r = None then findin_aterm tag buffer t3
	  else r
	else r
	
let findin_aatom tag buffer aa =
  match aa with
    | AAtrue
    | AAfalse -> None

    | AAeq atl
    | AAneq atl
    | AAdistinct atl
    | AAle atl
    | AAlt atl
    | AAbuilt (_, atl) -> findin_aaterm_list tag buffer atl

    | AApred at -> findin_aterm tag buffer at

let rec findin_quant_form tag buffer parent {aqf_triggers = trs; aqf_form = aaf } =
  let r = findin_triggers tag buffer trs in
  if r = None then 
    let goodbuf =  aaf.buf#get_oid = buffer#get_oid in
    let c = compare tag#priority aaf.tag#priority in
    if goodbuf && c = 0 then Some (AF (aaf, parent))
    else if goodbuf && c > 0 then None
    else findin_aform tag buffer (Some aaf) aaf.c
  else r

and findin_triggers tag buffer trs =
  List.fold_left
    (fun r aatl -> match r with
       | None -> findin_aaterm_list tag buffer aatl
       | Some _ -> r
    ) None trs
      
and findin_aform tag buffer parent aform =
  match aform with
    | AFatom a -> findin_aatom tag buffer a
    | AFop (op, afl) -> findin_aaform_list tag buffer parent afl
    | AFforall qf
    | AFexists qf -> 
	let goodbuf =  qf.buf#get_oid = buffer#get_oid in
	let c = compare tag#priority qf.tag#priority in
	if goodbuf && c = 0 then Some (QF qf)
	else if goodbuf && c > 0 then None
	else findin_quant_form tag buffer parent qf.c
    | AFlet (vs, s, t, aaf) ->
	let r = findin_aterm tag buffer t in
	if r = None then findin_aaform tag buffer parent aaf
	else r
    | AFnamed (_, aaf) ->
	findin_aform tag buffer parent aaf.c

and findin_aaform_list tag buffer parent aafl =
  List.fold_left
    (fun r aaf -> match r with
       | None -> findin_aaform tag buffer parent aaf
       | Some _ -> r
    ) None aafl

and findin_aaform tag buffer parent aaf =
  let goodbuf =  aaf.buf#get_oid = buffer#get_oid in
  let c = compare tag#priority aaf.tag#priority in
  if goodbuf && c = 0 then Some (AF (aaf, parent))
  else if goodbuf && c > 0 then None
  else findin_aform tag buffer (Some aaf) aaf.c

let findin_atyped_delc tag buffer (td, env) stop_decl =
  let goodbuf =  td.buf#get_oid = buffer#get_oid in
  let c = compare tag#priority td.tag#priority in
  if goodbuf && c = 0 then Some (AD (td, env))
  else if goodbuf && c > 0 then None
  else if stop_decl then Some (AD (td, env))
  else match td.c with
    | AAxiom (_, _, af)
    | APredicate_def (_, _, _, af)
    | AFunction_def (_, _, _, _, af) ->
        let aaf = new_annot buffer af (-1) tag in
	(* TODO: Change this so af is annoted *)
	findin_aform tag buffer (Some aaf) af
    | ARewriting (_, _, rwtl) -> None
        (*List.fold_left 
	  (fun {rwt_left = rl; rwt_right = rr} acc -> match acc with
	    | Some _ -> acc
	    | None -> findin_aterm_list tag buffer [rl; rr]
	  ) rwtl None*)
    | AGoal (_, _, aaf) ->
	let goodbuf =  aaf.buf#get_oid = buffer#get_oid in
	let c = compare tag#priority aaf.tag#priority in
	if goodbuf && c = 0 then Some (AF (aaf, None))
	else if goodbuf && c > 0 then None
	else findin_aform tag buffer (Some aaf) aaf.c
    | ALogic _
    | ATypeDecl _ ->
	None
	  
let find_aux stop_decl tag buffer l =
  List.fold_left
    (fun r td -> match r with
       | None -> findin_atyped_delc tag buffer td stop_decl
       | Some _ -> r
    ) None l

let find = find_aux false

let find_decl = find_aux true




let rec print_ppure_type fmt = function
  | PPTunit -> fprintf fmt "unit"
  | PPTint -> fprintf fmt "int"
  | PPTbool -> fprintf fmt "bool"
  | PPTreal -> fprintf fmt "real"
  | PPTbitv size -> fprintf fmt "bitv[%d]" size
  | PPTvarid (s, loc) -> fprintf fmt "\'%s" s
  (* | PPTfarray pp -> fprintf fmt "%a farray" print_ppure_type pp *)
  | PPTexternal ([], s, loc) ->
      fprintf fmt "%s" s
  | PPTexternal (pptypes, s, loc) ->
      fprintf fmt "%a %s" (print_ppure_type_list true) pptypes s
      
and print_ppure_type_list nested fmt l =
  let rec aux fmt = function
    | [] -> ()
    | [p] -> print_ppure_type fmt p
    | p::r -> fprintf fmt "%a,%a" print_ppure_type p aux r
  in
  if not nested then aux fmt l
  else match l with
    | [] -> ()
    | [s] -> aux fmt l
    | s::r -> fprintf fmt "(%a)" aux l

let print_plogic_type fmt = function
  | PPredicate [] -> fprintf fmt "prop"
  | PPredicate pptl -> 
      fprintf fmt "%a -> prop" (print_ppure_type_list false) pptl
  | PFunction ([], ppt) ->
	fprintf fmt "%a" print_ppure_type ppt
  | PFunction (pptl, ppt) ->
      fprintf fmt "%a -> %a" (print_ppure_type_list false) pptl 
	print_ppure_type ppt


let print_tconstant fmt = function
  | Tvoid -> fprintf fmt "void"
  | Ttrue -> fprintf fmt "true"
  | Tfalse -> fprintf fmt "false"
  | Tint s -> fprintf fmt "%s" s
  | Treal n -> fprintf fmt "%s" (Num.string_of_num n)
  | Tbitv s -> fprintf fmt "%s" s

let tconstant_to_string = function
  | Tvoid -> "void"
  | Ttrue -> "true"
  | Tfalse -> "false"
  | Tint s -> s
  | Treal n -> Num.string_of_num n
  | Tbitv s -> s

let rec print_var_list fmt = function
  | [] -> ()
  | [s,ty] -> fprintf fmt "%a:%a" Symbols.print s Ty.print ty
  | (s,ty)::l ->
      fprintf fmt "%a:%a,%a" Symbols.print s Ty.print ty print_var_list l


let rec print_string_sep sep fmt = function
  | [] -> ()
  | [s] -> fprintf fmt "%s" s
  | s::r -> fprintf fmt "%s%s%a" s sep (print_string_sep sep) r

let rec print_string_list fmt = print_string_sep "," fmt

let print_astring_list fmt l =
  let rec aux fmt = function
    | [] -> ()
    | [s] -> fprintf fmt "\'%s" s
    | s::r -> fprintf fmt "\'%s,%a" s aux r
  in
  match l with
    | [] -> ()
    | [s] -> aux fmt l
    | s::r -> fprintf fmt "(%a)" aux l

let rec print_string_ppure_type_list fmt = function
  | [] -> ()
  | [s,ppt] -> fprintf fmt "%s:%a" s print_ppure_type ppt
  | (s,ppt)::l -> fprintf fmt "%s:%a,%a" s print_ppure_type ppt
      print_string_ppure_type_list l

let print_pred_type_list fmt = function
  | [] -> ()
  | l -> fprintf fmt "(%a)" print_string_ppure_type_list l


(**************** to delete *******************)

let rec print_tterm fmt {Why_ptree.c= {tt_desc = tt_desc}} =
  print_tt_desc fmt tt_desc

and print_tterm_list se fmt = function
  | [] -> ()
  | [t] -> print_tterm fmt t
  | t::r -> fprintf fmt "%a%s%a" print_tterm t se (print_tterm_list se) r

and print_tt_desc fmt = function
  | TTconst c -> print_tconstant fmt c
  | TTvar s -> Symbols.print fmt s
  | TTapp (f, ts) ->
      fprintf fmt "%a(%a)" Symbols.print f (print_tterm_list ",") ts
  | TTinfix (t1, s, t2) ->
      fprintf fmt "%a %a %a" print_tterm t1 Symbols.print s print_tterm t2
  | TTprefix (s, t) ->
      fprintf fmt "%a %a" Symbols.print s print_tterm t
  | TTlet (s, t1, t2) -> 
      fprintf fmt "let %a = %a in %a"
	Symbols.print s print_tterm t1 print_tterm t2
  | TTconcat (t1, t2) ->
      fprintf fmt "%a@%a" print_tterm t1 print_tterm t2
  | TTextract (t, t1, t2) -> 
      fprintf fmt "%a^{%a;%a}" print_tterm t print_tterm t1 print_tterm t2
  | TTset (t, t1, t2) ->
      fprintf fmt "%a[%a<-%a]" print_tterm t print_tterm t1 print_tterm t2
  | TTget (t, t1) ->
      fprintf fmt "%a[%a]" print_tterm t print_tterm t1

let print_tatom fmt a = match a.Why_ptree.c with
  | TAtrue -> fprintf fmt "true" 
  | TAfalse -> fprintf fmt "false"
  | TAeq tl -> print_tterm_list " = " fmt tl
  | TAneq tl -> print_tterm_list " <> " fmt tl
  | TAdistinct tl ->
      fprintf fmt "distinct(%a)" (print_tterm_list ",") tl
  | TAle tl -> print_tterm_list " <= " fmt tl
  | TAlt tl -> print_tterm_list " < " fmt tl
  | TApred t -> print_tterm fmt t
  | TAbuilt (h, tl) -> print_tterm_list (" "^(Hstring.view h)^" ") fmt tl

let print_oplogic fmt = function
  | OPand -> fprintf fmt "and"
  | OPor -> fprintf fmt "or"
  | OPimp -> fprintf fmt "->"
  | OPnot -> fprintf fmt "not"
  | OPif t -> fprintf fmt "%a ->" print_tterm t
  | OPiff -> fprintf fmt "<->"

let print_rwt fmt { rwt_vars = rv; rwt_left = rl; rwt_right = rr } =
  fprintf fmt "forall %a. %a = %a" 
    print_var_list rv print_tterm rl print_tterm rr

let rec print_rwt_list fmt = function
  | [] -> ()
  | [rwt] -> print_rwt fmt rwt
  | rwt::l -> fprintf fmt "%a; %a" print_rwt rwt print_rwt_list l

let rec print_quant_form fmt
    {qf_bvars = bv; qf_upvars = uv; qf_triggers = trs; qf_form = tf } =
  fprintf fmt "%a [%a]. %a"
    print_var_list bv print_triggers trs print_tform tf

and print_triggers fmt = function
  | [] -> ()
  | [ts] -> print_tterm_list "," fmt ts
  | ts::l -> fprintf fmt "%a | %a" (print_tterm_list ",") ts print_triggers l

and print_tform2 fmt f = match f.Why_ptree.c with
  | TFatom a -> print_tatom fmt a
  | TFop (OPnot, [tf]) -> fprintf fmt "not %a" print_tform tf 
  | TFop (op, tfl) -> print_tform_list op fmt tfl
  | TFforall qf -> fprintf fmt "forall %a" print_quant_form qf
  | TFexists qf -> fprintf fmt "exists %a" print_quant_form qf
  | TFlet (vs, s, t, tf) -> 
      fprintf fmt "let %a = %a in\n %a" 
	Symbols.print s print_tterm t print_tform tf
  | TFnamed (_, tf) -> print_tform fmt tf

and print_tform fmt f = fprintf fmt " (id:%d)%a" f.Why_ptree.annot print_tform2 f

and print_tform_list op fmt = function
  | [] -> ()
  | [tf] -> print_tform fmt tf
  | tf::l -> fprintf fmt "%a %a %a"
      print_tform tf print_oplogic op (print_tform_list op) l

let print_typed_decl fmt td = match td.Why_ptree.c with
  | TAxiom (_, s, tf) -> fprintf fmt "axiom %s : %a" s print_tform tf
  | TRewriting (_, s, rwtl) -> 
    fprintf fmt "rewriting %s : %a" s print_rwt_list rwtl
  | TGoal (_, s, tf) -> fprintf fmt "goal %s : %a" s print_tform tf
  | TLogic (_, ls, ty) ->
      fprintf fmt "logic %a : %a" print_string_list ls print_plogic_type ty
  | TPredicate_def (_, p, spptl, tf) ->
      fprintf fmt "predicate %s %a = %a" p
	print_pred_type_list spptl print_tform tf
  | TFunction_def (_, f, spptl, ty, tf) ->
      fprintf fmt "function %s (%a) : %a = %a" f
	print_string_ppure_type_list spptl print_ppure_type ty print_tform tf
  | TTypeDecl (_, ls, s, []) -> fprintf fmt "type %a %s" print_astring_list ls s
  | TTypeDecl (_, ls, s, lc) -> 
    fprintf fmt "type %a %s = %a" print_astring_list ls s 
      (print_string_sep " | ") lc

let print_typed_decl_list fmt = List.iter (fprintf fmt "%a@." print_typed_decl)

(**********************************************)



(****************** Computing dependancies ***********************)

let find_dep_by_string dep s =
  MDep.fold
    (fun d _ found ->
       match found with
	 | Some _ -> found
	 | None -> begin
	     match d.c with
	       | ALogic (_, ls, ty) when List.mem s ls -> Some d
	       | ATypeDecl (_, _, s', _) when s = s'-> Some d
	       | APredicate_def (_, p, _, _) when s = p -> Some d
	       | AFunction_def (_, f, _, _, _) when s = f -> Some d
	       | _ -> None
	   end
    ) dep None

let find_tag_deps dep tag =
  MDep.fold
    (fun d (deps,_) found ->
       match found with
	 | Some _ -> found
	 | None -> if d.tag = tag then Some deps else None
    ) dep None

let find_tag_inversedeps dep tag =
  MDep.fold
    (fun d (_,deps) found ->
       match found with
	 | Some _ -> found
	 | None -> if d.tag = tag then Some deps else None
    ) dep None

let make_dep_string d ex dep s =
  if not (List.mem s ex) then
    let m = find_dep_by_string dep s in
    match m with
      | None -> dep
      | Some d' ->
	  let deps, depsi =
	    try MDep.find d' dep
	    with Not_found -> [], [] in
	  let dep = MDep.add d' (deps, d::depsi) dep in
	  let deps, depsi =
	    try MDep.find d dep
	    with Not_found -> [], [] in
	  MDep.add d (d'::deps, depsi) dep
  else dep

let rec make_dep_aterm d ex dep {at_desc = at_desc; at_ty = at_ty } =
  make_dep_at_desc d ex dep at_desc

and make_dep_aaterm d ex dep aat = make_dep_aterm d ex dep aat.c

and make_dep_at_desc d ex dep = function
    | ATconst _ -> dep
    | ATvar s  -> make_dep_string d ex dep (Symbols.to_string s)
    | ATapp (s, atl)  ->
	let dep = make_dep_string d ex dep (Symbols.to_string s) in
	List.fold_left (make_dep_aterm d ex) dep atl
    | ATinfix (t1, s, t2)  ->
	let dep = make_dep_aterm d ex dep t1 in
	let dep = make_dep_string d ex dep (Symbols.to_string s) in
	make_dep_aterm d ex dep t2
    | ATprefix (s, t) ->
	let dep = make_dep_string d ex dep (Symbols.to_string s) in
	make_dep_aterm d ex dep t
    | ATget (t1, t2) | ATconcat (t1, t2) ->
	let dep = make_dep_aterm d ex dep t1 in
	make_dep_aterm d ex dep t2
    | ATset (t1, t2, t3) | ATextract (t1, t2, t3)  ->
	let dep = make_dep_aterm d ex dep t1 in
	let dep = make_dep_aterm d ex dep t2 in
	make_dep_aterm d ex dep t3
    | ATlet (s, t1, t2) ->
	let dep = make_dep_string d ex dep (Symbols.to_string s) in
	let dep = make_dep_aterm d ex dep t1 in
	make_dep_aterm d ex dep t2	

let make_dep_aatom d ex dep = function
  | AAtrue | AAfalse -> dep
  | AAeq atl | AAneq atl | AAdistinct atl | AAle atl | AAlt atl ->
      List.fold_left (make_dep_aaterm d ex) dep atl
  | AApred at -> make_dep_aterm d ex dep at
  | AAbuilt (h, atl) -> List.fold_left (make_dep_aaterm d ex) dep atl

let make_dep_oplogic d ex dep = function
  | AOPif at -> make_dep_aterm d ex dep at
  | _ -> dep

let rec make_dep_quant_form d ex dep
    {aqf_bvars = bv; aqf_upvars = uv; aqf_triggers = trs; aqf_form = aaf } =
  let vars = List.map (fun (s,_) -> (Symbols.to_string s)) bv in
  make_dep_aform d (vars@ex) dep aaf.c
      
and make_dep_aform d ex dep = function
  | AFatom a -> make_dep_aatom d ex dep a
  | AFop (op, afl) ->
      List.fold_left (make_dep_aaform d ex) dep afl
  | AFforall qf -> make_dep_quant_form d ex dep qf.c
  | AFexists qf -> make_dep_quant_form d ex dep qf.c
  | AFlet (vs, s, t, aaf) ->
      let dep = make_dep_aterm d ex dep t in
      make_dep_aaform d ex dep aaf
  | AFnamed (_, aaf) ->
      make_dep_aform d ex dep aaf.c

and make_dep_aaform d ex dep aaf = make_dep_aform d ex dep aaf.c

let make_dep_atyped_decl dep d =
  match d.c with
  | AAxiom (loc, s, af) -> make_dep_aform d [] dep af
  | ARewriting (loc, s, arwtl) ->
      List.fold_left
	(fun dep r ->
	  let vars = List.map 
	    (fun (s,_) -> (Symbols.to_string s)) r.c.rwt_vars in
	  let dep = make_dep_aterm d vars dep r.c.rwt_left in
	  make_dep_aterm d vars dep r.c.rwt_right
	) dep arwtl
  | AGoal (loc, s, aaf) -> make_dep_aform d [] dep aaf.c
  | ALogic (loc, ls, ty) -> MDep.add d ([], []) dep
  | APredicate_def (loc, p, spptl, af) ->
      let dep = MDep.add d ([], []) dep in
      make_dep_aform d (p::(List.map fst spptl)) dep af
  | AFunction_def (loc, f, spptl, ty, af) ->
      let dep = MDep.add d ([], []) dep in
      make_dep_aform d (f::(List.map fst spptl)) dep af
  | ATypeDecl (loc, ls, s, lc) -> MDep.add d ([], []) dep

let make_dep annoted_ast =
  let dep = MDep.empty in
  List.fold_left (fun dep (t,_) -> make_dep_atyped_decl dep t) dep annoted_ast


(* Translation from AST to annoted/pruned AST *)


let annot_of_tconstant (buffer:sbuffer)  t =
  new_annot buffer t

let rec of_tterm (buffer:sbuffer) t =
  {at_desc = of_tt_desc buffer t.Why_ptree.c.tt_desc;
   at_ty = t.Why_ptree.c.tt_ty }

and annot_of_tterm (buffer:sbuffer) t =
  let ptag = tag buffer in
  let c = of_tterm buffer t in
  new_annot buffer c t.Why_ptree.annot ptag

and of_tt_desc (buffer:sbuffer) = function
  | TTconst c -> (ATconst c)
  | TTvar s  ->(ATvar s)
  | TTapp (s, tts)  ->
      ATapp (s, List.map (of_tterm buffer ) tts)
  | TTinfix (t1, s, t2)  ->
      ATinfix (of_tterm buffer t1, s, of_tterm buffer t2)
  | TTprefix (s,t) -> ATprefix (s, of_tterm buffer t)
  | TTget (t1, t2) -> ATget (of_tterm buffer t1, of_tterm buffer t2)
  | TTset (t, t1, t2) ->
      ATset (of_tterm buffer t, of_tterm buffer t1, of_tterm buffer t2)
  | TTextract (t, t1, t2) ->
      ATextract (of_tterm buffer t, of_tterm buffer t1, of_tterm buffer t2)
  | TTconcat (t1, t2) -> ATconcat (of_tterm buffer t1, of_tterm buffer t2)
  | TTlet (s, t1, t2) -> ATlet (s, of_tterm buffer t1, of_tterm buffer t2)

let of_tatom (buffer:sbuffer) a = match a.Why_ptree.c with
  | TAtrue -> AAtrue
  | TAfalse -> AAfalse
  | TAeq tl -> AAeq (List.map (annot_of_tterm buffer ) tl)
  | TAneq tl -> AAneq (List.map (annot_of_tterm buffer ) tl)
  | TAdistinct tl -> AAdistinct (List.map (annot_of_tterm buffer ) tl)
  | TAle tl -> AAle (List.map (annot_of_tterm buffer ) tl)
  | TAlt tl -> AAlt (List.map (annot_of_tterm buffer ) tl)
  | TApred t -> AApred (of_tterm buffer  t)
  | TAbuilt (h, tl) -> AAbuilt (h, (List.map (annot_of_tterm buffer ) tl))

let of_oplogic (buffer:sbuffer)  = function
  | OPand -> AOPand
  | OPor -> AOPor
  | OPimp -> AOPimp 
  | OPnot -> AOPnot
  | OPif t -> AOPif (of_tterm buffer  t)
  | OPiff -> AOPiff 

let rec change_polarity_aform f = 
  f.polarity <- not f.polarity;
  match f.c with
    | AFatom _ -> ()
    | AFop (_, afl) -> List.iter change_polarity_aform afl
    | AFforall aaqf | AFexists aaqf ->
      aaqf.polarity <- not aaqf.polarity;
      change_polarity_aform aaqf.c.aqf_form
    | AFlet (_,_,_,af) | AFnamed (_, af) -> change_polarity_aform af
	

let rec of_quant_form (buffer:sbuffer)   
    {qf_bvars = bv; qf_upvars = uv; qf_triggers = trs; qf_form = tf } =
  let ptag = tag buffer in
  { aqf_bvars = bv;
    aqf_upvars = uv;
    aqf_triggers = List.map (List.map (annot_of_tterm buffer )) trs;
    aqf_form = new_annot buffer (of_tform buffer tf) tf.Why_ptree.annot ptag}

and annot_of_quant_form (buffer:sbuffer) qf =
  let ptag = tag buffer in
  new_annot buffer (of_quant_form buffer qf) (-1) ptag

and of_tform (buffer:sbuffer) f = match f.Why_ptree.c with
  | TFatom a -> AFatom (of_tatom buffer a)
  | TFop (op, tfl) ->
    let afl = List.map (annot_of_tform buffer ) tfl in
    assert (let l = List.length afl in l >= 1 && l <= 2);
    if op = OPnot || op = OPimp then 
      change_polarity_aform (List.hd afl);
    AFop (of_oplogic buffer  op, afl)
  | TFforall qf -> AFforall (annot_of_quant_form buffer qf)
  | TFexists qf -> AFexists (annot_of_quant_form buffer qf)
  | TFlet (vs, s, t, tf) ->
      AFlet (vs, s, of_tterm buffer  t, annot_of_tform buffer tf)
  | TFnamed (n, tf) -> 
      AFnamed (n, annot_of_tform buffer tf)

and annot_of_tform (buffer:sbuffer) t =
  let ptag = tag buffer in
  let c = of_tform buffer t in
  new_annot buffer c t.Why_ptree.annot ptag

let annot_of_typed_decl (buffer:sbuffer) td = 
  let ptag = tag buffer in
  let c = match td.Why_ptree.c with
    | TAxiom (loc, s, tf) -> AAxiom (loc, s, of_tform buffer tf)
    | TRewriting (loc, s, rwtl) ->
      let arwtl = List.map 
	(fun rwt ->
	  new_annot buffer
	    { rwt with 
	      rwt_left = of_tterm buffer rwt.rwt_left;
	      rwt_right = of_tterm buffer rwt.rwt_right }
	    td.Why_ptree.annot ptag
	) rwtl in
      ARewriting (loc, s, arwtl)
    | TGoal (loc, s, tf) ->
        let g = new_annot buffer (of_tform buffer tf) tf.Why_ptree.annot ptag in
        AGoal (loc, s, g)
    | TLogic (loc, ls, ty) -> ALogic (loc, ls, ty)
    | TPredicate_def (loc, p, spptl, tf) ->
        APredicate_def (loc, p,  spptl, of_tform buffer  tf)
    | TFunction_def (loc, f, spptl, ty, tf) ->
        AFunction_def (loc, f,  spptl, ty, of_tform buffer  tf)
    | TTypeDecl (loc, ls, s, lc) -> ATypeDecl (loc, ls, s, lc)
  in
  new_annot buffer c td.Why_ptree.annot ptag


let annot (buffer:sbuffer) ast =
  List.map (fun (t,env) -> (annot_of_typed_decl buffer t, env)) ast

(* Translation from annoted/pruned AST to AST *)

let rec to_tterm id {at_desc = at_desc; at_ty = at_ty } =
  {Why_ptree.c = { tt_desc = to_tt_desc at_desc; tt_ty = at_ty };
   Why_ptree.annot = id }

and from_aaterm_list = function
  | [] -> []
  | at::l ->
      if at.pruned then from_aaterm_list l
      else (to_tterm at.id at.c)::(from_aaterm_list l)

and to_tt_desc = function
    | ATconst c -> TTconst c
    | ATvar s  -> TTvar s
    | ATapp (s, atl)  -> TTapp (s, List.map (to_tterm 0) atl)
    | ATinfix (t1, s, t2) -> TTinfix (to_tterm 0 t1, s, to_tterm 0 t2)
    | ATprefix (s, t) -> TTprefix (s, to_tterm 0 t)
    | ATget (t1, t2) -> TTget (to_tterm 0 t1, to_tterm 0 t2)
    | ATset (t1, t2, t3) -> TTset (to_tterm 0 t1, to_tterm 0 t2, to_tterm 0 t3)
    | ATextract (t1, t2, t3) ->
	TTextract (to_tterm 0 t1, to_tterm 0 t2, to_tterm 0 t3)
    | ATconcat (t1, t2) -> TTconcat (to_tterm 0 t1, to_tterm 0 t2)
    | ATlet (s, t1, t2) -> TTlet (s, to_tterm 0 t1, to_tterm 0 t2)

let to_tatom aa id = 
  let c = match aa with 
    | AAtrue -> TAtrue
    | AAfalse -> TAfalse
    | AAeq atl -> TAeq (from_aaterm_list atl)
    | AAneq atl -> TAneq (from_aaterm_list atl)
    | AAdistinct atl -> TAdistinct (from_aaterm_list atl)
    | AAle atl -> TAle (from_aaterm_list atl)
    | AAlt atl -> TAlt (from_aaterm_list atl)
    | AApred at -> TApred (to_tterm 0 at)
    | AAbuilt (h, atl) -> TAbuilt (h, (from_aaterm_list atl))
  in 
  { Why_ptree.c = c;
    Why_ptree.annot = id }

let to_oplogic = function
  | AOPand -> OPand
  | AOPor -> OPor
  | AOPimp  -> OPimp
  | AOPnot -> OPnot
  | AOPif at -> OPif (to_tterm 0 at)
  | AOPiff -> OPiff

let rec to_quant_form
    {aqf_bvars = bv; aqf_upvars = uv; aqf_triggers = trs; aqf_form = aaf } =
  { qf_bvars = bv;
    qf_upvars = uv;
    qf_triggers = to_triggers trs;
    qf_form = to_tform aaf
  }
  
and to_triggers = function
  | [] -> []
  | atl::l ->
      let l' = from_aaterm_list atl in
      if l' = [] then to_triggers l
      else l'::(to_triggers l)

and void_to_tform af id = 
  let c = match af with
    | AFatom a -> TFatom (to_tatom a id)
    | AFop (op, afl) ->
      let tfl = from_aaform_list afl in
      let op = to_oplogic op in
      begin
	match tfl, op with
	  | [], _ -> failwith "Empty logic operation"
	  | [tf], OPnot -> TFop (op, tfl)
	  | [tf], _ -> tf.Why_ptree.c
	  | _ -> TFop (op, tfl)
      end
    | AFforall qf -> TFforall (to_quant_form qf.c)
    | AFexists qf -> TFexists (to_quant_form qf.c)
    | AFlet (vs, s, t, aaf) -> TFlet (vs, s, to_tterm 0 t, to_tform aaf)
    | AFnamed (n, aaf) -> TFnamed (n, to_tform aaf)
  in
  { Why_ptree.c = c;
    Why_ptree.annot = id }
      
and to_tform aaf = void_to_tform aaf.c aaf.id

and from_aaform_list = function
  | [] -> []
  | aaf::l ->
      if aaf.pruned then from_aaform_list l
      else
	let l = from_aaform_list l in
	try (to_tform aaf)::l
	with Failure "Empty logic operation" -> l

let to_typed_decl td =
  let c = match td.c with
    | AAxiom (loc, s, af) -> 
      let af = void_to_tform af td.id in
      TAxiom (loc, s, af)
    | ARewriting (loc, s, arwtl) -> 
      let rwtl = List.fold_left (fun rwtl ar ->
	if ar.pruned then rwtl
	else { rwt_vars = ar.c.rwt_vars;
	       rwt_left = to_tterm ar.id ar.c.rwt_left;
	       rwt_right = to_tterm ar.id ar.c.rwt_right}::rwtl
      ) [] arwtl in
      TRewriting (loc, s, rwtl)
    | AGoal (loc, s, aaf) -> TGoal (loc, s, to_tform aaf)
    | ALogic (loc, ls, ty) -> TLogic (loc, ls, ty)
    | APredicate_def (loc, p, spptl, af) ->
      TPredicate_def (loc, p, spptl, void_to_tform af td.id)
    | AFunction_def (loc, f, spptl, ty, af) ->
      TFunction_def (loc, f, spptl, ty, void_to_tform af td.id)
    | ATypeDecl (loc, ls, s, lc) -> TTypeDecl (loc, ls, s, lc)
  in
  { Why_ptree.c = c;
    Why_ptree.annot = td.id }


let rec to_ast = function
  | [] -> []
  | (atd, _)::l ->
      if atd.pruned then to_ast l
      else (to_typed_decl atd)::(to_ast l)



let rec add_aterm_at (buffer:sbuffer) tags iter
    {at_desc = at_desc; at_ty = at_ty } =
  add_at_desc_at buffer tags iter at_desc

and add_aterm (buffer:sbuffer) tags tt =
  add_aterm_at buffer tags buffer#end_iter tt

and add_aterm_list_at (buffer:sbuffer) tags iter sep =
  function
    | [] -> ()
    | [at] -> add_aterm_at buffer tags iter at;
    | at::l ->
	add_aterm_at buffer tags iter at;
	buffer#insert ~iter ~tags sep;
	add_aterm_list_at buffer tags iter sep l

and add_aaterm_at (buffer:sbuffer) tags iter at =
  add_aterm_at buffer (at.tag::at.ptag::tags) iter at.c

and add_aaterm (buffer:sbuffer) tags at =
  add_aaterm_at buffer tags buffer#end_iter at

and add_aaterm_list_at (buffer:sbuffer) tags iter sep =
  function
    | [] -> ()
    | [at] -> add_aaterm_at buffer tags iter at;
    | at::l ->
	add_aaterm_at buffer tags iter at;
	buffer#insert ~iter ~tags sep;
	add_aaterm_list_at buffer tags iter sep l

and add_aaterm_list (buffer:sbuffer) tags sep atl =
  add_aaterm_list_at buffer tags buffer#end_iter sep atl

and add_at_desc_at (buffer:sbuffer) tags iter at =
  (* let off1 = iter#offset in *)
  (* let off = off1 - (buffer#get_iter (`OFFSET off1))#line_offset in *)
  (* print_endline (sprintf "%d" off); *)
  (* let iter = buffer#get_iter (`OFFSET off1) in *)
  match at with
    | ATconst c ->
	buffer#insert ~iter ~tags
	  (sprintf "%s" (tconstant_to_string c))
    | ATvar s  -> 
	buffer#insert ~iter ~tags (sprintf "%s" (Symbols.to_string s))
    | ATapp (s, atl)  ->
	buffer#insert ~iter ~tags 
	  (sprintf "%s(" (Symbols.to_string s));
	add_aterm_list_at buffer tags iter "," atl;
	buffer#insert ~iter ~tags ")"
    | ATinfix (t1, s, t2)  ->
	add_aterm_at buffer tags iter t1;
	buffer#insert ~iter ~tags
	  (sprintf " %s " (Symbols.to_string s));
	add_aterm_at buffer tags iter t2
    | ATprefix (s, t) ->
	buffer#insert ~iter ~tags
	  (sprintf " %s " (Symbols.to_string s));
	add_aterm_at buffer tags iter t
    | ATget (t1, t2) ->
	add_aterm_at buffer tags iter t1;
	buffer#insert ~iter ~tags "[";
	add_aterm_at buffer tags iter t2;
	buffer#insert ~iter ~tags "]"
    | ATset (t1, t2, t3) ->
	add_aterm_at buffer tags iter t1;
	buffer#insert ~iter ~tags "[";
	add_aterm_at buffer tags iter t2;
	buffer#insert ~iter ~tags "<-";
	add_aterm_at buffer tags iter t3;
	buffer#insert ~iter ~tags "]"
    | ATextract (t1, t2, t3) ->
	add_aterm_at buffer tags iter t1;
	buffer#insert ~iter ~tags "^{";
	add_aterm_at buffer tags iter t2;
	buffer#insert ~iter ~tags ",";
	add_aterm_at buffer tags iter t3;
	buffer#insert ~iter ~tags "}"
    | ATconcat (t1, t2) ->
	add_aterm_at buffer tags iter t1;
	buffer#insert ~iter ~tags "@";
	add_aterm_at buffer tags iter t2
    | ATlet (s, t1, t2) ->
	buffer#insert ~iter ~tags 
	  (sprintf "let %s = " (Symbols.to_string s));
	add_aterm_at buffer tags iter t1;
	buffer#insert ~iter ~tags " in ";
	add_aterm_at buffer tags iter t2

	
	
let add_aatom (buffer:sbuffer) indent tags aa =
  buffer#insert (String.make (indent * indent_size) ' ');
  match aa with
  | AAtrue -> buffer#insert ~tags "true"
  | AAfalse -> buffer#insert ~tags "false"
  | AAeq atl -> add_aaterm_list buffer tags " = " atl
  | AAneq atl -> add_aaterm_list buffer tags " <> " atl
  | AAdistinct atl  ->
    buffer#insert ~tags "distinct(";
    add_aaterm_list buffer tags "," atl;
    buffer#insert  ~tags ")"
  | AAle atl -> add_aaterm_list buffer tags " <= " atl
  | AAlt atl -> add_aaterm_list buffer tags " < " atl
  | AApred at -> add_aterm buffer tags at
  | AAbuilt (h, atl) ->
      add_aaterm_list buffer tags (" "^(Hstring.view h)^" ") atl

let add_oplogic (buffer:sbuffer) indent tags op =
  match op with
  | AOPand -> buffer#insert ~tags "and "
  | AOPor -> buffer#insert ~tags "or  "
  | AOPimp  -> buffer#insert ~tags "->  "
  | AOPnot -> buffer#insert ~tags "not "
  | AOPif at ->
      buffer#insert (String.make indent ' ');
      buffer#insert ~tags "if  ";
      add_aterm buffer tags at;
      buffer#insert ~tags "  then"
  | AOPiff -> buffer#insert ~tags "<-> "

let add_rwt (buffer:sbuffer) indent tags r =
  let { rwt_vars = rv; rwt_left = rl; rwt_right = rr } = r.c in
  let tags = r.tag::r.ptag::tags in
  buffer#insert (String.make (indent * indent_size) ' ');
  buffer#insert ~tags "forall ";
  fprintf str_formatter "%a. " print_var_list rv;
  buffer#insert ~tags (flush_str_formatter ());
  add_aterm buffer tags rl;
  buffer#insert ~tags " = ";
  add_aterm buffer tags rr

let rec add_rwt_list (buffer:sbuffer) indent tags = function
  | [] -> ()
  | [r] -> add_rwt buffer indent tags r
  | r::l -> 
    add_rwt buffer indent tags r;
    buffer#insert ~tags ";";
    buffer#insert "\n";
    add_rwt_list buffer indent tags l

let rec add_quant_form (buffer:sbuffer) indent tags qf =
  let {aqf_bvars = bv; aqf_upvars = uv; aqf_triggers = trs; aqf_form = aaf } =
    qf.c in
  fprintf str_formatter "%a " print_var_list bv;
  buffer#insert ~tags (flush_str_formatter ());
  let ntags = qf.tag::qf.ptag::tags in
  buffer#insert ~tags:ntags "[";
  add_triggers buffer ntags trs;
  buffer#insert ~tags:ntags "].";
  ignore(buffer#create_source_mark ~category:"trigger" buffer#end_iter);
  buffer#insert "\n";
  buffer#insert (String.make ((indent + 1)* indent_size) ' ');
  add_aaform buffer (indent+1) tags aaf

and add_triggers (buffer:sbuffer) tags = function
  | [] -> ()
  | [atl] -> add_aaterm_list buffer tags "," atl
  | atl::l -> 
      add_aaterm_list buffer tags "," atl;
      buffer#insert ~tags " | ";
      add_triggers buffer tags l
      
and add_aform (buffer:sbuffer) indent tags aform =
  match aform with
  | AFatom a -> add_aatom buffer 0 tags a
  | AFop (op, afl) -> add_aaform_list buffer indent tags op afl
  | AFforall qf ->
      buffer#insert ~tags "forall ";
      add_quant_form buffer indent tags qf
  | AFexists qf ->
      buffer#insert ~tags "exists ";
      add_quant_form buffer indent tags qf
  | AFlet (vs, s, t, aaf) ->
      buffer#insert ~tags 
	(sprintf "let %s = " (Symbols.to_string s));
      add_aterm buffer tags t;
      buffer#insert ~tags " in";
      buffer#insert "\n";
      buffer#insert (String.make (indent * indent_size) ' ');
      add_aaform buffer (indent) tags aaf
  | AFnamed (n, aaf) ->
      buffer#insert ~tags (sprintf "%s: " (Hstring.view n));
      add_aform buffer indent tags aaf.c
      

and add_aaform_list (buffer:sbuffer) indent tags op l =
  if l = [] then ()
  else begin
    (* add_aaform buffer indent tags (List.hd l); *)
    add_aaform_list_aux buffer indent tags op l
  end
   
and add_aaform_list_aux (buffer:sbuffer) indent tags op =
  function
  | [] -> ()
  | [af] ->
      add_oplogic buffer indent tags op;
      add_aaform buffer indent tags af
  | af1::af2::l ->
      add_aaform buffer indent tags af1;
      buffer#insert "\n";
      buffer#insert (String.make (indent * indent_size) ' ');
      add_oplogic buffer indent tags op;
      add_aaform buffer (indent+1) tags af2;
      add_aaform_list buffer (indent+1) tags op l      
  (* | af::l -> *)
  (*     buffer#insert "\n"; *)
  (*     buffer#insert (String.make (indent * indent_size) ' '); *)
  (*     add_oplogic buffer indent tags op; *)
  (*     add_aaform buffer indent tags af; *)
  (*     add_aaform_list buffer (indent+1) tags op l *)


and add_aaform (buffer:sbuffer) indent tags
    {c = af; tag = tag; ptag = ptag} =
  add_aform buffer indent (tag::ptag::tags) af

let add_atyped_decl (buffer:sbuffer) d =
  match d.c with
  | AAxiom (loc, s, af) ->
      let keyword = 
	if String.length s > 0 && s.[0] = '_' 
	then "hypothesis" else "axiom" in
      buffer#insert ~tags:[d.tag;d.ptag] (sprintf "%s %s :" keyword s);
      buffer#insert "\n";
      buffer#insert (String.make indent_size ' ');
      add_aform buffer 1 [d.tag;d.ptag] af;
      buffer#insert "\n\n"

  | ARewriting (loc, s, arwtl) ->
      buffer#insert ~tags:[d.tag;d.ptag] (sprintf "rewriting %s :" s);
      buffer#insert "\n";
      add_rwt_list buffer 1 [d.tag;d.ptag] arwtl;
      buffer#insert "\n\n"

  | AGoal (loc, s, aaf) -> 
      buffer#insert ~tags:[d.tag;d.ptag] (sprintf "goal %s :" s);
      buffer#insert "\n";
      buffer#insert (String.make indent_size ' ');
      add_aform buffer 1 [d.tag;d.ptag] aaf.c;
      buffer#insert "\n\n"

  | ALogic (loc, ls, ty) ->
      fprintf str_formatter 
	"logic %a : %a" print_string_list ls print_plogic_type ty;
      buffer#insert ~tags:[d.tag;d.ptag] (flush_str_formatter());
      buffer#insert "\n\n"

  | APredicate_def (loc, p, spptl, af) ->
      fprintf str_formatter "predicate %s %a =" p print_pred_type_list spptl;
      buffer#insert ~tags:[d.tag;d.ptag] (flush_str_formatter());
      buffer#insert "\n";
      buffer#insert (String.make indent_size ' ');
      add_aform buffer 1 [d.tag;d.ptag] af;
      buffer#insert "\n\n"

  | AFunction_def (loc, f, spptl, ty, af) ->
      fprintf str_formatter "function %s (%a) : %a =" f
	print_string_ppure_type_list spptl print_ppure_type ty;
      buffer#insert ~tags:[d.tag;d.ptag] (flush_str_formatter());
      buffer#insert "\n";
      buffer#insert (String.make indent_size ' ');
      add_aform buffer 1 [d.tag;d.ptag] af;
      buffer#insert "\n\n"
      
  | ATypeDecl (loc, ls, s, []) -> 
      fprintf str_formatter "type %a %s" print_astring_list ls s;
      buffer#insert ~tags:[d.tag;d.ptag] (flush_str_formatter());
      buffer#insert "\n\n"
      
  | ATypeDecl (loc, ls, s, lc) -> 
      fprintf str_formatter "type %a %s = %a"
	print_astring_list ls s (print_string_sep " | ") lc;
      buffer#insert ~tags:[d.tag;d.ptag] (flush_str_formatter());
      buffer#insert "\n\n"



let add_to_buffer (buffer:sbuffer) annoted_ast =
  List.iter (fun (t, _) -> add_atyped_decl buffer t) annoted_ast








let rec isin_aterm sl { at_desc = at_desc } =
  match at_desc with
    | ATconst _ -> false
    | ATvar sy -> 
      List.mem (Symbols.to_string sy) sl
    | ATapp (sy, atl) -> 
      List.mem (Symbols.to_string sy) sl || isin_aterm_list sl atl
    | ATinfix (t1, _, t2) | ATget (t1,t2)
    | ATconcat (t1, t2) | ATlet (_, t1, t2) ->
      isin_aterm sl t1 || isin_aterm sl t2
    | ATprefix (_,t) -> isin_aterm sl t
    | ATset (t1, t2, t3) | ATextract (t1, t2, t3)  ->
      isin_aterm sl t1 || isin_aterm sl t2 || isin_aterm sl t3 

and isin_aterm_list sl atl =
  List.fold_left
    (fun is at -> is || isin_aterm sl at
    ) false atl

and findtags_aaterm sl aat acc =
  match aat.c.at_desc with
    | ATconst _ -> acc
    | ATvar sy -> 
      if List.mem (Symbols.to_string sy) sl then aat.tag::acc else acc
    | ATapp (sy, atl) -> 
      if List.mem (Symbols.to_string sy) sl || isin_aterm_list sl atl
      then aat.tag::acc else acc
    | ATinfix (t1, _, t2) | ATget (t1,t2)
    | ATconcat (t1, t2) | ATlet (_, t1, t2) ->
      if isin_aterm sl t1 || isin_aterm sl t2 then aat.tag::acc else acc
    | ATprefix (_,t) -> if isin_aterm sl t then aat.tag::acc else acc
    | ATset (t1, t2, t3) | ATextract (t1, t2, t3)  ->
      if isin_aterm sl t1 || isin_aterm sl t2 || isin_aterm sl t3 
      then aat.tag::acc else acc

and findtags_aaterm_list sl aatl acc =
  List.fold_left
    (fun acc aat ->
      findtags_aaterm sl aat acc
    ) acc aatl
	
let findtags_aatom sl aa acc =
  match aa with
    | AAtrue
    | AAfalse -> acc

    | AAeq atl
    | AAneq atl
    | AAdistinct atl
    | AAle atl
    | AAlt atl
    | AAbuilt (_, atl) -> findtags_aaterm_list sl atl acc

    | AApred at -> acc

let rec findtags_quant_form sl {aqf_triggers = trs; aqf_form = aaf } acc =
  let acc = findtags_triggers sl trs acc in
  findtags_aform sl aaf.c acc

and findtags_triggers sl trs acc =
  List.fold_left
    (fun acc aatl ->
       findtags_aaterm_list sl aatl acc
    ) acc trs
      
and findtags_aform sl aform acc =
  match aform with
    | AFatom a -> findtags_aatom sl a acc
    | AFop (op, afl) -> findtags_aaform_list sl afl acc
    | AFforall qf
    | AFexists qf -> findtags_quant_form sl qf.c acc
    | AFlet (vs, sy, t, aaf) ->
        (* let acc = findtags_aterm sl t acc in *)
        let s = Symbols.to_string sy in
	let sl = List.fold_left (fun l s' -> if s' = s then l else s'::l) [] sl
	in
	findtags_aform sl aaf.c acc
    | AFnamed (_, aaf) ->
	findtags_aform sl aaf.c acc

and findtags_aaform_list sl aafl acc =
  List.fold_left
    (fun acc aaf -> findtags_aaform sl aaf acc
    ) acc aafl

and findtags_aaform sl aaf acc =
  match aaf.c with
    | AFatom (AApred at) when isin_aterm sl at -> aaf.tag::acc
    | _ -> findtags_aform sl aaf.c acc

let findtags_atyped_delc sl td acc =
  match td.c with
    | AAxiom (_, _, af)
    | APredicate_def (_, _, _, af)
    | AFunction_def (_, _, _, _, af) ->
	findtags_aform sl af acc
    | ARewriting (_, _, rwtl) -> acc
    | AGoal (_, _, aaf) ->
	findtags_aform sl aaf.c acc
    | ALogic _
    | ATypeDecl _ -> acc
	  
let findtags sl l =
  List.fold_left
    (fun acc (td, _) -> findtags_atyped_delc sl td acc
    ) [] l

let findtags_using r l =
  match r with
    | AAxiom _
    | ARewriting _
    | AGoal _
    | ATypeDecl _ -> []

    | ALogic (_, sl, _) -> findtags sl l
      
    | APredicate_def (_, s, _, _)
    | AFunction_def (_, s, _, _, _) -> findtags [s] l

let rec listsymbols at acc =
  match at.at_desc with
    | ATconst _ -> acc
    | ATvar sy -> (Symbols.to_string sy)::acc
    | ATapp (sy, atl) ->
      List.fold_left (fun acc at -> listsymbols at acc) 
	((Symbols.to_string sy)::acc) atl
    | ATinfix (t1, _, t2) | ATget (t1,t2)
    | ATconcat (t1, t2) | ATlet (_, t1, t2) ->
      listsymbols t1 (listsymbols t2 acc)
    | ATprefix (_,t) -> listsymbols t acc
    | ATset (t1, t2, t3) | ATextract (t1, t2, t3)  ->
      listsymbols t1 (listsymbols t2 (listsymbols t3 acc))

let findtags_atyped_delc_dep sl td acc =
  match td.c with
    | ALogic (_, ls, _) ->
      let ne = List.fold_left (fun ne s -> ne || List.mem s sl) false ls in
      if ne then td.tag::acc else acc
    | APredicate_def (_, p, _, _) when List.mem p sl -> td.tag::acc
    | AFunction_def (_, f, _, _, _) when List.mem f sl -> td.tag::acc
    | _ -> acc

let findtags_dep at l =
  let sl = listsymbols at [] in
  List.fold_left (fun acc (td, _) -> findtags_atyped_delc_dep sl td acc) [] l
  
let rec findproof_aform ids af acc found =
  match af with
    | AFatom at -> acc, found
    | AFop (_, aafl) ->
      List.fold_left
	(fun (acc, found) aaf -> findproof_aaform ids aaf acc found)
	(acc,found) aafl
    | AFforall aaqf | AFexists aaqf ->
      let acc, found = 
	if List.mem aaqf.id ids then aaqf.ptag::acc, true 
	else acc, found in
      findproof_aaform ids aaqf.c.aqf_form acc found
    | AFlet (_,_,_, aaf) | AFnamed (_, aaf) ->
      findproof_aaform ids aaf acc found

and findproof_aaform ids aaf acc found =
  let acc, found = 
    if List.mem aaf.id ids then aaf.ptag::acc, true 
    else acc, found in
  findproof_aform ids aaf.c acc found

let findproof_atyped_decl ids td (ax,acc) =
  let acc = if List.mem td.id ids then td.ptag::acc else acc in
  match td.c with
    | ARewriting (_,_, arwtl) -> assert false

    | ALogic _ | ATypeDecl _ -> ax,acc

    | APredicate_def (_,_,_, af) 
    | AFunction_def (_,_,_,_, af) 
    | AAxiom (_, _, af) -> 
      let acc, found = findproof_aform ids af acc false in
      if found then td.ptag::ax, acc else ax,acc

    | AGoal (_,_, aaf) ->
      let acc, found = findproof_aaform ids aaf acc false in
      if found then td.ptag::ax, acc else ax,acc

let findtags_proof expl l =
  match Explanation.ids_of expl with
    | None -> [],[]
    | Some ids -> 
      List.fold_left (fun acc (td, _) ->
	findproof_atyped_decl ids td acc) ([],[]) l
