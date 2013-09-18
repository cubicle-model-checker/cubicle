open Ast
open Global
open Format
open Why3



(*---------------------------- Theories ---------------------------*)

let env,config =
  (* reads the Why3 config file *)
  let config : Whyconf.config = Whyconf.read_config None in
  (* the [main] section of the config file *)
  let main : Whyconf.main = Whyconf.get_main config in
  let env : Env.env = Env.create_env (Whyconf.loadpath main) in
  env,config


let find th s = Theory.ns_find_ls th.Theory.th_export [s]
let find_type th s = Theory.ns_find_ts th.Theory.th_export [s]



(* map.Map theory *)
let map_theory : Theory.theory = Env.find_theory env ["map"] "Map"
let map_ts : Ty.tysymbol = find_type map_theory "map"
(* let map_type (t:Ty.ty) : Ty.ty = Ty.ty_app map_ts [t] *)
let map_get : Term.lsymbol = find map_theory "get"


(* ref.Ref module *)

let ref_modules, ref_theories =
  Env.read_lib_file (Mlw_main.library_of_env env) ["ref"]

let ref_module : Mlw_module.modul = Stdlib.Mstr.find "Ref" ref_modules

let ref_type : Mlw_ty.T.itysymbol =
  Mlw_module.ns_find_its ref_module.Mlw_module.mod_export ["ref"]

let ref_fun : Mlw_expr.psymbol =
  Mlw_module.ns_find_ps ref_module.Mlw_module.mod_export ["ref"]

let get_logic_fun : Term.lsymbol =
  find ref_module.Mlw_module.mod_theory "prefix !"

let get_fun : Mlw_expr.psymbol =
  Mlw_module.ns_find_ps ref_module.Mlw_module.mod_export ["prefix !"]

let set_fun : Mlw_expr.psymbol =
  Mlw_module.ns_find_ps ref_module.Mlw_module.mod_export ["infix :="]


(*---------------- Formulas to why data structures ----------------*)

let hs_id s = Ident.id_fresh (Hstring.view s)

let ty_proc = 
  let tys = Ty.create_tysymbol (Ident.id_fresh "proc") [] (Some Ty.ty_int) in
  Ty.ty_app tys []

let type_why ty = 
  let tys = Ty.create_tysymbol (hs_id ty) [] None in
  Ty.ty_app tys []

let constr_symb_ty x ty = Term.create_fsymbol (hs_id x) [] ty

let constr_symb x =
  let _, hty = Smt.Symbol.type_of x in
  constr_symb_ty x (type_why hty)

let constr_why x = 
  let ty = type_why (snd (Smt.Symbol.type_of x)) in
  Term.fs_app (constr_symb_ty x ty) [] ty


(* TODO : Use ref instead *)
let f_to_why f =
  let hargs_ty, hret_ty = Smt.Symbol.type_of f in
  let args_ty, ret_ty = List.map type_why hargs_ty, type_why hret_ty in
  Term.create_fsymbol (hs_id f) args_ty ret_ty
		
let rec app_to_why f ls = 
  let tls = List.map (fun s -> app_to_why s []) ls in  
  Term.t_app_infer (f_to_why f) tls

let var_symb x =
  let _, hty = Smt.Symbol.type_of x in
  Term.create_vsymbol (hs_id x) (type_why hty)
  (* try Mlw_ty.restore_pv vs with Not_found -> vs *)

let var_to_why x = Term.t_var (var_symb x)
  
let var_pvsymbol x = 
  let _, hty = Smt.Symbol.type_of x in
  Mlw_ty.create_pvsymbol (hs_id x) (Mlw_ty.ity_of_ty (type_why hty))

let var_to_pv x =
  let pvs = var_pvsymbol x in
  Term.t_var pvs.Mlw_ty.pv_vs
  
let glob_to_ref x = Term.t_app_infer get_logic_fun [var_to_pv x]

let access_to_map a lx =
  match lx with
  | [x] -> 
     let va, vx = var_to_pv a, var_to_pv x in
     Term.t_app_infer map_get [va; vx]
  | _ -> failwith "access_to_map not implemented for matrices"

let term_to_why = function
  | Const _ -> failwith "term_to_why Const: Not implemented"
  | Elem (x, Var) -> var_to_why x
  | Elem (x, Constr) -> app_to_why x []
  | Elem (x, Glob) -> glob_to_ref x
  | Elem (_, Arr) -> assert false
  | Access (a, lx) -> access_to_map a lx
  | Arith _ -> failwith "term_to_why Arith: Not implemented"


let rec atom_to_why = function
  | Atom.True -> Term.t_true
  | Atom.False -> Term.t_false
  | Atom.Comp (x, Eq, y) -> Term.t_equ_simp (term_to_why x) (term_to_why y)
  | Atom.Comp (x, Neq, y) -> Term.t_neq_simp (term_to_why x) (term_to_why y)
  | Atom.Comp _ -> failwith "atom_to_why: Not implemented"
  | Atom.Ite (sa, a1, a2) ->
     Term.t_if_simp (cube_to_why sa) (atom_to_why a1) (atom_to_why a2)

and cube_to_why sa =
  if SAtom.is_empty sa then Term.t_false
  else SAtom.fold (fun a -> Term.t_and_simp (atom_to_why a)) sa Term.t_true


let cube_to_fol = cube_to_why


let system_to_why {t_unsafe = args, sa} =
  match args with
  | [] -> cube_to_why sa
  | _ ->
     let vsl = List.map var_symb args in
     Term.t_exists_close vsl [] (cube_to_why sa)

let systems_to_why =
  List.fold_left (fun acc s -> Term.t_or_simp (system_to_why s) acc)
		 Term.t_false



let ureq_to_fol (j, disj) =
  let tdisj = List.fold_left 
    (fun acc sa -> Term.t_or_simp (cube_to_why sa) acc) Term.t_false disj in
  Term.t_forall_close_simp [var_symb j] [] tdisj


(*--------------------------------------------------------------------*)



(*--------------- Why data structures to cubicle cubes ---------------*)

let why_var_to_hstring f = match f.Term.t_node with
  | Term.Tvar vs -> Hstring.make vs.Term.vs_name.Ident.id_string
  | _ -> assert false


let rec why_to_term ?(glob=false) f = match f.Term.t_node with
  | Term.Tvar vs ->
     Elem (Hstring.make vs.Term.vs_name.Ident.id_string,
	   if glob then Glob else Var)
  | Term.Tconst _ -> 
     failwith "why_to_term: Tconst to arith translation not implemented"
  | Term.Tapp (s, []) ->
     Elem (Hstring.make s.Term.ls_name.Ident.id_string, Constr)
  | Term.Tapp (s, [t]) when Term.ls_equal s get_logic_fun (* ref *) ->
     why_to_term ~glob:true t
  | Term.Tapp (s, a::li) when Term.ls_equal s map_get ->
     Access (Hstring.make s.Term.ls_name.Ident.id_string,
	     List.map why_var_to_hstring li)
  | _ -> assert false


let rec why_to_atom f = match f.Term.t_node with
  | Term.Ttrue -> Atom.True
  | Term.Tfalse -> Atom.False
  | Term.Tnot t -> Atom.neg (why_to_atom t)
  | Term.Tapp (s, [t1; t2]) when Term.ls_equal s Term.ps_equ ->
     Atom.Comp (why_to_term t1, Eq, why_to_term t2)
  | _ -> assert false

let rec why_to_cube f = match f.Term.t_node with
  | Term.Ttrue | Term.Tfalse | Term.Tnot _ | Term.Tapp _ ->
     SAtom.singleton (why_to_atom f)
  | Term.Tbinop (Term.Tand, f1, f2) ->
     SAtom.union (why_to_cube f1) (why_to_cube f2)
  | _ -> assert false


let why_to_system f = 
  let args, sa = match f.Term.t_node with
    | Term.Tquant (Term.Texists, tq) ->
       let vsl, _, t = Term.t_open_quant tq in     
       let args =
	 List.map (fun vs -> Hstring.make vs.Term.vs_name.Ident.id_string)
		  vsl in
       args, why_to_cube t
    | _ ->
       [], why_to_cube f
  in
  (* XXX: proper cube ? *)
  let arr_sa = ArrayAtom.of_satom sa in
  { !Global.global_system with 
    t_unsafe = args, sa;
    t_arru = arr_sa;
    t_alpha = ArrayAtom.alpha arr_sa args }


let rec why_to_systems f = match f.Term.t_node with
  | Term.Tbinop (Term.Tor, f1, f2) ->
     List.rev_append (why_to_systems f1) (why_to_systems f2)
  | _ -> [why_to_system f]

(*--------------------------------------------------------------------*)




(*---------------------------    DNF    ------------------------------*)

let rec push_neg p f = match f.Term.t_node with
  | Term.Tvar _ | Term.Tconst _ | Term.Tapp _ | Term.Ttrue | Term.Tfalse ->
      if p then f else Term.t_not_simp f
  | Term.Tnot f2 -> push_neg (not p) f2
  | Term.Tquant (q, tq) ->
     let vs, tr, t = Term.t_open_quant tq in
     let tq' = Term.t_close_quant vs tr (push_neg p t) in
     if p then Term.t_quant_simp q tq'
     else 
       let q' = match q with 
	 | Term.Tforall -> Term.Texists
	 | Term.Texists -> Term.Tforall in 
       Term.t_quant_simp q' tq'
  | Term.Teps tb ->
     let vs, t = Term.t_open_bound tb in
     Term.t_eps (Term.t_close_bound vs (push_neg p t))
  | Term.Tif (c, t1, t2) ->
     push_neg p (Term.t_and_simp 
		   (Term.t_or_simp (Term.t_not_simp c) t1)
		   (Term.t_or_simp c t2))
  | Term.Tbinop (Term.Timplies, t1, t2) ->
     push_neg p (Term.t_or_simp (Term.t_not_simp t1) t2)
  | Term.Tbinop (Term.Tiff, t1, t2) ->
     push_neg p (Term.t_and_simp 
		   (Term.t_or_simp (Term.t_not_simp t1) t2)
		   (Term.t_or_simp (Term.t_not_simp t2) t1))
  | Term.Tbinop (Term.Tand, t1, t2) ->
     if p then Term.t_and_simp (push_neg p t1) (push_neg p t2)
     else Term.t_or_simp (push_neg p t1) (push_neg p t2)
  | Term.Tbinop (Term.Tor, t1, t2) ->
     if p then Term.t_or_simp (push_neg p t1) (push_neg p t2)
     else Term.t_and_simp (push_neg p t1) (push_neg p t2)
  | Term.Tcase _ | Term.Tlet _ -> assert false

let dnf f =
  let cons x xs = x :: xs in
  let rec fold g f = match f.Term.t_node with
    | Term.Tbinop (Term.Tand, t1, t2) -> fold (fold g t1) t2
    | Term.Tbinop (Term.Tor, t1, t2) -> (fold g t1) @ (fold g t2)
    | _ -> List.map (cons f) g in
  fold [[]] (push_neg true f)

(* let already_conj = function *)
(*   | Lit _ -> true *)
(*   | And l -> List.for_all (function Lit _ -> true | _ -> false) l *)
(*   | _ -> false *)
		
(* let rec already_dnf f =  *)
(*   already_conj f || *)
(*     match f with *)
(*     | Or l -> List.for_all already_conj l *)
(*     | Exists (_, f) -> already_dnf f *)
(*     | _ -> false *)

let reconstruct_dnf f =
  let l = List.map (function 
		     | [] -> Term.t_false
		     | [f] -> f
		     | conj -> 
			List.fold_left (fun acc l -> Term.t_and_simp l acc)
				       Term.t_true conj
		   ) (dnf f) in
  match l with
  | [] -> Term.t_false
  | [f'] -> f'
  | _ -> List.fold_left (fun acc c -> Term.t_or_simp c acc)
			Term.t_false l
	       
let rec dnfize f = match f.Term.t_node with
  | Term.Tquant (q, tq) ->
     let vs, tr, t = Term.t_open_quant tq in
     let tq' = Term.t_close_quant vs tr (dnfize t) in
     Term.t_quant_simp q tq'
  | _ -> reconstruct_dnf f

let dnfize2 f =
  Prover.TimeF.start ();
  eprintf "indnf ... @.";
  let f = dnfize f in
  eprintf "outdnf ... @.";
  Prover.TimeF.pause ();
  f


(*--------------------------------------------------------------------*)


(*---------------- transitions to why data structures ----------------*)


let assign_to_post (a, t) =
  let aw = glob_to_ref a in
  let old_tw = Mlw_wp.t_at_old (term_to_why t) in
  Term.t_equ_simp aw old_tw (* , Mlw_ty.eff_empty *)


let switches_to_ite at swts =
  match List.rev swts with
  | (_, default) :: rswts ->
     let def = Mlw_wp.t_at_old (term_to_why default) in
     List.fold_left (fun acc (sa, t) ->
		     let cond = Mlw_wp.t_at_old (cube_to_why sa) in
		     let old_tw = Mlw_wp.t_at_old (term_to_why t) in
		     Term.t_if_simp cond (Term.t_equ_simp at old_tw) acc
		    )  (Term.t_equ_simp at def) rswts
  | _ -> assert false
		
		
let simple_update a j swts =
  match List.rev swts with
  | (_, default) :: rswts ->
     begin 
       try
	 let assigns = List.fold_left (fun acc (c, t) ->
		    match SAtom.elements c with
		    | [Atom.Comp (Elem(i, Var), Eq, Elem(k, Var))] ->
		      if Hstring.equal i j then (k, t) :: acc
		      else if Hstring.equal k j then (i, t) :: acc
		      else raise Exit
		    | _ -> raise Exit) [] rswts in
	 let utw = List.fold_left (fun acc (i, t) ->
			 let ai = access_to_map a [i] in
			 let old_tw = Mlw_wp.t_at_old (term_to_why t) in
			 Term.t_and_simp (Term.t_equ_simp ai old_tw) acc
			) Term.t_true assigns in
			 
	 Some utw
       with Exit -> None
     end    
  | _ -> assert false
  
  

let update_to_post { up_arr = a; up_arg = js; up_swts = swts } =
  match js with
  | [j] ->
     begin match simple_update a j swts with
     | Some utw -> utw
     | None ->
	let vj = var_symb j in
	let aj = access_to_map a js in
	let swtsw = switches_to_ite aj swts in
	Term.t_quant_simp Term.Tforall (Term.t_close_quant [vj] [] swtsw)
     end
  | _ -> failwith "update to post not implemented for matrices"
  


let transition_spec t =
  let c_req = cube_to_why t.tr_reqs in
  let req = List.fold_left 
	      (fun acc u -> Term.t_and_simp (ureq_to_fol u) acc)
	      c_req t.tr_ureq in
  let post = List.fold_left (fun post ass ->
			     Term.t_and_simp (assign_to_post ass) post)
			    Term.t_true t.tr_assigns in
  let post = List.fold_left (fun post upd ->
			     Term.t_and_simp (update_to_post upd) post)
			    post t.tr_upds in
  (* TODO : effects in updates and assigns -- see regions *)
  { Mlw_ty.c_pre = req;
           c_post = post;
	   c_xpost = Mlw_ty.Mexn.empty;
	   c_effect  = Mlw_ty.eff_empty;
	   c_variant = [];
	   c_letrec  = 0;
  }


let transition_to_lambda t =
  {
    Mlw_expr.l_args = List.map var_pvsymbol t.tr_args;
	     l_expr = Mlw_expr.e_void;
	     l_spec = transition_spec t;
  }




(*--------------------------------------------------------------------*)

