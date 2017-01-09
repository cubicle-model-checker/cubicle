(*-----------------  Begin manually edited ------------------*)

open Ast
open Global
open Format

module P = Pretty

open Why3


(*     TODO:    Use Decl.known_map DONE *)

(*---------------------------- Theories ---------------------------*)

let env, config =
  (* reads the Why3 config file *)
  let config : Whyconf.config = Whyconf.read_config None in
  (* the [main] section of the config file *)
  let main : Whyconf.main = Whyconf.get_main config in
  let env : Env.env = Env.create_env (Whyconf.loadpath main) in
  env, config


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

let ref_ts = ref_type.Mlw_ty.T.its_ts

let ref_fun : Mlw_expr.psymbol =
  Mlw_module.ns_find_ps ref_module.Mlw_module.mod_export ["ref"]

let get_logic_fun : Term.lsymbol =
  find ref_module.Mlw_module.mod_theory "prefix !"

let get_fun : Mlw_expr.psymbol =
  Mlw_module.ns_find_ps ref_module.Mlw_module.mod_export ["prefix !"]

let set_fun : Mlw_expr.psymbol =
  Mlw_module.ns_find_ps ref_module.Mlw_module.mod_export ["infix :="]


(* int.Int theory *)
let int_type : Ty.ty = Ty.ty_int
let int_theory : Theory.theory = Env.find_theory env ["int"] "Int"
let add_int : Term.lsymbol = find int_theory "infix +"
let sub_int : Term.lsymbol = find int_theory "infix -"
let minus_int : Term.lsymbol = find int_theory "prefix -"
let mul_int : Term.lsymbol = find int_theory "infix *"
let ge_int : Term.lsymbol = find int_theory "infix >="
let le_int : Term.lsymbol = find int_theory "infix <="
let gt_int : Term.lsymbol = find int_theory "infix >"
let lt_int : Term.lsymbol = find int_theory "infix <"


let th_known = Decl.merge_known 
		 Mlw_wp.th_mark_at.Theory.th_known
		 Mlw_wp.th_mark_old.Theory.th_known


(*---------------- Formulas to why data structures ----------------*)

let user_idents = Hstring.H.create 19

let hs_id s =
  try Hstring.H.find user_idents s
  with Not_found ->
       let id = Ident.id_fresh (Hstring.view s) in
       Hstring.H.add user_idents s id;
       id


let h_proc = Hstring.make "proc"
let h_bool = Hstring.make "bool"
let h_int = Hstring.make "int"

let user_cubtypes = Hstring.H.create 13

let ty_proc = 
  let tys = Ty.create_tysymbol (Ident.id_fresh "proc") [] (Some Ty.ty_int) in
  Hstring.H.add user_cubtypes h_proc tys;
  let ts = Ty.ty_app tys [] in
  ts

let hs_to_tys ty =
  try Hstring.H.find user_cubtypes ty
  with Not_found ->
       let ts = Ty.create_tysymbol (hs_id ty) [] None in
       Hstring.H.add user_cubtypes ty ts;
       ts

let tysymb = hs_to_tys

let type_var ty = ty_proc

let type_constr ty = Ty.ty_app (tysymb ty) []

let type_glob ty =
  let tyap = Ty.ty_app (tysymb ty) [] in
  Ty.ty_app ref_ts [tyap]

let type_array ty =
  let tyap = Ty.ty_app (tysymb ty) [] in
  Ty.ty_app ref_ts [Ty.ty_app map_ts [ty_proc; tyap]]



(*--------------------------------------------------------------------*)


let user_symbols = Hstring.H.create 13

let constr_symb_ty x ty =
  try Hstring.H.find user_symbols x
  with Not_found ->
       let s = Term.create_fsymbol (hs_id x) [] ty in
       Hstring.H.add user_symbols x s;
       s

let constr_symb x =
  let _, hty = Smt.Symbol.type_of x in
  constr_symb_ty x (type_constr hty)

let constr_to_why x = 
  let ty = type_constr (snd (Smt.Symbol.type_of x)) in
  Term.fs_app (constr_symb_ty x ty) [] ty


(* let f_to_why f = *)
(*   let hargs_ty, hret_ty = Smt.Symbol.type_of f in *)
(*   let args_ty, ret_ty = List.map type_array hargs_ty, type_arr hret_ty in *)
(*   Term.create_fsymbol (hs_id f) args_ty ret_ty *)
		
(* let rec app_to_why f ls =  *)
(*   let tls = List.map (fun s -> app_to_why s []) ls in   *)
(*   Term.t_app_infer (f_to_why f) tls *)

let user_vsymbols = Hstring.H.create 13

let var_symb x =
  try Hstring.H.find user_vsymbols x
  with Not_found ->
    let _, hty = Smt.Symbol.type_of x in
    let s = Term.create_vsymbol (hs_id x) (type_glob hty) in
    Hstring.H.add user_vsymbols x s;
    s
      


let var_symb_proc x =
  try Hstring.H.find user_vsymbols x
  with Not_found ->
       let s = Term.create_vsymbol (hs_id x) ty_proc in
       Hstring.H.add user_vsymbols x s;
       s
		 

let var_to_why x = Term.t_var (var_symb x)
  
let user_pvsymbols = Hstring.H.create 13

let create_pvs x ty = 
  try Hstring.H.find user_pvsymbols x
  with Not_found ->
    try Mlw_ty.restore_pv (Hstring.H.find user_vsymbols x)
    with Not_found ->
      let ps = Mlw_ty.create_pvsymbol (hs_id x) (Mlw_ty.ity_of_ty ty) in
      Hstring.H.add user_pvsymbols x ps;
      ps
       

let var_pvsymbol x =
    let hty = try snd (Smt.Symbol.type_of x) with Not_found -> h_proc in
    create_pvs x (type_var hty)    

let var_to_pv x =
  let pvs = var_pvsymbol x in
  Term.t_var pvs.Mlw_ty.pv_vs


let proc_pvsymbol x = create_pvs x ty_proc

let proc_vsymbol x = (proc_pvsymbol x).Mlw_ty.pv_vs

let proc_to_pv x =
  let pvs = proc_pvsymbol x in
  Term.t_var pvs.Mlw_ty.pv_vs

let glob_pvsymbol x = 
  let _, hty = Smt.Symbol.type_of x in
  create_pvs x (type_glob hty)

let glob_to_pv x =
  let pvs = glob_pvsymbol x in
  Term.t_var pvs.Mlw_ty.pv_vs

let arr_pvsymbol x = 
  let _, hty = Smt.Symbol.type_of x in
  create_pvs x (type_array hty)

let arr_to_pv x =
  let pvs = arr_pvsymbol x in
  Term.t_var pvs.Mlw_ty.pv_vs
  
  
let glob_to_ref x = Term.t_app_infer get_logic_fun [glob_to_pv x]

let rec cross acc = function
    | [] -> acc
    | x :: r -> cross (List.fold_left (fun acc y -> (x, y)::acc) acc r) r

let distinct_why procs =
  List.fold_left 
    (fun acc (v1, v2) ->
     Term.t_and_simp acc 
		     (Term.t_neq_simp
			(proc_to_pv v1) (proc_to_pv v2))
    ) Term.t_true (cross [] procs)

let distinct_from_why x others =
  let vx = proc_to_pv x in
  List.fold_left 
    (fun acc y -> Term.t_and_simp acc (Term.t_neq_simp vx (proc_to_pv y)))
    Term.t_true others


(* let procs_of_why f = *)
(*   match f.Term.t_node with *)
(*   | Term.Tquant (Term.Texists, tq) -> *)
(*      let vsl, _, _ = Term.t_open_quant tq in      *)
(*      List.map (fun vs -> Hstring.make vs.Term.vs_name.Ident.id_string) vsl *)
(*   | _ -> [] *)

let procs_of_why f =
  Term.Mvs.fold (fun vs _ acc ->
    let n = vs.Term.vs_name.Ident.id_string in
    if n.[0] = '#' then (proc_pvsymbol (Hstring.make n)) :: acc
    else acc
  ) (Term.t_vars f) []
  

let access_to_map a lx =
  match lx with
  | [x] -> 
     let va, vx = arr_to_pv a, proc_to_pv x in
     let geta = Term.t_app_infer get_logic_fun [va] in
     Term.t_app_infer map_get [geta; vx] 
  | _ -> failwith "access_to_map not implemented for matrices"

let term_to_why = function
  | Const _ -> failwith "term_to_why Const: Not implemented"
  | Elem (x, Var) -> proc_to_pv x (* var_to_why x *)
  | Elem (x, Constr) -> constr_to_why x
  | Elem (x, Glob) -> glob_to_ref x
  | Elem (_, Arr) -> assert false
  | Access (a, lx) -> access_to_map a lx
  | Arith _ -> failwith "term_to_why Arith: Not implemented"

let rec atom_to_why = function
  | Atom.True -> Term.t_true
  | Atom.False -> Term.t_false
  | Atom.Comp (x, Eq, y) ->
     let tx, ty = term_to_why x, term_to_why y in
     Term.t_equ_simp tx ty
  | Atom.Comp (x, Neq, y) ->
     Term.t_neq_simp (term_to_why x) (term_to_why y)
  | Atom.Comp (x, Le, y) ->
     Term.t_app_infer le_int [term_to_why x; term_to_why y]
  | Atom.Comp (x, Lt, y) ->
     Term.t_app_infer lt_int [term_to_why x; term_to_why y]
  | Atom.Ite (sa, a1, a2) ->
     Term.t_if_simp (cube_to_why sa) (atom_to_why a1) (atom_to_why a2)

and cube_to_why sa =
try
  if SAtom.is_empty sa then Term.t_false
  else 
    let f =
      SAtom.fold (fun a -> Term.t_and_simp (atom_to_why a)) sa Term.t_true in
    let procs = Ast.procs_of_cube sa in
    Term.t_and_simp (distinct_why procs) f
with e -> eprintf "%a@." Exn_printer.exn_printer e; assert false


(* let cube_to_why sa =  *)
(*   let f = cube_to_why sa in *)
(*   eprintf "%a ----> %a@." P.print_cube sa Pretty.print_term f; *)
(*   f *)

let cube_to_fol = cube_to_why


let system_to_why {t_unsafe = args, sa} =
  match args with
  | [] -> cube_to_why sa
  | _ ->
     (* let vsl = List.map var_symb_proc args in *)
     let vsl = List.map (fun vs -> (proc_pvsymbol vs).Mlw_ty.pv_vs) args in
     (* Term.Mvs.iter (fun vs i -> *)
     (* 		    eprintf "> %a:%d@." Pretty.print_vs vs i; *)
     (* 	       ) (Term.t_freevars Term.Mvs.empty (cube_to_why sa)); *)
     Term.t_exists_close(* _simp *) vsl [] (cube_to_why sa)

let systems_to_why =
  List.fold_left (fun acc s -> Term.t_or_simp (system_to_why s) acc)
		 Term.t_false



let ureq_to_fol (j, disj) others =
  let tdisj = List.fold_left 
    (fun acc sa -> Term.t_or_simp (cube_to_why sa) acc) Term.t_false disj in
  let tdisj = Term.t_and_simp (distinct_from_why j others) tdisj in
  Term.t_forall_close_simp [(proc_pvsymbol j).Mlw_ty.pv_vs] [] tdisj


(*------------------------ Declarations ----------------------------*)


let type_decls = Hstring.H.create 13

let find_type t =
  eprintf "find type %a@." Hstring.print t;
  if Hstring.equal t h_proc then Mlw_ty.ity_of_ty ty_proc
  else if Hstring.equal t h_bool then Mlw_ty.ity_bool
  else if Hstring.equal t h_int then Mlw_ty.ity_int
  else Hstring.H.find type_decls t
    (* (\* TODO pas mettre id_register *\) *)
    (* match (Ident.Mid.find (Ident.id_register (hs_id t)) kn).Mlw_decl.pd_node with *)
    (* | Mlw_decl.PDtype tys | Mlw_decl.PDdata [tys, _, _] -> *)
    (* 			     Mlw_ty.ity_app_fresh tys [] *)
    (* | _ -> assert false *)


let add_type_decls s sm =
  let sm = 
    let tys = Mlw_ty.create_itysymbol
		(Ident.id_fresh "proc") [] [] (Some Mlw_ty.ity_int) in
    Mlw_module.add_pdecl ~wp:false sm (Mlw_decl.create_ty_decl tys) in
  List.fold_left (fun sm (n, c) ->
	          let tys = Mlw_ty.create_itysymbol (hs_id n) [] [] None in
	          let d = match c with
		    | [] -> Mlw_decl.create_ty_decl tys
		    | _ -> 
		       let constrs = 
                         List.map (fun s ->
                                   (* ignore (constr_to_why s); *)
                                   hs_id s, []) c in
		       Mlw_decl.create_data_decl [tys, constrs] in
	          Hstring.H.add type_decls n (Mlw_ty.ity_app_fresh tys []);
                  eprintf "!>> %a\n@." Mlw_pretty.print_pdecl d;
	          Mlw_module.add_pdecl ~wp:false sm d
	         ) sm s.type_defs

let user_regions = Hstring.H.create 21

let add_glob_decls s sm =
   List.fold_left (fun sm (n, t) ->
              ignore (glob_to_ref n);
	      let pid = hs_id n in
	      let ret_ity = find_type t in
	      let rity = Mlw_ty.ity_app_fresh ref_type [ret_ity] in
	      let ps = create_pvs n (Mlw_ty.ty_of_ity rity) in
	      let d = Mlw_decl.create_val_decl (Mlw_expr.LetV ps) in
	      let reg = Mlw_ty.create_region pid rity in
	      Hstring.H.add user_regions n reg;
              eprintf "!>> %a\n@." Mlw_pretty.print_pdecl d;
	      Mlw_module.add_pdecl ~wp:false sm d
	     ) sm s.globals

let add_array_decls s sm =
    List.fold_left (fun sm (n, (args, ret)) ->
	      let ret_ity = find_type ret in
	      let args_ity = List.map find_type args in
	      match args_ity with
	      | [arg_ity] ->
                 ignore (arr_to_pv n);
		 let pid = hs_id n in
		 let map_ty = Mlw_ty.ity_pur map_ts [arg_ity; ret_ity] in
		 let aty = Mlw_ty.ity_app_fresh ref_type [map_ty] in
		 let ps = create_pvs n (Mlw_ty.ty_of_ity aty) in
		 let d = Mlw_decl.create_val_decl (Mlw_expr.LetV ps) in
		 let reg = Mlw_ty.create_region pid aty in
		 Hstring.H.add user_regions n reg;
                 eprintf "!>> %a\n@." Mlw_pretty.print_pdecl d;
		 Mlw_module.add_pdecl ~wp:false sm d
	      | _ -> assert false
	    ) sm s.arrays


(*------------------------------------------------------------------*)



(*--------------- Why data structures to cubicle cubes ---------------*)

let why_var_to_hstring f = match f.Term.t_node with
  | Term.Tvar vs -> 
     let s = vs.Term.vs_name.Ident.id_string in
     let s = 
       try Scanf.sscanf s "sh%d" (fun x -> "#"^(string_of_int x))
       with _ -> s
     in
     Hstring.make s
  | _ -> assert false


let rec why_to_term ?(glob=false) f =
 match f.Term.t_node with
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
     (match a.Term.t_node with
      | Term.Tapp (s, [ra]) when Term.ls_equal s get_logic_fun (* ref *) ->
	 (match ra.Term.t_node with
	  | Term.Tvar avs ->
	     Access (Hstring.make avs.Term.vs_name.Ident.id_string,
		     List.map why_var_to_hstring li)
	  | _ -> assert false)
      | _ -> assert false)
  | _ -> assert false


let rec why_to_atom f = match f.Term.t_node with
  | Term.Ttrue -> Atom.True
  | Term.Tfalse -> Atom.False
  | Term.Tnot t -> Atom.neg (why_to_atom t)
  | Term.Tapp (s, [t1; t2]) when Term.ls_equal s Term.ps_equ ->
     Atom.Comp (why_to_term t1, Eq, why_to_term t2)
  | Term.Tapp (s, [t1; t2]) when Term.ls_equal s le_int ->
     Atom.Comp (why_to_term t1, Le, why_to_term t2)
  | Term.Tapp (s, [t1; t2]) when Term.ls_equal s lt_int ->
     Atom.Comp (why_to_term t1, Lt, why_to_term t2)
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
  | Term.Tcase (c, [br]) ->
     let pat, t = Term.t_open_branch br in
     Term.t_case_close_simp c [pat, (push_neg p t)]
  | Term.Tcase _ -> assert false
  | Term.Tlet (x, tb) ->
     Term.t_let_simp (push_neg p x) tb

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

let reconstruct_conj f =
  List.map (function 
	     | [] -> Term.t_false
	     | [f] -> f
	     | conj -> 
		List.fold_left (fun acc l -> Term.t_and_simp l acc)
			       Term.t_true conj
	   ) (dnf f)

let reconstruct_dnf f =
  match reconstruct_conj f with
  | [] -> Term.t_false
  | [f'] -> f'
  | l -> List.fold_left (fun acc c -> Term.t_or_simp c acc)
			Term.t_false l
	       
let rec dnfize f = match f.Term.t_node with
  | Term.Tquant (q, tq) ->
     let vs, tr, t = Term.t_open_quant tq in
     let tq' = Term.t_close_quant vs tr (dnfize t) in
     Term.t_quant_simp q tq'
  | _ -> reconstruct_dnf f
	       
let rec dnfize_list f = match f.Term.t_node with
  | Term.Tquant (q, tq) ->
     let vs, tr, t = Term.t_open_quant tq in
     let tq' = Term.t_close_quant vs tr (dnfize t) in
     [Term.t_quant_simp q tq']
  | _ -> reconstruct_conj f

let dnfize_list2 f =
  Prover.TimeF.start ();
  (* eprintf "indnf ... @."; *)
  let f = dnfize_list f in
  (* eprintf "outdnf ... @."; *)
  Prover.TimeF.pause ();
  f


let rec dnf_to_conj_list acc f = match f.Term.t_node with
  | Term.Tbinop (Term.Tor, f1, f2) ->
     dnf_to_conj_list (dnf_to_conj_list acc f1) f2
  | _ -> f :: acc

let dnf_to_conj_list = dnf_to_conj_list []

(*--------------------------------------------------------------------*)


let rec simplify f = match f.Term.t_node with
  | Term.Tvar _ | Term.Tconst _ | Term.Tapp _ | Term.Ttrue | Term.Tfalse -> f
  | Term.Tnot f2 -> Term.t_not_simp (simplify f2)
  | Term.Tquant (q, tq) ->
     let vs, tr, t = Term.t_open_quant tq in
     let tq' = Term.t_close_quant vs tr (simplify t) in
     Term.t_quant_simp q tq'
  | Term.Teps tb ->
     let v, t = Term.t_open_bound tb in
     Term.t_eps_close v (simplify t)
  | Term.Tif (c, t1, t2) ->
     Term.t_if_simp c (simplify t1) (simplify t2)
  | Term.Tbinop (op, t1, t2) ->
     Term.t_binary_simp op (simplify t1) (simplify t2)
  | Term.Tlet (x, tb) ->
     let v, t = Term.t_open_bound tb in
     Term.t_let_close_simp v (simplify x) (simplify t)
  | Term.Tcase (c, [br]) ->
     let pat, t = Term.t_open_branch br in
     begin 
       match pat.Term.pat_node with 
       | Term.Papp (ls, _) when ls.Term.ls_name.Ident.id_string = "mk ref" ->
          eprintf "simpl CASE %a == %a@." Pretty.print_term f Pretty.print_term t;
          t
       | _ -> f   
     end
  | _ -> f

(*---------------- transitions to why data structures ----------------*)

(* TODO Create val with specification instead of unit functions *)

let t_old t =
  (* Term.t_app_infer Mlw_wp.fs_old [t]*)
  Mlw_wp.t_at_old t
                   
  
let assign_to_post globals (a, t) =
  let aw = glob_to_ref a in
  let reg_a = Hstring.H.find user_regions a in
  let eff =  Mlw_ty.eff_write Mlw_ty.eff_empty reg_a in
  let old_tw = t_old (term_to_why t) in
  Term.t_equ_simp aw old_tw , eff, Hstring.HSet.remove a globals

(* let assign_to_expr (a, t) = *)
(*   let va = glob_to_pv a in *)
(*   let ity_va = va.Mlw_ty.pv_ity in *)
(*   let ret_ty = match ity_va.Mlw_ty.ity_node with *)
(*     | Mlw_ty.Ityapp (_, [r], _) -> r *)
(*     | _ -> assert false in *)
(*   let bang = Mlw_expr.e_arrow get_fun [ity_va] ret_ty in *)
(*   let coleq = Mlw_expr.e_arrow get_fun [ity_va; ret_ty] Mlw_ty.ity_unit in *)
(*   Mlw_expr.e_app coleq [Mlw_expr.e_value va; ] *)

(*   let reg_a = Hstring.H.find user_regions a in *)
(*   let eff =  Mlw_ty.eff_write Mlw_ty.eff_empty reg_a in *)
(*   let old_tw = t_old (term_to_why t) in *)
  

let unchanged_globals globals =
  Hstring.HSet.fold 
    (fun a acc ->
     let aw = glob_to_ref a in
     Term.t_and_simp acc (Term.t_equ_simp aw (t_old aw))
    ) globals Term.t_true

let switches_to_ite at swts =
  match List.rev swts with
  | (_, default) :: rswts ->
     let def = t_old (term_to_why default) in
     List.fold_left (fun acc (sa, t) ->
		     let cond = t_old (cube_to_why sa) in
		     let old_tw = t_old (term_to_why t) in
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
			 let old_tw = t_old (term_to_why t) in
			 Term.t_and_simp (Term.t_equ_simp ai old_tw) acc
			) Term.t_true assigns in
			 
	 Some utw
       with Exit -> None
     end    
  | _ -> assert false
  
  

let update_to_post arrays { up_arr = a; up_arg = js; up_swts = swts } =
  let reg_a = Hstring.H.find user_regions a in
  let eff =  Mlw_ty.eff_write Mlw_ty.eff_empty reg_a in
  let arrays = Hstring.HSet.remove a arrays in
  match js with
  | [j] ->
     begin match simple_update a j swts with
     | Some utw -> utw, eff, arrays
     | None ->
	let vj = var_symb j in
	let aj = access_to_map a js in
	let swtsw = switches_to_ite aj swts in
	Term.t_forall_close_simp [vj] [] swtsw, eff, arrays
     end
  | _ -> failwith "update to post not implemented for matrices"


let unchanged_arrays arrays =
  Hstring.HSet.fold
    (fun a acc ->
     let j = Hstring.make "j" in
     let vj = proc_vsymbol
 j in
     let aj = access_to_map a [j] in
     let unch = Term.t_equ_simp aj (t_old aj) in
     Term.t_and_simp acc (Term.t_forall_close_simp [vj] [] unch)
    ) arrays Term.t_true


let dummy_vsymbol =
  Term.create_vsymbol (Ident.id_fresh "@dummy@") Mlw_ty.ty_unit

let transition_spec t =
  let globals = 
    List.fold_left 
      (fun acc (g, _) -> Hstring.HSet.add g acc)
      Hstring.HSet.empty !Global.info.globals in
  let arrays = 
    List.fold_left 
      (fun acc (a, _) -> Hstring.HSet.add a acc)
      Hstring.HSet.empty !Global.info.arrays in
  
  let c_req = cube_to_why t.tr_reqs in
  
  let req = List.fold_left 
	      (fun acc u -> Term.t_and_simp acc (ureq_to_fol u t.tr_args))
	      c_req t.tr_ureq in
  let post, eff, globals = 
    List.fold_left (fun (post, eff, globals) ass ->
		    let ta, eff_ass, globals = assign_to_post globals ass in
		    Term.t_and_simp ta post,
		    Mlw_ty.eff_union eff eff_ass, globals)
		   (Term.t_true, Mlw_ty.eff_empty, globals) t.tr_assigns in
  let post, eff, arrays = 
    List.fold_left (fun (post, eff, arrays) upd ->
		    let ta, eff_upd, arrays = update_to_post arrays upd in
		    Term.t_and_simp ta post,
		    Mlw_ty.eff_union eff eff_upd, arrays)
		   (post, eff, arrays) t.tr_upds in
  (* let post = Term.t_and_simp_l *)
  (*              [post; unchanged_globals globals; unchanged_arrays arrays ] in *)
  let post = Mlw_ty.create_post dummy_vsymbol post in
  (* TODO : effects in updates and assigns -- see regions *)
  { Mlw_ty.c_pre = req;
           c_post = post;
	   c_xpost = Mlw_ty.Mexn.empty;
	   c_effect  = eff;
	   c_variant = [];
	   c_letrec  = 0;
  }


let transition_to_lambda t =
  {
    Mlw_expr.l_args = List.map var_pvsymbol t.tr_args;
	     l_expr = Mlw_expr.e_void;
	     l_spec = transition_spec t;
  }


let trans_symbols = Hstring.H.create 21

let add_transition_fun_decl sm t =
  let p_name = hs_id t.tr_name in
  let lamb = transition_to_lambda t in
  let f = Mlw_expr.create_fun_defn p_name lamb in
  Hstring.H.add trans_symbols t.tr_name f.Mlw_expr.fun_ps;
  let d = Mlw_decl.create_rec_decl [f] in
  (* let d = Mlw_decl.create_val_decl (Mlw_expr.LetA f.Mlw_expr.fun_ps) in *)
  eprintf "!>> %a\n@." Mlw_pretty.print_pdecl d;
  try
    Mlw_module.add_pdecl ~wp:false sm d
  with Decl.UnknownIdent (i) ->
    eprintf "uknowkwd : %s@." i.Ident.id_string;
    assert false
  (* sm *)


let add_transitions_decls s kn =
  List.fold_left add_transition_fun_decl kn s.trans

let transition_to_fun t =
  eprintf "find %a@." Hstring.print t.tr_name;
  let pst = Hstring.H.find trans_symbols t.tr_name in
  Mlw_expr.e_arrow pst
		   (List.map (fun _ -> Mlw_ty.ity_of_ty ty_proc) t.tr_args)
		   Mlw_ty.ity_unit


let instantiate_trans t args =
  let e_args = List.map Mlw_expr.e_value args in
  let ft = transition_to_fun t in
  Mlw_expr.e_app ft e_args
  

(*--------------------------------------------------------------------*)

let sys_module_uc =
  let cub_module_uc =
    Mlw_module.create_module env (Ident.id_fresh "cub_module") in
  let cub_module_uc = Mlw_module.use_export cub_module_uc ref_module in
  let cub_module_uc = Mlw_module.use_export_theory cub_module_uc map_theory in
  let cub_module_uc = 
    Mlw_module.use_export_theory cub_module_uc Mlw_wp.th_mark_at in
  let cub_module_uc = 
    Mlw_module.use_export_theory cub_module_uc Mlw_wp.th_mark_old in
  cub_module_uc

(* let known_map = ref Ident.Mid.empty *)

let module_declarations s =
  sys_module_uc |> add_type_decls s
                |> add_glob_decls s
                |> add_array_decls s
                |> add_transitions_decls s

let sys_module =
  (* Dummy module *)
  ref (* (Mlw_module.close_module *)
         (Mlw_module.create_module env (Ident.id_fresh "@dummy_module@"))
                                     
let set_decl_module s =
  sys_module := (* Mlw_module.close_module *) (module_declarations s)

(*--------------------------------------------------------------------*)



module HSet = Hstring.HSet


let skolemize f =
  (* eprintf "skolemize: %a@." Pretty.print_term f; *)
  let csts = ref [] in
  let h_csts = ref [] in
  let rec simpl = 
    fun f -> match f.Term.t_node with
	     | Term.Tquant (Term.Texists, tq) ->
		let vsl, _, t = Term.t_open_quant tq in
	        (* assert *)
		(*   (List.for_all  *)
		(*      (fun vs -> *)
		(*       eprintf "%s : %a@." (vs.Term.vs_name.Ident.id_string) *)
		(* 	      Pretty.print_ty vs.Term.vs_ty; *)
		(*       Ty.ty_equal vs.Term.vs_ty ty_proc) vsl); *)
		let subst, _ = List.fold_left (fun (acc, vh) v -> 
		    match vh with
		    | h :: rh -> let th = proc_to_pv h in
				 csts := th :: !csts; 
				 h_csts := h :: !h_csts; 
				 Term.Mvs.add v th acc, rh
		    | _ -> assert false) (Term.Mvs.empty, proc_vars) vsl in
		(* Term.Mvs.iter (fun vs t -> *)
		(* 	       eprintf "%a -> %a:%a@." Pretty.print_vs vs Pretty.print_term t *)
		(* 		       Pretty.print_ty (Term.t_type t) *)
		(* 	      ) subst; *)
		(* eprintf "in subst %a @." Pretty.print_term t; *)
		simpl (Term.t_subst subst t)
	     | _ -> Term.t_map_simp simpl f
  in
  let f = simpl f in
  (* let f = Term.t_map_simp simpl f in *)
  f, !csts, !h_csts


let perm_to_subst =
  List.fold_left (fun acc (a,b) -> Term.Mvs.add a b acc) Term.Mvs.empty

let rec instanciate_proc csts f =
  let simpl =
    fun f -> match f.Term.t_node with
	     | Term.Tquant (Term.Tforall, tq) ->
		let vsl, _, t = Term.t_open_quant tq in
		List.fold_left (fun instances d ->
		(* 		eprintf "inst:"; *)
		(* Term.Mvs.iter (fun vs t -> *)
		(* 	       eprintf "%a -> %a:%a@." Pretty.print_vs vs Pretty.print_term t *)
		(* 		       Pretty.print_ty (Term.t_type t) *)
		(* 	      ) (perm_to_subst d); *)
				
		  let ni = Term.t_subst (perm_to_subst d) t in
		  Term.t_and_simp (instanciate_proc csts ni) instances
		) Term.t_true (all_permutations vsl csts)
	     | _ -> f
  in
  Term.t_map_simp simpl f


let skolem_instanciate f =
  List.map (fun f ->
	    let f, csts, h_csts = skolemize f in
            let csts, h_csts =
              (* create at least one instance *)
              if csts = [] then let h = (Hstring.make "#1") in 
                                [proc_to_pv h], [h]
              else csts, h_csts in
	    let f = instanciate_proc csts f in
	    f, h_csts
	   ) (dnfize_list f)


(* XXX : change this *)
let why_to_smt f = Prover.make_formula_set (why_to_cube f)
  (* let ss = why_to_systems f in *)
  (* List.map (fun {t_arru = ap} ->  *)
  (* eprintf "CUB SAFETY: %a@." P.print_array ap; *)
  (* Prover.make_formula ap) ss *)



let distinct vars = 
  Smt.Formula.make_lit Smt.Formula.Neq 
		       (List.map (fun v -> Smt.Term.make_app v []) vars)

let safety_formulas f =
  List.map (fun (f, h_csts) ->
    distinct h_csts,
    let sf  = why_to_smt f in
    sf
  ) (skolem_instanciate f)

  



let init_to_fol {t_init = args, lsa} = match lsa with
  | [] -> Term.t_false
  | _ ->
     (* let vsl = List.map var_symb_proc args in *)
     let vsl = List.map (fun vs -> (proc_pvsymbol vs).Mlw_ty.pv_vs) args in
     (* List.iter (fun vs -> eprintf "## %a@." Pretty.print_vs vs) vsl; *)
     let t = List.fold_left (fun acc sa -> Term.t_or_simp (cube_to_why sa) acc)
			    Term.t_false lsa in
     Term.t_forall_close_simp vsl [] t




(*------------------  End manually edited -------------------*)
