open Ast
open Global
open Format
open Why3



(*---------------------------- Theories ---------------------------*)

let env,config =
  try
    (* reads the Why3 config file *)
    let config : Whyconf.config = Whyconf.read_config None in
    (* the [main] section of the config file *)
    let main : Whyconf.main = Whyconf.get_main config in
    let env : Env.env = Env.create_env (Whyconf.loadpath main) in
    env,config
  with e ->
    Self.fatal "Exception raised in Why3 env:@ %a" Exn_printer.exn_printer e

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
  

let term_to_why = function
  | Const _ -> failwith "term_to_why Const: Not implemented"
  | Elem (x, Var) -> var_to_why x
  | Elem (x, _) -> app_to_why x []
  | Access (a, lx) -> app_to_why a lx
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

let ureq_to_fol (j, disj) =
  let tdisj = List.fold_left 
    (fun acc sa -> Term.t_or_simp (cube_to_why sa) acc) Term.t_false disj in
  Term.t_forall_close_simp [var_symb j] [] tdisj


(*--------------------------------------------------------------------*)



(*---------------- transitions to why data structures ----------------*)

let transition_spec t =
  let pv_args = List.map var_pvsymbol t.tr_args in
  let c_req = cube_to_why t.tr_req in
  let req = List.fold_left 
	      (fun acc u -> Term.t_and_simp (ureq_to_fol u) acc)
	      c_req t.tr_ureq in
  (* TODO : post + effects -- see regions *)
  { c_pre     = req;
    c_post    = post;
    c_xpost   = Mlw_ty.Mexn.empty;
    c_effect  = Mlw_ty.eff_empty;
    c_variant = [];
    c_letrec  = 0;
  }

let transition_to_lambda = assert false




(*--------------------------------------------------------------------*)
