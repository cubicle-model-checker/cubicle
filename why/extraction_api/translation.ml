open Ast
open Global
open Format
open Why3


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

let var_to_why x = Term.t_var (var_symb x)
  
let var_to_pv x = 


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


(*--------------------------------------------------------------------*)



(*---------------- transitions to why data structures ----------------*)

let transition_spec

let transition_to_lambda = assert false




(*--------------------------------------------------------------------*)

