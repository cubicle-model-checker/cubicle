(**************************************************************************)
(*                                                                        *)
(*     The Alt-ergo theorem prover                                        *)
(*     Copyright (C) 2006-2010                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
(*     Alain Mebsout                                                      *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

open Why_ptree

let eq_var x t = 
  match t.c.tt_desc with
    | TTvar y -> Symbols.equal x y
    | _ -> false

let rec find_eq x eqs f = match f.c with
  | TFatom ({c=TAeq [t1;t2]}) -> 
      if eq_var x t1 then (x,t2)::eqs 
      else if eq_var x t2 then (x,t1)::eqs
      else eqs
  | TFop (OPand,l) -> List.fold_left (find_eq x) eqs l
  | _ -> eqs (* XXX: TODO *)

let find_equalities lv f = 
  List.fold_left 
    (fun eqs (x,_) -> 
       let l = find_eq x [] f in 
       if l = [] then raise Not_found; l::eqs ) [] lv

let rec apply_subst_term env t = 
  let tt = match t.c.tt_desc with
    | TTvar x as tt -> 
	(try (List.assoc x env).c.tt_desc with Not_found -> tt)
    | TTapp(s,l) -> TTapp(s,List.map (apply_subst_term env) l)
    | TTinfix(t1,s,t2) -> 
	TTinfix(apply_subst_term env t1,s,apply_subst_term env t2)
    | tt -> tt
  in
  { t with c = { t.c with tt_desc = tt }}

let rec apply_subst_formula env f = 
  let c = match f.c with
    | TFatom e -> 
	let a = match e.c with
	  | TAeq l -> TAeq (List.map (apply_subst_term env) l) 
	  | TAneq l -> TAneq (List.map (apply_subst_term env) l)
	  | TAdistinct l -> TAdistinct (List.map (apply_subst_term env) l)
	  | TAle l -> TAle (List.map (apply_subst_term env) l)
	  | TAlt l -> TAlt (List.map (apply_subst_term env) l)
	  | TAbuilt(s,l) -> TAbuilt(s,List.map (apply_subst_term env) l)
	  | TApred t -> TApred (apply_subst_term env t)
	  | TAfalse | TAtrue -> e.c 
	in TFatom {e with c = a}
    | TFop (op, lf) ->
	TFop (op, List.map (apply_subst_formula env) lf)
    | TFforall _ | TFexists _ -> f.c (* XXX: TODO *)
    | _ -> f.c 
  in
  { f with c = c }
	
let make_instance f = 
  let lt = find_equalities f.qf_bvars f.qf_form in
  apply_subst_formula (List.map List.hd lt) f.qf_form

let make f = 
  if Options.no_rm_eq_existential 
  then TFexists f
  else
    try (*TFop(OPor,[TFexists f;*)
      (make_instance f).c
    (*])*) 
    with Not_found -> TFexists f

