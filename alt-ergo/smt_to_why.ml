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

open Smt_ast
open Why_ptree
open Lexing

let dpos = {pos_fname="";pos_lnum=0;pos_bol=0;pos_cnum=0}
let dloc = dpos, dpos

exception Not_Implemented

let sort_to_type pos = function
  | "Int" -> PPTint
  | "Real" -> PPTreal
  | "Array" -> PPTexternal([PPTint;PPTint],"Array_poly",pos)
  | "Array1" -> PPTexternal([PPTint;PPTreal],"Array_poly",pos)
  | "Array2" -> 
      PPTexternal([PPTint;PPTexternal([PPTint;PPTreal],"Array_poly",pos)],
		  "Array_poly",pos)
  | s -> PPTexternal ([], s, pos)
  
let curry_sort_to_type (pos,sort) =
  sort_to_type pos sort

let pexp pos f = {pp_loc = pos; pp_desc = f}
let mlexpr f = pexp dloc f

let make_forall f bl  =
  let f = List.fold_left
           (fun f x -> pexp f.pp_loc
                        (PPforall ([x.var], 
                         sort_to_type f.pp_loc x.sort, [], f ))) f bl
  in f.pp_desc

let make_exists f bl =
  let f = 
    List.fold_left 
      (fun f x -> pexp f.pp_loc 
        (PPexists ([x.var], sort_to_type f.pp_loc x.sort, f))) f bl
  in f.pp_desc

let make_infix op = function
  | x::l -> let f = List.fold_left 
                     (fun f x -> pexp x.pp_loc (PPinfix (f,op,x)))
                     x l
            in
              f.pp_desc
  | _ -> assert false

let make_distinct_aux elem l =
  List.map ( fun x -> PPinfix (elem, PPneq, x)) l

let make_distinct l =
  let rec aux = function
    | [] -> []
    | (x::xs) -> 
        List.rev_append (make_distinct_aux x xs) (aux xs)
  in
    List.map mlexpr (aux l)

let wequal x y = PPinfix (x, PPeq, y)

let rec make_equal = function
  | [] -> PPconst ConstTrue
  | [x] -> PPconst ConstTrue
  | [x;y] -> wequal x y
  | (x::y::z::xs) -> 
      PPinfix (mlexpr (wequal x y),
               PPand,
               mlexpr (make_equal (y::z::xs)))

let infix = function
  | "<" -> PPlt
  | "<=" -> PPle
  | ">" -> PPgt
  | ">=" -> PPge
  | "+" -> PPadd
  | "-" -> PPsub
  | "*" -> PPmul
  | "/" | "int___div" -> PPdiv
  | "int___mod" -> PPmod
  | _ -> assert false

let product f_map l1 l2 = 
  List.fold_left 
    (fun res (f1,t1) -> 
       List.fold_left 
	 (fun res (f2,t2) -> 
	    let f = match f1, f2 with
	      | None, None -> None
	      | (None, (Some _ as f)) | (Some _ as f, None) -> f
              | Some f1, Some f2 -> 
		  Some (pexp f2.pp_loc (PPinfix (f1,PPand,f2))) in
            (f,f_map t1 t2)::res) 
         res l2) [] l1

let term_to_formula f1 = 
  function 
    | [None,t] -> f1 t
    | l -> 
	make_infix PPand 
	  (List.map (function (Some f,x) ->
		       mlexpr (PPinfix (f,PPimplies,mlexpr (f1 x))) 
                     | _ -> assert false) l)

(* !inverse l1! *)
let apply_list_product f1 l1 = 
  term_to_formula f1 (List.fold_left (product (fun l x -> x::l)) [None,[]] l1)

let concat_product f1 = List.fold_left (fun env (f,t) -> (f1 f,t)::env)

module StringMap = Map.Make(String)

type env_unfold = {
  uterm : ((Why_ptree.lexpr option * Why_ptree.pp_desc) list) StringMap.t ; 
  uformula : Why_ptree.pp_desc StringMap.t
}

let rec term_to_desc env = function
  | Num str -> [None,PPconst (ConstInt str)]
  | Rat str -> assert false (*[None,PPconst (ConstReal str)]*)
  | Var str ->  (try StringMap.find str env.uterm
                with Not_found -> [None,PPvar str])
  | Fun ("+" | "-" | "*" | "/" | "int___mod" | "int___div" as s, [a;b]) -> 
      let ta = term env a and tb = term env b in
      (*PPinfix (ta, infix s, tb)*)
      product (fun x y -> PPinfix (x, infix s, y)) ta tb
        (* Le - est pour AUFLIRA *)
  | Fun (("-"|"~"), [a]) -> 
      List.map (fun (f,x) -> f,PPprefix(PPneg, x)) (term env a)
  | Fun (str,tlist) ->  
      List.map (fun (f,l) -> (f,PPapp (str,l )))
	(List.fold_left 
	   (product (fun l x -> x::l)) 
	   [None,[]]  (List.rev_map (term env) tlist))
	
  | Ite (f,t1,t2) ->  
      let ff = envformula env f in 
      let not_ff = 
	{ff with pp_desc = PPprefix (PPnot,pexp ff.pp_loc ff.pp_desc)} in
      let aux ff2 = function 
	  None -> Some ff2
        | Some f -> 
	    Some (pexp ff.pp_loc 
		    (PPinfix (ff2,PPand,pexp ff2.pp_loc f.pp_desc))) 
      in
      concat_product (aux ff) 
	(concat_product (aux not_ff) [] 
	   (term_to_desc env t2.term)) (term_to_desc env t1.term)

and term env a = 
  List.map (fun (f,t) -> (f,pexp a.tloc t)) (term_to_desc env a.term)

and form_to_desc env = function
    (* Pour l'instant on unfold *)
  | Flet (ident,f1,f2) -> (*raise Not_Implemented*)
      form_to_desc 
	{env with
	   uformula = 
	    StringMap.add ident 
	      (form_to_desc env f1.formula) env.uformula} f2.formula
      (*incorrect*)

  | Let (ident,t,f) -> 
(*      let f' = envformula env f in
      term_to_formula (fun x -> PPlet (ident,x,f')) (term env t)
*)

  (*Pforall ([ident],PPTvarid(ident,f1.floc),[],mlexpr (PPinfix(mlexpr
    (apply_list_product make_equal [(term env t);[None,mlexpr (PPvar
    ident)]]),PPimplies,envformula env f1)))*)
  form_to_desc {env with uterm = StringMap.add ident (term_to_desc
    env t.term) env.uterm} f.formula

  | Forall (binders,f1) -> 
      make_forall (envformula env f1) binders 
  | Exists (binders,f1) -> 
      make_exists (envformula env f1) binders
  | And l -> 
      make_infix PPand (List.map (envformula env) l)
  | Or l -> 
      make_infix PPor (List.map (envformula env) l)
  | Not f -> 
      PPprefix (PPnot, envformula env f)
  | Implies (f1,f2) -> 
      make_infix PPimplies (List.map (envformula env) [f1;f2])
  | Xor l -> 
      raise Not_Implemented
  | Iff l -> 
      make_infix PPiff (List.map (envformula env) l )
  | Fite (f,f_if,f_else) -> 
      PPif (envformula env f,envformula env f_if,envformula env f_else)

  | True -> PPconst ConstTrue
  | False -> PPconst ConstFalse

  | Fvar str -> 
      (try StringMap.find str env.uformula with Not_found -> PPvar str)
	
  | Distinct l -> 
      apply_list_product 
	(fun x -> (make_infix PPand (make_distinct x))) 
	(List.rev_map (term env) l)
	
  | Equals l -> apply_list_product make_equal (List.rev_map (term env) l)
  | Pred (("<" | "<=" | ">" | ">=" as s), [a; b]) -> 
      apply_list_product 
	(function [x;y] -> PPinfix (x,infix s,y) |_-> assert false) 
	(List.rev_map (term env) [a;b])

  | Pred (str,tlist) -> 
      apply_list_product 
	(fun x -> PPapp (str, x)) (List.rev_map (term env) tlist)

and envformula env f = pexp f.floc (form_to_desc env f.formula)

let formula  = envformula {uterm = StringMap.empty ; uformula = StringMap.empty}

let psig_to_pdef (pos,psig) =
  Logic (pos, Symbols.Other, [psig.pname],
	 PPredicate (List.map curry_sort_to_type psig.pargs))

let fsig_to_fdef (pos,fsig) =
  Logic (pos, Symbols.Other, [fsig.fname],
	 PFunction ((List.map curry_sort_to_type fsig.fargs),
                    curry_sort_to_type fsig.fres ))

let sortdecl_to_type (pos,s) =
  TypeDecl (pos,[], s, Abstract)
    

let bench_to_why = function
  | Pblogic _ -> [] (* this seems to be comments only, throw away *)
  | Pbstatus s -> []
  | Pbextr_preds plist -> 
      List.map psig_to_pdef plist
  | Pbextr_funs flist -> 
      List.map fsig_to_fdef flist
  | Pbextr_sorts sorts -> 
      List.map sortdecl_to_type sorts
  | Pbformula (pos,f) -> 
      [Goal (pos, "", formula f)]
  | Pbassumption (pos,f) -> 
      [Axiom (pos, "", formula f)]
  | Pbrewriting (pos, lf) -> 
      [Rewriting (pos, "", List.map formula lf)]
  | Pannotation  -> []

