(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon, Universite Paris-Sud 11              *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

open Ast
open Atom
open Options

module AE = AltErgo

let vrai = AE.Formula.mk_lit AE.Literal.LT.vrai 0
let faux = AE.Formula.mk_lit AE.Literal.LT.faux 0
let ty_proc = AE.Ty.Tint
let ty_int = AE.Ty.Tint

let op_arith x = 
  let sx = match x with Plus -> AE.Symbols.Plus | Minus -> AE.Symbols.Minus in
  AE.Symbols.Op sx

let make_variable ty z = AE.Term.make (AE.Symbols.name z) []  ty

let get a z = 
  let {AE.Term.ty=ty} = AE.Term.view a in
  match ty with
    | AE.Ty.Tfarray(_, ty') ->
	AE.Term.make (AE.Symbols.Op AE.Symbols.Get) [a; z] ty'
    | _ -> assert false

let global_eq g c = 
  AE.Formula.mk_lit (AE.Literal.LT.make (AE.Literal.Eq (g, c))) 0

let make_distincts = function
  | [] | [_] -> vrai
  | l ->
      AE.Formula.mk_lit (AE.Literal.LT.make (AE.Literal.Distinct(false, l))) 0

let make_term env = function
  | Elem e ->
      begin try
	let _, _, te = Hashtbl.find env e in te
      with Not_found -> make_variable ty_proc e end
  | Const i ->
      AE.Term.int (string_of_int i)
  | Access (a, i) -> 
      let _, _, ta = Hashtbl.find env a in
      let ti = 
	try let _, _, ti = Hashtbl.find env i in ti 
	with Not_found -> make_variable ty_proc i 
      in
      get ta ti
  | Arith (x, op, i) ->
      let _, _, tx = Hashtbl.find env x in
      let si = AE.Term.int (string_of_int i) in
      AE.Term.make (op_arith op) [tx;si] ty_int

let rec make_formula env f = 
  List.fold_left (fun f a -> AE.Formula.mk_and f (make_literal env a) 0) f

and make_literal env = function
  | True -> vrai 
  | False -> faux
  | Comp (Elem ("True" | "False" as b), op, x) 
  | Comp (x, op, Elem ("True" | "False" as b))-> 
      let tx = make_term env x in
      let p = AE.Literal.LT.mk_pred tx in
      let lit = 
	match op, b with
	  | Eq, "True" | Neq, "False" ->  p 
	  | Eq, "False" | Neq, "True" -> AE.Literal.LT.neg p
	  | _ -> assert false
      in
      AE.Formula.mk_lit lit 0

  | Comp (x, op, y) -> 
      let tx = make_term env x in
      let ty = make_term env y in
      let lit = 
	match op with
	  | Eq -> AE.Literal.LT.make (AE.Literal.Eq(tx, ty)) 
	  | Neq -> AE.Literal.LT.make (AE.Literal.Distinct(false, [tx; ty]))
	  | Lt ->
	      AE.Literal.LT.make 
		(AE.Literal.Builtin(true, AE.Hstring.make "<", [tx;ty])) 
	  | Le ->
	      AE.Literal.LT.make 
		(AE.Literal.Builtin(true, AE.Hstring.make "<=", [tx;ty])) 
      in
      AE.Formula.mk_lit lit 0
  | Ite (la, a1, a2) -> 
      let f = make_formula env vrai (SAtom.elements la) in
      let a1 = make_literal env a1 in
      let a2 = make_literal env a2 in
      let ff1 = AE.Formula.mk_imp f a1 0 in
      let ff2 = AE.Formula.mk_imp (AE.Formula.mk_not f) a2 0 in
      AE.Formula.mk_and ff1 ff2 0

let contain_arg z = function
  | Elem x | Arith (x, _, _) -> x = z
  | Access (x, y) -> x = z || y = z
  | Const _ -> false

let has_var z = function
  | True | False -> false
  | Comp (t1, _, t2) -> (contain_arg z t1) || (contain_arg z t2)
  | Ite _ -> assert false

let make_init env {t_init = arg, sa } f lvars =
  match arg with
    | None ->   
	make_formula env f (SAtom.elements sa)
    | Some z ->
	let sa, cst = SAtom.partition (has_var z) sa in
	let f = make_formula env f (SAtom.elements cst) in
	List.fold_left 
	  (fun f hash -> 
	     let la = SAtom.elements (subst_atoms [z, hash] sa) in
	     make_formula env f la) f lvars

let make_alpha = 
  List.fold_left 
    (fun f (x, y) -> 
       let x = make_variable ty_proc x in
       let y = make_variable ty_proc y in
       let lit = AE.Literal.LT.make (AE.Literal.Eq(x,y)) in
       let eq = AE.Formula.mk_lit lit 0 in
       AE.Formula.mk_and f eq 0) vrai

let unsafe ({ t_unsafe = (vars, sa); t_env = env } as ts) = 
  let tvars = List.map (make_variable ty_proc) vars in
  let distincts = make_distincts tvars in
  let init = make_init env ts distincts vars in
  make_formula env init (SAtom.elements sa)

let fixpoint {t_env=env} vars np p =  
  let vars = List.map (make_variable ty_proc) vars in
  let distincts = make_distincts vars in
  let np = make_formula env distincts (SAtom.elements np) in
  let p =  make_formula env vrai (SAtom.elements p) in
  AE.Formula.mk_not (AE.Formula.mk_imp np p 0) 
  
let extended_fixpoint {t_env=env} vars d np p = 
  let vars = List.map (make_variable ty_proc) vars in
  let preambule = 
    AE.Formula.mk_and (make_distincts vars) (make_alpha d) 0 in
  let np = make_formula env preambule (SAtom.elements np) in
  let p =  make_formula env vrai (SAtom.elements p) in
  AE.Formula.mk_not (AE.Formula.mk_imp np p 0)
  
let simpl_check env vars sa1 sa2  = 
  try
    let tvars = List.map (make_variable ty_proc) vars in
    let distincts = make_distincts tvars in
    let f1 = make_formula env vrai (SAtom.elements sa1) in
    let f2 = make_formula env vrai (SAtom.elements sa2) in
    let f = AE.Formula.mk_and distincts (AE.Formula.mk_and 
      (AE.Formula.mk_not f1) (AE.Formula.mk_not f2) 0) 0 in
    let gf = { AE.Sat.f = f; age = 0; name = None; mf=false; gf=true} in
    ignore(AE.Sat.unsat AE.Sat.empty gf);
    true
  with 
    | AE.Sat.Sat _ | AE.Sat.I_dont_know -> false
    | AE.Sat.Unsat _ -> true


(* ---------- extra stuff ----------- *)

(*
  let alt_ergo_unsafe = 
    if not debug_altergo then fun _ -> 	() else 
      fun f ->
	eprintf "[Unsafe check] Alt-Ergo is called on:@.%a\n@." 
	  AE.Formula.print f

  let alt_ergo_fixpoint = 
    if not debug_altergo then fun _ -> () else 
      fun f ->
	eprintf "[Fixpoint check] Alt-Ergo is called on:@.%a\n@." 
	  AE.Formula.print f
*)
