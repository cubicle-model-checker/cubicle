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

let htrue = Hstring.make "true"
let hfalse = Hstring.make "false"

let cpt_check = ref 0

module TimeAE = Timer.Make(struct end)

let vrai = AE.Formula.mk_lit AE.Literal.LT.vrai 0
let faux = AE.Formula.mk_lit AE.Literal.LT.faux 0
let ty_proc = AE.Ty.Tint
let ty_int = AE.Ty.Tint

let nb_calls () = !cpt_check

let op_arith x = 
  let sx = match x with Plus -> AE.Symbols.Plus | Minus -> AE.Symbols.Minus in
  AE.Symbols.Op sx

let make_variable ty z = AE.Term.make (AE.Symbols.name (Hstring.view z)) []  ty

let get ta a z = 
  let {AE.Term.ty=ty} = AE.Term.view ta in
  match ty with
    | AE.Ty.Tfarray(_, ty') ->
        (* Theory of arrays if needed *)
	(* AE.Term.make (AE.Symbols.Op AE.Symbols.Get) [a; z] ty' *)
        (* Use UF instead when no affectations done in arrays *)
	AE.Term.make (AE.Symbols.name (Hstring.view a)) [z] ty'
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
	let _, _, te = Hstring.H.find env e in te
      with Not_found -> make_variable ty_proc e end
  | Const i ->
      AE.Term.int (string_of_int i)
  | Access (a, i) -> 
      let _, _, ta = Hstring.H.find env a in
      let ti = 
	try let _, _, ti = Hstring.H.find env i in ti 
	with Not_found -> make_variable ty_proc i 
      in
      get ta a ti
  | Arith (x, op, i) ->
      let _, _, tx = Hstring.H.find env x in
      let si = AE.Term.int (string_of_int i) in
      AE.Term.make (op_arith op) [tx;si] ty_int

let rec make_formula env f = 
  List.fold_left (fun f a -> AE.Formula.mk_and f (make_literal env a) 0) f


and make_formula_atoms env atoms =
  try
    let f = SAtom.choose atoms in
    let ratoms = SAtom.remove f atoms in
    SAtom.fold (fun a acc ->
      AE.Formula.mk_and acc (make_literal env a) 0)
      ratoms (make_literal env f)
  with Not_found -> vrai

and make_formula_array env atoms =
  Array.fold_left (fun acc a -> 
    AE.Formula.mk_and acc (make_literal env a) 0)
    vrai atoms

and make_literal env = function
  | True -> vrai 
  | False -> faux
  | Comp (Elem b, op, x) 
  | Comp (x, op, Elem b) when 
      Hstring.compare htrue b = 0 || Hstring.compare hfalse b = 0 -> 
      let tx = make_term env x in
      let p = AE.Literal.LT.mk_pred tx in
      let lit = 
	if (op = Eq && Hstring.compare htrue b = 0) 
	  || (op = Neq && Hstring.compare hfalse b = 0)
	then p
	else if (op = Eq && Hstring.compare hfalse b = 0) 
	    || (op = Neq && Hstring.compare htrue b = 0)
	then AE.Literal.LT.neg p
	else assert false
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

let empty vars =
  let vars = List.map (make_variable ty_proc) vars in
  let distincts = make_distincts vars in
  let df = { AE.Sat.f = distincts; age = 0; name = None; mf=false; gf=false} in
  AE.Sat.assume df

let check () =
  incr cpt_check;
  AE.Sat.check ()

let unsafe ({ t_unsafe = (vars, sa); t_env = env } as ts) =
  TimeAE.start ();
  AE.Sat.clear ();
  let tvars = List.map (make_variable ty_proc) vars in
  let distincts = make_distincts tvars in
  let init = make_init env ts distincts vars in
  let f = make_formula env init (SAtom.elements sa) in
  let gf = { AE.Sat.f = f; age = 0; name = None; mf = false; gf = true} in
  AE.Sat.assume gf;
  try 
    check ();
    TimeAE.pause ()
  with e -> TimeAE.pause (); raise e

let add_goal {t_unsafe = (args, np); t_arru = ap; t_env=env} =
  TimeAE.start ();
  AE.Sat.clear ();
  empty args; 
  let f = make_formula_array env ap in
  if debug_altergo then Format.eprintf "goal g: %a@." AE.Formula.print f;
  let gf = { AE.Sat.f = f; age = 0; name = None; mf=true; gf=true} in
  AE.Sat.assume gf;
  try 
    check ();
    TimeAE.pause ()
  with e -> TimeAE.pause (); raise e

let add_node env ap =
  TimeAE.start ();
  let f = 
    AE.Formula.mk_not (make_formula_array env ap)
  in
  if debug_altergo then Format.eprintf "axiom node: %a@." AE.Formula.print f;
  let gf = 
    { AE.Sat.f = f; age = 0; name = None; mf=false; gf=false} in
  AE.Sat.assume gf;
  try 
    check ();
    TimeAE.pause ()
  with e -> TimeAE.pause (); raise e

let check_fixpoint ({t_env=env} as s) nodes =
  try
    add_goal s;
    List.iter (add_node env) nodes;
    false
  with
    | Exit -> false
    | AE.Sat.Sat _ | AE.Sat.I_dont_know -> false
    | AE.Sat.Unsat _ -> true
