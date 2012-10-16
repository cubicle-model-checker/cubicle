(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                  Universite Paris-Sud 11                               *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

open Format
open Ast
open Atom
open Options

module T = Smt.Term
module F = Smt.Formula

module TimeF = Timer.Make (struct end)

module SMT = Smt.Make (struct end)

let proc_terms =
  List.iter 
    (fun x -> Smt.Symbol.declare x [] Smt.Type.type_proc) proc_vars;
  List.map (fun x -> T.make_app x []) proc_vars

let distinct_vars = 
  let t = Array.create max_proc F.f_true in
  let _ = 
    List.fold_left 
      (fun (acc,i) v -> 
	 if i<>0 then t.(i) <- F.make_lit F.Neq (v::acc);
	 v::acc, i+1) 
      ([],0) proc_terms 
  in
  function n -> if n = 0 then F.f_true else t.(n-1)

let order_vars =
  let t = Array.create max_proc F.f_true in
  let _ =
    List.fold_left
      (fun (acc, lf, i) v ->
        match acc with
          | v2::r ->
            let lf = (F.make_lit F.Lt [v;v2]) :: lf in
            t.(i) <- F.make F.And lf;
            v::acc, lf, i+1
          | [] -> v::acc, lf, i+1)
      ([], [], 0) proc_terms
  in
  function n -> if n = 0 then F.f_true else t.(n-1)


let make_op_arith = function Plus -> T.Plus | Minus -> T.Minus
let make_op_comp = function
  | Eq -> F.Eq
  | Lt -> F.Lt
  | Le -> F.Le
  | Neq -> F.Neq

let make_const = function
  | ConstInt i -> T.make_int i
  | ConstReal i -> T.make_real i
  | ConstName n -> T.make_app n []

let ty_const = function
  | ConstInt _ -> Smt.Type.type_int
  | ConstReal _ -> Smt.Type.type_real
  | ConstName n -> snd (Smt.Symbol.type_of n)

let rec mult_const tc c i =
 match i with
  | 0 -> 
    if ty_const c = Smt.Type.type_int then T.make_int (Num.Int 0)
    else T.make_real (Num.Int 0)
  | 1 -> tc
  | -1 -> T.make_arith T.Minus (mult_const tc c 0) tc
  | i when i > 0 -> T.make_arith T.Plus (mult_const tc c (i - 1)) tc
  | i when i < 0 -> T.make_arith T.Minus (mult_const tc c (i + 1)) tc
  | _ -> assert false

let make_arith_cs =
  MConst.fold 
    (fun c i acc ->
      let tc = make_const c in
      let tci = mult_const tc c i in
       T.make_arith T.Plus acc tci)

let make_cs cs =
  let c, i = MConst.choose cs in
  let t_c = make_const c in
  let r = MConst.remove c cs in
  if MConst.is_empty r then mult_const t_c c i
  else make_arith_cs r (mult_const t_c c i)
	 
let rec make_term = function
  | Elem (e, _) -> T.make_app e []
  | Const cs -> make_cs cs 
  | Access (a, i, _) -> T.make_app a [T.make_app i []]
  | Arith (x, cs) -> 
      let tx = make_term x in
      make_arith_cs cs tx

let rec make_formula_set sa = 
  F.make F.And (SAtom.fold (fun a l -> make_literal a::l) sa [])

and make_literal = function
  | True -> F.f_true 
  | False -> F.f_false
  | Comp (x, op, y) ->
      let tx = make_term x in
      let ty = make_term y in
      F.make_lit (make_op_comp op) [tx; ty]
  | Ite (la, a1, a2) -> 
      let f = make_formula_set la in
      let a1 = make_literal a1 in
      let a2 = make_literal a2 in
      let ff1 = F.make F.Imp [f; a1] in
      let ff2 = F.make F.Imp [F.make F.Not [f]; a2] in
      F.make F.And [ff1; ff2]

let make_formula atoms =
  F.make F.And (Array.fold_left (fun l a -> make_literal a::l) [] atoms)


let make_disjunction nodes = F.make F.Or (List.map make_formula nodes)


let make_conjuct atoms1 atoms2 =
  let l = Array.fold_left (fun l a -> make_literal a::l) [] atoms1 in
  let l = Array.fold_left (fun l a -> make_literal a::l) l atoms2 in
  F.make F.And l

let make_init {t_init = arg, sa } lvars =
  match arg with
    | None ->   
	make_formula_set sa
    | Some z ->
	let sa, cst = SAtom.partition (has_var z) sa in
	let f = make_formula_set cst in
	let fsa = 
	  List.rev_map
	    (fun h -> make_formula_set (subst_atoms [z, h] sa)) lvars
	in
	F.make F.And (f::fsa)

let unsafe ({ t_unsafe = (args, sa) } as ts) =
  SMT.clear ();
  SMT.assume 
    ~profiling ~id:ts.t_nb (distinct_vars (List.length args));
  (* SMT.assume (order_vars (List.length args)); *)
  if profiling then TimeF.start ();
  let init = make_init ts (* (List.rev_append ts.t_glob_proc  *) args in
  let f = make_formula_set sa in
  if profiling then TimeF.pause ();
  if debug_smt then eprintf "[smt] safety: %a and %a@." F.print f F.print init;
  SMT.assume ~profiling ~id:ts.t_nb init;
  SMT.assume ~profiling ~id:ts.t_nb f;
  SMT.check  ~profiling ()


let assume_goal ({t_unsafe = (args, _); t_arru = ap } as ts) =
  SMT.clear ();
  SMT.assume 
    ~profiling ~id:ts.t_nb (distinct_vars (List.length args));
  (* SMT.assume (order_vars (List.length args)); *)
  if profiling then TimeF.start ();
  let f = make_formula ap in
  if profiling then TimeF.pause ();
  if debug_smt then eprintf "[smt] goal g: %a@." F.print f;
  SMT.assume ~profiling ~id:ts.t_nb f;
  SMT.check  ~profiling ()

let assume_node ap ~id =
  if profiling then TimeF.start ();
  let f = F.make F.Not [make_formula ap] in
  if profiling then TimeF.pause ();
  if debug_smt then eprintf "[smt] assume node: %a@." F.print f;
  SMT.assume ~profiling ~id f;
  SMT.check  ~profiling ()


let check_guard args sa reqs =
  SMT.clear ();
  SMT.assume ~profiling ~id:0 (distinct_vars (List.length args));
  if profiling then TimeF.start ();
  let f = make_formula_set (SAtom.union sa reqs) in
  if profiling then TimeF.pause ();
  SMT.assume ~profiling ~id:0 f;
  SMT.check ~profiling ()

let unsat_core_wrt_node uc ap =
  Array.fold_left (fun acc a ->
    match make_literal a with
      | F.Lit la when List.mem [la] uc -> SAtom.add a acc
      | _ -> acc) 
    SAtom.empty ap
  
(*
let extract_candidates args ap forward_nodes =
  List.fold_left (fun acc fs ->
    try
      let c = 
	List.fold_left (fun acc fp ->
	  SMT.clear ();
	  SMT.assume ~profiling (F.Ground (distinct_vars (List.length args)));
	  if profiling then TimeF.start ();
	  let f = F.Ground (make_conjuct ap fp) in
	  if profiling then TimeF.pause ();
	  try 
	    SMT.assume ~profiling f;
	    SMT.check ~profiling;
	    raise Exit
	  with Smt.Unsat uc ->
	    let c = unsat_core_wrt_node uc ap in
	    SAtom.union c acc
	    (* let acc =  *)
	    (*   if !first then (first := false; c) *)
	    (*   else SAtom.inter c acc in *)
	    (* if SAtom.is_empty acc then raise Exit else acc *)
	) SAtom.empty fs
      in if SAtom.cardinal c > 1 then c :: acc else acc
    with Exit -> acc)
    [] forward_nodes
*)
