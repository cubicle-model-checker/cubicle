(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2014                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

open Format
open Options
open Util
open Ast
open Types

module HMap = Hstring.HMap

module T = Smt.Term
module F = Smt.Formula

module SMT = Smt.Make (Options)

let proc_terms =
  let procs = (Hstring.make "#0") :: Variable.procs in
  List.iter 
    (fun x -> Smt.Symbol.declare x [] Smt.Type.type_proc) procs;
  List.map (fun x -> T.make_app x []) Variable.procs

let distinct_vars =
  let t = Array.make max_proc F.f_true in
  let _ = 
    List.fold_left 
      (fun (acc,i) v -> 
       (*if i<>0 then*) t.(i) <- F.make_lit F.Neq (v::acc);
	 v::acc, i+1) 
      ([T.make_app (Hstring.make "#0") []],0) proc_terms 
  in
  function n -> if n = 0 then F.f_true else t.(n-1)

(* let _ = SMT.assume ~id:0 (distinct_vars max_proc) *)

let order_vars =
  let t = Array.make max_proc F.f_true in
  let _ =
    List.fold_left
      (fun (acc, lf, i) v ->
        match acc with
          | v2::r ->
            let lf = (F.make_lit F.Lt [v2;v]) :: lf in
            t.(i) <- F.make F.And lf;
            v::acc, lf, i+1
          | [] -> v::acc, lf, i+1)
      ([], [], 0) proc_terms
  in
  function n -> if n = 0 then F.f_true else t.(n-1)

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
  | Access (a, li) -> T.make_app a (List.map (fun i -> T.make_app i []) li)
  | Arith (x, cs) -> 
      let tx = make_term x in
      make_arith_cs cs tx
  | Field (t, f) -> T.make_app f [make_term t]
  | List tl -> failwith "Prover.make_term List TODO"
  | Read _ -> failwith "Prover.make_term : Read should not be in atom"
  | Write _ -> failwith "Prover.make_term : Write should not be in atom"
  | Fence _ -> failwith "Prover.make_term : Fence should not be in atom"

let rec make_formula_set sa =
  let sa, evts, ord = Weakmem.split_events_orders_set sa in
  (F.make F.And (SAtom.fold (fun a l -> make_literal a::l) sa []), evts, ord)

and make_literal = function
  | Atom.True -> F.f_true
  | Atom.False -> F.f_false
  | Atom.Comp (x, op, y) ->
      let tx = make_term x in
      let ty = make_term y in
      F.make_lit (make_op_comp op) [tx; ty]
  | Atom.Ite (la, a1, a2) -> 
      let (f, _, _) = make_formula_set la in
      let a1 = make_literal a1 in
      let a2 = make_literal a2 in
      let ff1 = F.make F.Imp [f; a1] in
      let ff2 = F.make F.Imp [F.make F.Not [f]; a2] in
      F.make F.And [ff1; ff2]


let make_formula atoms =
  let sa, evts, ord = Weakmem.split_events_orders_array atoms in
  (F.make F.And (SAtom.fold (fun a l -> make_literal a::l) sa []), evts, ord)

module HAA = Hashtbl.Make (ArrayAtom)

let make_formula =
  let cache = HAA.create 200001 in
  fun atoms ->
    try HAA.find cache atoms
    with Not_found ->
      let f = make_formula atoms in
      HAA.add cache atoms f;
      f

let make_formula array =
  TimeFormula.start ();
  let f = make_formula array in
  TimeFormula.pause ();
  f

let make_formula_set satom =
  TimeFormula.start ();
  let f = make_formula_set satom in
  TimeFormula.pause ();
  f

(*
let make_disjunction nodes = F.make F.Or (List.map make_formula nodes)


let make_conjuct atoms1 atoms2 =
  let l = Array.fold_left (fun l a -> make_literal a::l) [] atoms1 in
  let l = Array.fold_left (fun l a -> make_literal a::l) l atoms2 in
  F.make F.And l
 *)

let make_init_dnfs s nb_procs = (* S only *)
  let { init_cdnf } = Hashtbl.find s.t_init_instances nb_procs in
  List.rev_map (fun dnf ->
    List.rev_map (make_formula_set) (List.map Weakmem.events_of_satom dnf)
  ) init_cdnf

let get_user_invs s nb_procs = (* S only *)
  let { init_invs } =  Hashtbl.find s.t_init_instances nb_procs in
  List.rev_map (fun a ->
    let (f, _, _) = make_formula a in F.make F.Not [f]) init_invs

let unsafe_conj { tag = id; cube = cube } nb_procs invs (init, ievts, iord) = (*S only*)
  if debug_smt then eprintf ">>> [smt] safety with: %a@." F.print init;
  SMT.clear ();
  SMT.assume ~id (distinct_vars nb_procs);
  List.iter (SMT.assume ~id) invs;
  let (f, evts, ord) = make_formula_set cube.Cube.litterals in
  if debug_smt then eprintf "[smt] safety: %a and %a@." F.print f F.print init;
  SMT.assume ~id init;
  SMT.assume ~id f;
  let evts = Weakmem.merge_evts ievts evts in
  let ord = Weakmem.merge_ord iord ord in
  SMT.assume ~id (Weakmem.make_orders evts ord);
  SMT.check ()

let unsafe_dnf node nb_procs invs dnf = (* S only *)
  try
    let uc =
      List.fold_left (fun accuc init ->
        try 
          unsafe_conj node nb_procs invs init;
          raise Exit
        with Smt.Unsat uc -> List.rev_append uc accuc)
        [] dnf in
    raise (Smt.Unsat uc)
  with Exit -> ()

let unsafe_cdnf s n = (* S only *)
  let nb_procs = List.length (Node.variables n) in
  let cdnf_init = make_init_dnfs s nb_procs in
  let invs = get_user_invs s nb_procs in
  List.iter (unsafe_dnf n nb_procs invs) cdnf_init

let unsafe s n = unsafe_cdnf s n (* S only *)


let reached args s sa = (* FW only *)
  SMT.clear ();
  SMT.assume ~id:0 (distinct_vars (List.length args));
  let (f, _, _) = make_formula_set (SAtom.union sa s) in
  SMT.assume ~id:0 f;
  SMT.check ()


let assume_goal_no_check { tag = id; cube = cube } = (* FP only *)
  SMT.clear ();
  SMT.assume ~id (distinct_vars (List.length cube.Cube.vars));
  let (f, evts, ord) = make_formula cube.Cube.array in
  if debug_smt then eprintf "[smt] goal g: %a@." F.print f;
  SMT.assume ~id f;
  SMT.assume ~id (Weakmem.make_orders ~fp:true evts ord)

let assume_node_no_check { tag = id } ap = (* FP only *)
  let (f, evts, ord) = make_formula ap in
  let f = F.make F.Not [f] in
  if debug_smt then eprintf "[smt] assume node: %a@." F.print f;
  SMT.assume ~id f;
  SMT.assume ~id (F.make F.Not [(Weakmem.make_orders ~fp:true evts ord)])

let assume_goal n = (* FP only *)
  assume_goal_no_check n;
  SMT.check ~fp:true ()

let assume_node n ap = (* FP only *)
  assume_node_no_check n ap;
  SMT.check ~fp:true ()


let run () = SMT.check ~fp:true () (* FP only *)

let check_guard args sa reqs = (* FW only *)
  SMT.clear ();
  SMT.assume ~id:0 (distinct_vars (List.length args));
  let (f, _, _) = make_formula_set (SAtom.union sa reqs) in
  SMT.assume ~id:0 f;
  SMT.check ()

let assume_goal_nodes { tag = id; cube = cube } nodes = (* FP only *)
  SMT.clear ();
  SMT.assume ~id (distinct_vars (List.length cube.Cube.vars));
  let (f, evts, ord) = make_formula cube.Cube.array in
  if debug_smt then eprintf "[smt] goal g: %a@." F.print f;
  SMT.assume ~id f;
  SMT.assume ~id (Weakmem.make_orders ~fp:true evts ord);
  List.iter (fun (n, a) -> assume_node_no_check n a) nodes;
  SMT.check ~fp:true ()

let init () =
  SMT.init_axioms ()
