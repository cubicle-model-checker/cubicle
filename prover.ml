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


module T = Smt.Term
module F = Smt.Formula

module SMT = Smt.Make (Options)

let proc_terms =
  List.iter 
    (fun x -> Smt.Symbol.declare x [] Smt.Type.type_proc)
      (Weakmem.hP0 :: Variable.procs);
  List.map (fun x -> T.make_app x []) Variable.procs

let distinct_vars =
  let t = Array.make max_proc F.f_true in
  let _ = 
    List.fold_left 
      (fun (acc,i) v -> 
       (*if i<>0 then*) t.(i) <- F.make_lit F.Neq (v::acc);
	 v::acc, i+1) 
      ([T.make_app Weakmem.hP0 []],0) proc_terms 
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
  | Read _ -> failwith "Prover.make_term : Read should not be there"
  | Write _ -> failwith "Prover.make_term : Write should not be there"
  | Fence _ -> failwith "Prover.make_term : Fence should not be there"

let rec make_formula_set sa =
  F.make F.And (SAtom.fold (fun a l -> make_literal a::l) sa [])

and make_literal = function
  | Atom.True -> F.f_true 
  | Atom.False -> F.f_false
  | Atom.Comp (x, op, y) ->
      let tx = make_term x in
      let ty = make_term y in
      F.make_lit (make_op_comp op) [tx; ty]
  | Atom.Ite (la, a1, a2) ->
      let f = make_formula_set la in
      let a1 = make_literal a1 in
      let a2 = make_literal a2 in
      let ff1 = F.make F.Imp [f; a1] in
      let ff2 = F.make F.Imp [F.make F.Not [f]; a2] in
      F.make F.And [ff1; ff2]


(* let make_formula atoms = *)
(*   F.make F.And (Array.fold_left (fun l a -> make_literal a::l) [] atoms) *)

let make_formula ?(fp=false) array =
  let sa, evts, rels = Weakorder.extract_events_array array in
  let f = make_formula_set sa in
  match Weakorder.make_orders ~fp evts rels with
  | None -> f
  | Some fo -> if debug_smt then eprintf ">>>> rels: %a@." F.print fo;
               F.make F.And [f; fo]

let make_formula_set ?(fp=false) satom =
  let sa, evts, rels = Weakorder.extract_events_set satom in
  let f = make_formula_set sa in
  match Weakorder.make_orders ~fp evts rels with
  | None -> f
  | Some fo -> if debug_smt then eprintf ">>>> rels: %a@." F.print fo;
               F.make F.And [f; fo]

module HAA = Hashtbl.Make (ArrayAtom)

let make_formula =
  let cache = HAA.create 200001 in
  fun ?(fp=false) atoms -> (* dekker2 : 2110 false, 18588 true*)
    try HAA.find cache atoms
    with Not_found ->
      let f = make_formula ~fp atoms in
      HAA.add cache atoms f;
      f

let make_formula ?(fp=false) array =
  TimeFormula.start ();
  let f = make_formula ~fp array in
  TimeFormula.pause ();
  f

let make_formula_set ?(fp=false) satom =
  TimeFormula.start ();
  let f = make_formula_set ~fp satom in
  TimeFormula.pause ();
  f


(* let make_disjunction nodes = F.make F.Or (List.map make_formula nodes) *)


(* let make_conjuct atoms1 atoms2 = *)
(*   let l = Array.fold_left (fun l a -> make_literal a::l) [] atoms1 in *)
(*   let l = Array.fold_left (fun l a -> make_literal a::l) l atoms2 in *)
(*   F.make F.And l *)


let make_init_dnfs s nb_procs = (* S only *) (* no events to handle *)
  let { init_cdnf } = Hashtbl.find s.t_init_instances nb_procs in
  List.rev_map (List.rev_map (fun sa -> make_formula_set sa)) init_cdnf

let get_user_invs s nb_procs = (* S only *) (* no events to handle *)
  let { init_invs } =  Hashtbl.find s.t_init_instances nb_procs in
  List.rev_map (fun a -> F.make F.Not [make_formula a]) init_invs

let unsafe_conj { tag = id; cube = cube } nb_procs invs init = (* S only *)
  if debug_smt then eprintf ">>> [smt] safety with: %a@." F.print init;
  SMT.clear ();
  SMT.assume ~id (distinct_vars nb_procs);
  List.iter (SMT.assume ~id) invs; (* without events *)
  let sa = Weakwrite.satisfy_unsatisfied_reads cube.Cube.litterals in
  let f = make_formula_set ~fp:false sa in
  if debug_smt then eprintf "[smt] safety: %a and %a@." F.print f F.print init;
  SMT.assume ~id init; (* without events *)
  SMT.assume ~id f;
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


let reached args s sa = (* FW only *) (* events not handled yet *)
  SMT.clear ();
  SMT.assume ~id:0 (distinct_vars (List.length args));
  let f = make_formula_set ~fp:false (SAtom.union sa s) in
  SMT.assume ~id:0 f;
  SMT.check ()


let assume_goal_no_check { tag = id; cube = cube } = (* FP only *)
  SMT.clear ();
  SMT.assume ~id (distinct_vars (List.length cube.Cube.vars));
  (* let f = make_formula ~fp:true cube.Cube.array in *)
  (* let f = make_formula ~fp:false cube.Cube.array in *)
  let f = make_formula_set ~fp:true cube.Cube.litterals in
  (* let f = make_formula_set ~fp:false cube.Cube.litterals in *)
  if debug_smt then eprintf "[smt] goal g: %a@." F.print f;
  SMT.assume ~id f

let assume_node_no_check { tag = id } ap = (* FP only *)
  let f = make_formula ~fp:true ap in
  let f = F.make F.Not [f] in
  if debug_smt then eprintf "[smt] assume node: %a@." F.print f;
  SMT.assume ~id f

let assume_goal n = (* FP only *)
  assume_goal_no_check n;
  SMT.check ~fp:true ()
  (* SMT.check ~fp:false () *)

let assume_node n ap = (* FP only *)
  assume_node_no_check n ap;
  SMT.check ~fp:true ()
  (* SMT.check ~fp:false () *)


let run () = SMT.check ~fp:true () (* FP only *)
(* let run () = SMT.check ~fp:false () (\* FP only *\) *)

let check_guard args sa reqs = (* FW only *)
  SMT.clear ();
  SMT.assume ~id:0 (distinct_vars (List.length args));
  let f = make_formula_set ~fp:false (SAtom.union sa reqs) in
  SMT.assume ~id:0 f;
  SMT.check ()

let assume_goal_nodes n nodes = (* FP only *)
  assume_goal_no_check n;
  List.iter (fun (n, a) -> assume_node_no_check n a) nodes;
  SMT.check ~fp:true ()
  (* SMT.check ~fp:false () *)


let acyclic ({ tag = id; cube = cube } as n) =
  SMT.clear ();
  let nb_procs = List.length (Node.variables n) in
  SMT.assume ~id (distinct_vars nb_procs);
  (* Can read from init => can read from other threads ? *)
  (* let sa = Weakwrite.satisfy_unsatisfied_reads cube.Cube.litterals in *)
  let sa, evts, rels = (* rels = po, rf, fence, sync *)
    Weakorder.extract_events_set (cube.Cube.litterals) in
  let sa = SAtom.filter (fun a -> match a with
    | Atom.Comp (Access (a,[_;_;_;_]), Eq, Elem _)
    | Atom.Comp (Elem _, Eq, Access (a,[_;_;_;_]))
	 when Hstring.equal a Weakmem.hRf -> true
    | _ -> false
  ) sa in
  if not (SAtom.is_empty sa) then begin
    let f = make_formula_set sa in (* just for rf *)
    SMT.assume ~id f
  end;
  match Weakorder.make_orders evts rels with
  | None -> ()
  | Some fo -> SMT.assume ~id fo;
               SMT.check ()

let init () =
  SMT.init_axioms ()
