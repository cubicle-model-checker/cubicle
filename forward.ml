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
open Options
open Ast
open Atom
open Cube




let prime_h h =
  Hstring.make ((Hstring.view h)^"@0")

let prime_term t = match t with
  | Elem (e, Glob) -> Elem (prime_h e, Glob)
  | Arith (a, Glob, c) -> Arith (prime_h a, Glob, c)
  | Access (a, x, Glob) -> Access (prime_h a, prime_h x, Glob)
  | Access (a, x, sx) -> Access (prime_h a, x, sx)
  | _ -> t

let rec prime_atom a = match a with
  | True | False -> a
  | Comp (t1, op, t2) -> Comp (prime_term t1, op, prime_term t2)
  | Ite (sa, a1, a2) -> 
    Ite (prime_satom sa, prime_atom a1, prime_atom a2)
  
and prime_satom sa =
  SAtom.fold (fun a acc -> SAtom.add (prime_atom a) acc) sa SAtom.empty

let unprime_h h =
  let s = Hstring.view h in
  Hstring.make (String.sub s 0 (String.index s '@'))

let unprime_term t = match t with
  | Elem (e, Glob) -> Elem (unprime_h e, Glob)
  | Arith (a, Glob, c) -> Arith (unprime_h a, Glob, c)
  | Access (a, x, Glob) -> Access (unprime_h a, unprime_h x, Glob)
  | Access (a, x, sx) -> Access (unprime_h a, x, sx)
  | _ -> t


let is_prime s = String.contains s '@'

let is_prime_term = function
  | Const _ -> false 
  | Elem (s, _) | Access (s, _, _) | Arith (s, _, _) ->
      is_prime (Hstring.view s)

let rec is_prime_atom = function
  | True | False -> false
  | Comp (t1, _, t2) ->
    is_prime_term t1 || is_prime_term t2
  | Ite (sa, a1, a2) ->
    is_prime_atom a1 || is_prime_atom a2 || SAtom.exists is_prime_atom sa


let is_const = function
  | Const _ | Elem (_, (Constr | Var)) | Arith (_, (Constr | Var), _) -> true
  | _ -> false

exception Found_const of (op_comp * term)

let find_const_value g init =
  try
    SAtom.iter (function
      | Comp (g', op, t') when compare_term g g' = 0 ->
	raise (Found_const (op, t'))
      | Comp (t', op, g') when compare_term g g' = 0 ->
	raise (Found_const (op, t'))
      | _ -> ()) init;
    raise Not_found
  with Found_const c -> c


let elim_prime_atom init = function
  | True -> None 
  | False -> Some False
  | Comp (t1, Eq, t2) as a ->
      assert (not (is_prime_term t1));
      if not (is_prime_term t2) then Some a
      else begin
	try
	  let op, t2' = find_const_value t2 init in
	  Some (Comp (t1, op, t2'))
	with Not_found -> None
      end
  | _ -> assert false
    


let elim_prime init sa =
  let sa = 
    SAtom.fold 
      (fun a acc ->
	match elim_prime_atom init a with
	  | None -> acc
	  | Some na -> SAtom.add na acc)
      sa SAtom.empty
  in
  assert (not (SAtom.exists is_prime_atom sa));
  sa


let apply_assigns assigns sigma =
  List.fold_left 
    (fun (nsa, terms) (h, t) ->
      let nt = Elem (h, Glob) in
      let t = subst_term sigma t in
      SAtom.add (Comp (nt, Eq, prime_term t)) nsa,
      STerm.add nt terms)
    (SAtom.empty, STerm.empty) assigns


let add_update (sa, st) {up_arr=a; up_arg=j; up_swts=swts} procs sigma =
  let rec sd acc = function
    | [] -> assert false
    | [d] -> List.rev acc, d
    | s::r -> sd (s::acc) r in
  let swts, (d, t) = sd [] swts in
  (* assert (d = SAtom.singleton True); *)
  let at = Access (a, j, Var) in
  let t = subst_term sigma (prime_term t) in
  let default = Comp (at, Eq, t) in
  let ites = 
    List.fold_left (fun ites (sa, t) ->
      let sa = subst_atoms sigma (prime_satom sa) in
      let t = subst_term sigma (prime_term t) in
      Ite (sa, Comp (at, Eq, t), ites)) default swts
  in
  List.fold_left (fun (sa, st) i ->
    SAtom.add (subst_atom [j, i] ites) sa,
    STerm.add (Access (a, i, Var)) st
  ) (sa, st) procs

let apply_updates upds procs sigma =
  List.fold_left 
    (fun acc up -> add_update acc up procs sigma)
    (SAtom.empty, STerm.empty) upds

let preserve_terms upd_terms sa =
  let vsa = STerm.fold 
    (fun t acc -> STerm.add t acc) (variables_of sa) STerm.empty
  in
  let unc = STerm.diff vsa upd_terms in
  STerm.fold (fun t acc ->
    SAtom.add (Comp (t, Eq, prime_term t)) acc)
    unc SAtom.empty


let uguard_dnf sigma args tr_args = function
  | [] -> []
  | [j, dnf] ->
      let uargs = List.filter (fun a -> not (H.list_mem a tr_args)) args in
      List.map (fun i ->
	List.map (fun sa ->
	  prime_satom (subst_atoms ((j, i)::sigma) sa)) dnf) uargs
  | _ -> assert false




let possible_guard args sigma init reqs =
  let reqs = subst_atoms sigma reqs in
  not (inconsistent_2cubes init reqs) &&
    try Prover.check_guard args init reqs; true
    with Smt.Unsat _ -> false


let post ({ t_unsafe = _, init } as s_init) procs { tr_args = tr_args; 
						    tr_reqs = reqs; 
						    tr_assigns = assigns; 
						    tr_upds = upds; 
						    tr_nondets = nondets } =
  assert (List.length procs >= List.length tr_args);
  let sigma = build_subst tr_args procs in
  if possible_guard procs sigma init reqs then
    let assi, assi_terms = apply_assigns assigns sigma in
    let upd, upd_terms = apply_updates upds procs sigma in
    let unchaged = preserve_terms (STerm.union assi_terms upd_terms) init in
    let sa = simplification_atoms SAtom.empty
      (SAtom.union unchaged (SAtom.union assi upd)) in
    let sa = elim_prime (prime_satom init) sa in
    let sa, (nargs, _) = proper_cube sa in
    let ar =  ArrayAtom.of_satom sa in
    let s = { s_init with
              t_unsafe = nargs, sa;
              t_arru = ar;
	      t_alpha = ArrayAtom.alpha ar nargs; } 
    in
    Some s
  else None

let rec forward visited procs trs = function
  | [] -> visited
  | init :: to_do ->
    let new_td = List.fold_left (fun new_td tr -> 
      match post init procs tr with
	| None -> new_td
	| Some s -> 
	  if fixpoint ~invariants:[] ~visited s then new_td
	  else s :: new_td) [] trs in
    forward (init :: visited) procs trs (to_do @ new_td)
    
let mkinit arg init args =
  match arg with
    | None -> init
    | Some z ->
	let sa, cst = SAtom.partition (has_var z) init in
	List.fold_left (fun acc h ->
	  SAtom.union (subst_atoms [z, h] sa) acc) cst args

let mkinit_s procs ({t_init = ia, init} as s) =
  let sa, (nargs, _) = proper_cube (mkinit ia init procs) in
  let ar = ArrayAtom.of_satom sa in
  { s with
    t_unsafe = nargs, sa;
    t_arru = ar;
    t_alpha = ArrayAtom.alpha ar nargs;
  }

let search procs init = forward [] procs init.t_trans [mkinit_s procs init]

let search_nb n =
  let rp, _ = 
    List.fold_left (fun (acc, n) v ->
      if n > 0 then v :: acc, n - 1
      else acc, n) ([], n) proc_vars in
  let procs = List.rev rp in
  search procs






(*
let post s sa tr args procs =
  let sigma = List.combine tr.tr_args args in
  let guard = prime_satom (subst_atoms sigma tr.tr_reqs) in
  let udnf = uguard_dnf sigma procs args tr.tr_ureq in
  begin 
    try
      Prover.check_guard procs sa guard udnf
    with
      | Smt.Sat | Smt.IDontknow -> ()
      | Smt.Unsat uc -> raise (UnsatGuard (level, s, uc))
  end;
  let assi, assi_terms = apply_assigns tr.tr_assigns sigma in
  let upd, upd_terms = apply_updates tr.tr_upds procs sigma in
  let unchaged = preserve_terms (STerm.union assi_terms upd_terms) sa in
  simplification_atoms SAtom.empty
    (SAtom.union unchaged (SAtom.union assi (SAtom.union upd sa)))
*)



(* let find_value g init = *)
(*   let t = ref (Eq, g) in *)
(*   Array.iter (function  *)
(*     | Comp (g', op, t') | Comp (t', op, g') when compare_term g g' = 0 -> *)
(*       t := op, t' *)
(*     | _ -> ()) init; *)
(*   !t *)
    

(* let apply_assigns init a assigns = *)
(*   let na = Array.copy a in *)
(*   Array.iteri (fun i -> function *)
(*     | Comp (Elem (g, Glob), _, _) -> *)
(*       (try  *)
(* 	 let t1 = subst_term subst (Hstring.list_assoc g assigns) in *)
(* 	 let op, t' = find_value t1 init in *)
(* 	 na.(i) <- Comp (t1, op, t') *)
(*        with Not_found -> ()) *)
(*     | _ -> ()) a; *)
(*   na *)


(* let apply_upds init a upds = *)
(*   let na = Array.copy a in *)
(*   List.iter (fun {up_arr = a; up_arg=i; } *)
(*   Array.iteri (fun i -> function *)
(*     | Comp (Elem (g, Glob), Eq, t2) -> *)
(*       (try  *)
(* 	 let t1 = subst_term subst (Hstring.list_assoc g assigns) in *)
(* 	 let op, t' = find_value t1 init in *)
(* 	 na.(i) <- Comp (t1, op, t') *)
(*        with Not_found -> ()) *)
(*     | _ -> ()) a; *)
(*   na *)

(* let rec post visited init args { tr_args = tr_args;  *)
(* 				 tr_reqs = reqs;  *)
(* 				 tr_assigns = assigns;  *)
(* 				 tr_upds = upds;  *)
(* 				 tr_nondets = nondets } = *)
(*   assert (List.length args >= List.length tr_args); *)
(*   let subst = build_subst tr_args args in *)
(*   if possible_guard args subst init reqs then *)
    
(*   else None *)

