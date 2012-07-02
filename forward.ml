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
	  if is_const t' then raise (Found_const (op, t'))
      | Comp (t', op, g') when compare_term g g' = 0 ->
	  if is_const t' then raise (Found_const (op, t'))
      | _ -> ()) init;
    raise Not_found
  with Found_const c -> c


let rec elim_prime_atom init = function
  | True -> None 
  | False -> Some False
  | Comp (t1, Eq, t2) as a ->
      let t1, t2 = 
	if is_prime_term t1 && not (is_prime_term t2) then t2, t1
	else t1, t2 in
      assert (not (is_prime_term t1));
      if not (is_prime_term t2) then Some (Comp (t1, Eq, t2))
      else begin
	try
	  let op, t2' = find_const_value t2 init in
	  Some (Comp (t1, op, t2'))
	with Not_found -> None
      end
  | Ite (sa, a1, a2) ->
      let a1 = match elim_prime_atom init a1 with
	| None -> True
	| Some a1 -> a1 in
      let a2 = match elim_prime_atom init a2 with
	| None -> True
	| Some a2 -> a2 in
      Some (Ite (elim_prime init sa, a1, a2))
  | _ -> assert false

and elim_prime init sa =
  (* eprintf "elim prime : %a@." Pretty.print_cube sa; *)
  let sa = 
    SAtom.fold 
      (fun a acc ->
	match elim_prime_atom init a with
	  | None -> acc
	  | Some na -> SAtom.add na acc)
      sa SAtom.empty
  in
  assert (not (SAtom.exists is_prime_atom sa));
  (* eprintf "   == %a@." Pretty.print_cube sa; *)
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
    | [d] -> acc, d
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
	List.map (fun sa -> subst_atoms ((j, i)::sigma) sa) dnf) uargs
  | _ -> assert false


let possible_init args init reqs =
  (** Very incomplete semantic test **)
  not (inconsistent_2cubes init reqs) (*  && *)
    (* try Prover.check_guard args init reqs; true *)
    (* with Smt.Unsat _ -> false *)

let possible_guard args all_args tr_args sigma init reqs ureqs =
  let reqs = subst_atoms sigma reqs in
  possible_init args init reqs &&
    let t_args_ef = List.map (svar sigma) tr_args in
    let udnfs = uguard_dnf sigma all_args t_args_ef ureqs in
    List.for_all (List.exists (possible_init all_args init)) udnfs


let missing_args procs tr_args =
  let rec aux p t pv =
  match p, t, pv with
    | [], _::_, _ -> List.rev (snd (List.split (build_subst t pv)))
    | _::rp, _::rt, _::rpv -> aux rp rt rpv
    | _, [], _ -> []
    | _, _::_, [] -> assert false
  in
  aux procs tr_args proc_vars

let term_contains_arg z = function
  | Elem (x, Var) | Access (_, x, Var) | Arith (x, Var, _) 
      when Hstring.equal x z -> true
  | _ -> false

let rec atom_contains_arg z = function
  | True | False -> false
  | Comp (t1, _, t2) -> term_contains_arg z t1 || term_contains_arg z t2
  | Ite (sa, a1, a2) -> atom_contains_arg z a1 || atom_contains_arg z a2 ||
                        SAtom.exists (atom_contains_arg z) sa


let abstract_others sa others =
  SAtom.filter (fun a ->
    not (List.exists (fun z -> atom_contains_arg z a) others)) sa

let post ({ t_unsafe = all_procs, init } as s_init) procs { tr_args = tr_args; 
						    tr_reqs = reqs;
						    tr_ureq = ureqs;
						    tr_assigns = assigns; 
						    tr_upds = upds; 
						    tr_nondets = nondets } =
  let others = missing_args procs tr_args in
  let d = all_permutations tr_args (procs@others) in
  List.fold_left (fun acc sigma ->
  (* let sigma = build_subst tr_args procs in *)
    if possible_guard procs all_procs tr_args sigma init reqs ureqs then
      let assi, assi_terms = apply_assigns assigns sigma in
      let upd, upd_terms = apply_updates upds procs sigma in
      let unchanged = preserve_terms (STerm.union assi_terms upd_terms) init in
      let sa = simplification_atoms SAtom.empty
	(SAtom.union unchanged (SAtom.union assi upd)) in
      let sa = abstract_others sa others in
      let sa = elim_prime (prime_satom init) sa in
      let sa = simplification_atoms SAtom.empty sa in
      let sa, (nargs, _) = proper_cube sa in
      let ar =  ArrayAtom.of_satom sa in
      let s = { s_init with
        t_unsafe = nargs, sa;
        t_arru = ar;
	t_alpha = ArrayAtom.alpha ar nargs; } 
      in
      s::acc
    else acc
  ) [] d

let cpt_f = ref 0

module HA = Hashtbl.Make (struct include ArrayAtom let hash = Hashtbl.hash end)
let h_visited = HA.create 1001

let rec forward visited procs trs = function
  | [] -> visited
  | init :: to_do ->
    (* if fixpoint ~invariants:[] ~visited init then *)
    (* if easy_fixpoint init visited then *)
    (** Very incomplete hash test **)
    if HA.mem h_visited init.t_arru then
      forward visited procs trs to_do
    else
    let new_td =
      List.fold_left (fun new_td tr ->
	List.fold_left (fun new_td s ->
	  (* if fixpoint ~invariants:[] ~visited s then new_td *)
	  (* else *) (s :: new_td)
	) new_td (post init procs tr)
      ) [] trs
    in
    incr cpt_f; 
    eprintf "%d\n" !cpt_f; 
    if !cpt_f mod 1000 = 0 then pp_print_flush err_formatter ();
    HA.add h_visited init.t_arru ();
    forward (init :: visited) procs trs (List.rev_append new_td to_do)(* (to_do @ (List.rev new_td)) *)
    
(* let mkinit_multi args init args = *)
(*   match args with *)
(*     | [] -> init *)
(*     | _ -> *)
(* 	let sa, cst = SAtom.partition (fun a ->  *)
(* 	  List.exists (fun z -> has_var z a) args) init in *)
(* 	List.fold_left (fun acc h -> *)
(* 	  SAtom.union (subst_atoms [z, h] sa) acc) cst args *)

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

let mkforward_s s =
  List.map (fun fo ->
    let _,_,sa = fo in
    let sa, (nargs, _) = proper_cube sa in
    let ar = ArrayAtom.of_satom sa in
    { s with
      t_unsafe = nargs, sa;
      t_arru = ar;
      t_alpha = ArrayAtom.alpha ar nargs;
    })
    s.t_forward

let search procs init = forward [] procs init.t_trans [mkinit_s procs init]

let search_nb n =
  let rp, _ = 
    List.fold_left (fun (acc, n) v ->
      if n > 0 then v :: acc, n - 1
      else acc, n) ([], n) proc_vars in
  let procs = List.rev rp in
  search procs


let search_only s =
  let ex_args = 
    match s.t_forward with (_, args, _) :: _ -> args | _ -> assert false in
  forward [] ex_args s.t_trans (mkforward_s s)
