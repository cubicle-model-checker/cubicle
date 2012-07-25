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

let rec prime_term t = match t with
  | Elem (e, Glob) -> Elem (prime_h e, Glob)
  | Arith (x, c) -> Arith (prime_term x, c)
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

let rec unprime_term t = match t with
  | Elem (e, Glob) -> Elem (unprime_h e, Glob)
  | Arith (x, c) -> Arith (unprime_term x, c)
  | Access (a, x, Glob) -> Access (unprime_h a, unprime_h x, Glob)
  | Access (a, x, sx) -> Access (unprime_h a, x, sx)
  | _ -> t


let is_prime s = String.contains s '@'

let rec is_prime_term = function
  | Const _ -> false 
  | Elem (s, _) | Access (s, _, _) ->
      is_prime (Hstring.view s)
  | Arith (x, _) -> is_prime_term x

let rec is_prime_atom = function
  | True | False -> false
  | Comp (t1, _, t2) ->
    is_prime_term t1 || is_prime_term t2
  | Ite (sa, a1, a2) ->
    is_prime_atom a1 || is_prime_atom a2 || SAtom.exists is_prime_atom sa


let rec is_const = function
  | Const _ | Elem (_, (Constr | Var)) -> true
  | Arith (x, _) -> is_const x 
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

let find_const_value g init = match g with
  | Arith (g', c) -> 
      begin
	let op, t = find_const_value g' init in
	match t with
	  | Const c' -> op, Const (add_constants c c')
	  | _ -> assert false
      end
  | _ -> find_const_value g init


let rec elim_prime_atom init = function
  | True -> None 
  | False -> Some False
  | Comp (t1, Eq, t2)  ->
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
  not (inconsistent_2cubes init reqs) (* && *)
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

let rec term_contains_arg z = function
  | Elem (x, Var) | Access (_, x, Var)
      when Hstring.equal x z -> true
  | Arith (x, _) -> term_contains_arg z x
  | _ -> false

let rec atom_contains_arg z = function
  | True | False -> false
  | Comp (t1, _, t2) -> term_contains_arg z t1 || term_contains_arg z t2
  | Ite (sa, a1, a2) -> atom_contains_arg z a1 || atom_contains_arg z a2 ||
                        SAtom.exists (atom_contains_arg z) sa


let abstract_others sa others =
  SAtom.filter (fun a ->
    not (List.exists (fun z -> atom_contains_arg z a) others)) sa

let post init all_procs procs { tr_args = tr_args; 
				   tr_reqs = reqs; 
				   tr_name = name;
				   tr_ureq = ureqs;
				   tr_assigns = assigns; 
				   tr_upds = upds; 
				   tr_nondets = nondets } =
  let others = missing_args procs tr_args in
  let d = all_permutations tr_args (procs@others) in
  (* do it even if no arguments *)
  let d = if d = [] then [[]] else d in
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
      (sa, nargs) :: acc
      (* let ar =  ArrayAtom.of_satom sa in *)
      (* let s = { s_init with *)
      (* 	(\* t_from =  *\) *)
      (* 	(\*   (name, (List.map (svar sigma) tr_args),s_init) :: s_init.t_from; *\) *)
      (*   t_unsafe = nargs, sa; *)
      (*   t_arru = ar; *)
      (* 	t_alpha = ArrayAtom.alpha ar nargs; }  *)
      (* in *)
      (* s::acc *)
    else acc
  ) [] d


(* module HA = Hashtbl.Make (ArrayAtom) *)

module HSA : Hashtbl.S with type key = SAtom.t = Hashtbl.Make (SAtom)


module HI = Hashtbl.Make 
  (struct 
  type t = int 
  let equal = (=) 
  let hash x = x end)


(* let _ = Ocamlviz.init () *)

(* let h_visited = Ocamlviz.Hashtable.observe ~period:100 "h_visited" *)
(*   (HA.create 200_029) *)

(* let h_visited = HSA.create 200_029 *)


let visited_from_h s h = HSA.fold (fun sa _ acc ->
  let sa, (nargs, _) = proper_cube sa in
  let ar = ArrayAtom.of_satom sa in
  { s with 
    t_unsafe = nargs, sa;
    t_arru = ar;
    t_alpha = ArrayAtom.alpha ar nargs } :: acc) h []


let forward s procs trs l =
  let h_visited = HSA.create 200_029 in
  let cpt_f = ref 0 in
  let rec forward_rec s procs trs = function
    | [] -> eprintf "Total forward nodes : %d@." !cpt_f
    | (sa, args) :: to_do ->
    (* if ArrayAtom.subset s.t_arru init.t_arru then begin *)
    (*   eprintf "\nUnsafe trace: @[%a@]@."  Pretty.print_verbose_node init; *)
    (*   raise (Search.Unsafe init) *)
    (* end; *)
      if false && !cpt_f > 400_000 then ()
      else (
    (* if fixpoint ~invariants:[] ~visited init then *)
    (* if easy_fixpoint init visited then *)
    (** Very incomplete hash test **)
	if HSA.mem h_visited sa then
	  forward_rec s procs trs to_do
	else
	  let new_td =
	    List.fold_left (fun new_td tr ->
	      List.fold_left (fun new_td s ->
	  (* if fixpoint ~invariants:[] ~visited s then new_td *)
	  (* else *) (s :: new_td)
	      ) new_td (post sa args procs tr)
	    ) [] trs
	  in
	  incr cpt_f;
	  if debug then eprintf "%d : %a@." !cpt_f Pretty.print_cube sa
	  else if !cpt_f mod 1000 = 0 then eprintf "%d@." !cpt_f;
	  HSA.add h_visited sa ();
	  forward_rec s procs trs (List.rev_append new_td to_do)
      )
  in
  forward_rec s procs trs l;
  h_visited



module MA = Map.Make (Atom)

let add_compagnions_from_node sa =
  SAtom.fold (fun a mc ->
    let comps = SAtom.remove a sa in
    let old_comps = try MA.find a mc with Not_found -> SAtom.empty in
    MA.add a (SAtom.union comps old_comps) mc) sa


let stateless_forward s procs trs l =
  let h_visited = HI.create 200_029 in
  let cpt_f = ref 0 in
  let rec forward_rec s procs trs mc = function
    | [] -> eprintf "Total forward nodes : %d@." !cpt_f; mc
    | (sa, args) :: to_do ->
      let hsa = SAtom.hash sa in
      if HI.mem h_visited hsa then
	forward_rec s procs trs mc to_do
      else
	let new_td =
	  List.fold_left (fun new_td tr ->
	    List.fold_left (fun new_td s ->
	  (* if fixpoint ~invariants:[] ~visited s then new_td *)
	  (* else *) (s :: new_td)
	    ) new_td (post sa args procs tr)
	  ) [] trs
	in
	incr cpt_f;
	
	if debug then eprintf "%d : %a@." !cpt_f Pretty.print_cube sa
	else if !cpt_f mod 1000 = 0 then eprintf "%d@." !cpt_f;
	HI.add h_visited hsa ();
	let mc = add_compagnions_from_node sa mc in
	forward_rec s procs trs mc (List.rev_append new_td to_do)
  in
  forward_rec s procs trs MA.empty l
  
  


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

let mkinit_s procs ({t_init = ia, init}) =
  let sa, (nargs, _) = proper_cube (mkinit ia init procs) in
  sa, nargs
  (* let ar = ArrayAtom.of_satom sa in *)
  (* { s with *)
  (*   t_unsafe = nargs, sa; *)
  (*   t_arru = ar; *)
  (*   t_alpha = ArrayAtom.alpha ar nargs; *)
  (* } *)

let mkforward_s s =
  List.map (fun fo ->
    let _,_,sa = fo in
    let sa, (nargs, _) = proper_cube sa in
    sa, nargs
    (* let ar = ArrayAtom.of_satom sa in *)
    (* { s with *)
    (*   t_unsafe = nargs, sa; *)
    (*   t_arru = ar; *)
    (*   t_alpha = ArrayAtom.alpha ar nargs; *)
    (* } *)
  ) s.t_forward

let search procs init = forward init procs init.t_trans [mkinit_s procs init]

let search_stateless procs init = 
  stateless_forward init procs init.t_trans [mkinit_s procs init]

let search_nb n =
  let rp, _ = 
    List.fold_left (fun (acc, n) v ->
      if n > 0 then v :: acc, n - 1
      else acc, n) ([], n) proc_vars in
  let procs = List.rev rp in
  search procs


let search_stateless_nb n =
  let rp, _ = 
    List.fold_left (fun (acc, n) v ->
      if n > 0 then v :: acc, n - 1
      else acc, n) ([], n) proc_vars in
  let procs = List.rev rp in
  search_stateless procs


let search_only s =
  let ex_args = 
    match s.t_forward with (_, args, _) :: _ -> args | _ -> assert false in
  forward s ex_args s.t_trans (mkforward_s s)






(*********************************)
(* Extract candidates from trace *)
(*********************************)

module HA = Hashtbl.Make (struct 
  include Atom 
  let equal a b = compare a b = 0
  let hash = Hashtbl.hash end)

module MT = Map.Make (struct type t = term let compare = compare_term end)


let all_litterals h = HSA.fold (fun sa _ acc ->
  SAtom.union sa acc) h SAtom.empty

let compagnions_from_trace forward_nodes =
  let lits = all_litterals forward_nodes in
  SAtom.fold (fun a acc ->
    let compagnions =
      HSA.fold (fun sa _ acc ->
	if SAtom.mem a sa then
	  SAtom.union (SAtom.remove a sa) acc
	else acc)
	forward_nodes SAtom.empty
    in
    MA.add a compagnions acc) lits MA.empty



let compagnions_values compagnions =
  SAtom.fold (fun c (acc, compagnions) -> 
    match c with
      | Comp (Elem (x, Constr), Eq, t1)
      | Comp (t1, Eq, Elem (x, Constr)) ->
	let vals = try MT.find t1 acc with Not_found -> H.HSet.empty in
	MT.add t1 (H.HSet.add x vals) acc, SAtom.remove c compagnions
      (* heuristic: remove proc variables *)
      | Comp (Elem (_, Var), _, _)
      | Comp (_, _, Elem (_, Var)) ->
      	acc, SAtom.remove c compagnions
      | _ -> acc, compagnions)
    compagnions (MT.empty, compagnions)


let get_variants x =
  (* add missing constructors for bool *)
  if Hstring.equal (snd (Smt.Typing.find x)) Smt.Typing.type_bool then
    H.HSet.add htrue (H.HSet.singleton hfalse)
  else Smt.Typing.Variant.get_variants x


let candidates_from_compagnions a compagnions acc =
  let singl_a = SAtom.singleton a in
  let mt, remaining = compagnions_values compagnions in
  let acc = 
    SAtom.fold (fun c acc -> SAtom.add (Atom.neg c) singl_a :: acc)
    remaining acc
  in
  MT.fold (fun c vals acc -> match c with
    | Elem (x, _) | Access (x, _, _) ->
      begin
	match H.HSet.elements vals with
	  | [v] when Hstring.equal v htrue ->
	    SAtom.add (Comp (c, Eq, (Elem (hfalse, Constr)))) singl_a :: acc	
	  | [v] when Hstring.equal v hfalse ->
	    SAtom.add (Comp (c, Eq, (Elem (htrue, Constr)))) singl_a :: acc
	  | [v] -> SAtom.add (Comp (c, Neq, (Elem (v, Constr)))) singl_a :: acc
	  | vs ->
	    try
	      let dif = H.HSet.diff (get_variants x) vals in
	      match H.HSet.elements dif with
		| [] -> acc
		| [cs] -> 
		  SAtom.add (Comp (c, Eq, (Elem (cs, Constr)))) singl_a :: acc
		| _ -> raise Not_found
	    with Not_found ->
	      let sa = List.fold_left (fun sa v ->
		SAtom.add (Comp (c, Neq, (Elem (v, Constr)))) sa)
		singl_a vs in
	      sa :: acc
      end
    | _ -> assert false)
    mt acc


let useless_candidate sa =
  SAtom.exists (function
    (* heuristic: remove proc variables *)
    | Comp (Elem (_, Var), _, _)
    | Comp (_, _, Elem (_, Var)) -> true
    | _ -> false) sa
  (* || List.length (args_of_atoms sa) > 1 *)




let extract_candidates_from_compagnons comps s =
  let cpt = ref (-1) in
  MA.iter (fun a compagnions ->
    eprintf "compagnons %a : %a@." 
      Pretty.print_atom a Pretty.print_cube compagnions) comps;
  let sas = MA.fold candidates_from_compagnions comps [] in
  let sas = List.rev sas in
  Gc.full_major ();
  List.fold_left (fun acc sa ->
    if useless_candidate sa then acc
    else
      let sa', (args, _) = proper_cube sa in
      let ar' = ArrayAtom.of_satom sa' in
      let s' = 
	{ s with
	  t_from = [];
	  t_unsafe = args, sa';
	  t_arru = ar';
	  t_alpha = ArrayAtom.alpha ar' args;
	  t_deleted = false;
	  t_nb = !cpt;
	  t_nb_father = -1 } in
      if List.exists (fun s -> ArrayAtom.equal s.t_arru s'.t_arru) acc then acc
      else (decr cpt; s' :: acc)) [] sas

let extract_candidates_from_trace forward_nodes s =
  let comps = compagnions_from_trace forward_nodes in
  HSA.clear forward_nodes;
  extract_candidates_from_compagnons comps s



let select_relevant_candidates {t_unsafe = _, sa} =
  List.filter (fun {t_unsafe = _, ca} ->
    not (SAtom.is_empty (SAtom.inter ca sa))
  )

  

(*----------------------------------------------------------------*)

