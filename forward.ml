(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2013                          *)
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
open Ast
open Atom
open Cube

module H = Hstring

type inst_trans =
    {
      i_reqs : SAtom.t;
      i_udnfs : SAtom.t list list;
      i_actions : SAtom.t;
      i_touched_terms : STerm.t;
    }

let prime_h h =
  Hstring.make ((Hstring.view h)^"@0")

let rec prime_term t = match t with
  | Elem (e, Glob) -> Elem (prime_h e, Glob)
  | Arith (x, c) -> Arith (prime_term x, c)
  (* | Access (a, x, Glob) -> Access (prime_h a, prime_h x, Glob) *)
  | Access (a, lx) -> Access (prime_h a, lx)
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
  (* | Access (a, x, Glob) -> Access (unprime_h a, unprime_h x, Glob) *)
  | Access (a, lx) -> Access (unprime_h a, lx)
  | _ -> t


let is_prime s = String.contains s '@'

let rec is_prime_term = function
  | Const _ -> false 
  | Elem (s, _) | Access (s, _) ->
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
	with Not_found -> None (* Some (Comp (t1, Eq, t2)) *)
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
  (* eprintf "elim prime : %a@." Pretty.print_cube (SAtom.union init sa); *)
  let sa = 
    SAtom.fold 
      (fun a acc ->
	match elim_prime_atom init a with
	  | None -> acc
	  | Some na -> SAtom.add na acc)
      sa SAtom.empty
  in
  (* assert (not (SAtom.exists is_prime_atom sa)); *)
  (* eprintf "   == %a@." Pretty.print_cube sa; *)
  sa


exception Found_eq of term * term * Atom.t
exception Found_neq of term * term * Atom.t

let rec apply_subst_terms_atom t t' a = match a with
  | True | False -> a
  | Comp (t1, op, t2) ->
      if compare_term t t1 = 0 then Comp (t', op, t2)
      else if compare_term t t2 = 0 then Comp (t1, op, t')
      else a
  | Ite (sa, a1, a2) -> Ite (apply_subst_terms_atoms t t' sa, 
			     apply_subst_terms_atom t t' a1,
			     apply_subst_terms_atom t t' a2)

and apply_subst_terms_atoms t t' sa =
  SAtom.fold 
    (fun a acc -> SAtom.add (apply_subst_terms_atom t t' a) acc)
    sa SAtom.empty


let elim_primed_term t sa =		     
  try
    SAtom.iter (fun a -> match a with
      | Comp (t1, Eq, t2) -> 
	if compare_term t t1 = 0 && is_const t2 then raise (Found_eq (t1, t2, a));
	if compare_term t t2 = 0 && is_const t1 then raise (Found_eq (t2, t1, a))
      | _ -> ()) sa;
    SAtom.iter (fun a -> match a with
      | Comp (t1, Eq, t2) -> 
	if compare_term t t1 = 0 then raise (Found_eq (t1, t2, a));
	if compare_term t t2 = 0 then raise (Found_eq (t2, t1, a))
      | _ -> ()) sa;
    SAtom.iter (fun a -> match a with
      | Comp (t1, Neq, t2) -> 
	if compare_term t t1 = 0 then raise (Found_neq (t1, t2, a));
	if compare_term t t2 = 0 then raise (Found_neq (t2, t1, a))
      | _ -> ()) sa;
    sa
  with
    | Found_eq (t, t', a) -> 
        let rsa = SAtom.remove a sa in
	apply_subst_terms_atoms t t' rsa

    | Found_neq (t, t', a) -> (* TODO *) sa

type primed_value = Const_Eq | Var_Eq | Var_Neq

let elim_primed_term t sa =
  let r = SAtom.fold (fun a res -> match a with
    | Comp (t1, Eq, t2) ->
      begin
	if compare_term t t1 = 0 then
	  match res with
	    | None -> 
	        Some (Eq, t1, t2, a)
	    | Some (Eq, _, t', _) when compare_term t2 t' < 0 ->
	        Some (Eq, t1, t2, a)
	    | _ -> res	    
      else if compare_term t t2 = 0 then
	  match res with
	    | None ->
	        Some (Eq, t2, t1, a)
	    | Some (Eq, _, t', _) when compare_term t1 t' < 0 ->
	        Some (Eq, t2, t1, a)
	    | _ -> res
      else res
      end
    | Comp (t1, Neq, t2) -> 
      begin
	if compare_term t t1 = 0 then
	  match res with
	    | None -> Some (Neq, t1, t2, a)
	    | _ -> res
	else if compare_term t t2 = 0 then
	  match res with
	    | None -> Some (Neq, t2, t1, a)
	    | _ -> res
	else res
      end
    | Comp (t1, op, t2) ->
        (* TODO: perform fourier motzkin instead *)
        if compare_term t t1 = 0 || compare_term t t2 = 0 then
          match res with
	    | None -> Some (op, t1, t2, a) 
            | _ -> res
        else res
    | _ -> res) sa None
  in
  match r with
    | None -> sa
    | Some (Eq, t, t', a) ->
        let rsa = SAtom.remove a sa in
	apply_subst_terms_atoms t t' rsa
    | Some (_, _, _, a) -> SAtom.remove a sa

let primed_terms_of_atom a =
  let rec primed_terms_of_atom a acc = match a with
    | True | False -> acc
    | Comp (t1, _, t2) ->
      let acc = if is_prime_term t1 then STerm.add t1 acc else acc in
      if is_prime_term t2 then STerm.add t2 acc else acc
    | Ite (sa, a1, a2) -> 
      primed_terms_of_atom a1 
	(primed_terms_of_atom a2 
	   (SAtom.fold primed_terms_of_atom sa acc))
  in
  primed_terms_of_atom a STerm.empty

exception First_primed_atom of Atom.t * STerm.t

let first_primed_atom sa =
  try
    SAtom.iter (fun a -> 
      let pts = primed_terms_of_atom a in
      if not (STerm.is_empty pts) then raise (First_primed_atom (a, pts))
    ) sa;
    raise Not_found
  with First_primed_atom (a, pts) -> a, pts

let rec elim_prime2 sa =
  let sa =
    try
      let a, pts = first_primed_atom sa in
      let sa = STerm.fold elim_primed_term pts sa in
      elim_prime2 sa
    with Not_found -> sa
  in
  (* assert (not (SAtom.exists is_prime_atom sa)); *)
  sa

(* let elim_prime2 sa = *)
(*   eprintf "elim prime 2 : %a@." Pretty.print_cube sa; *)
(*   let sa = elim_prime2 sa in *)
(*   eprintf "   == %a@." Pretty.print_cube sa; *)
(*   sa *)

let rec elim_prime3 init sa =
  let pts = 
    SAtom.fold (fun a acc -> STerm.union (primed_terms_of_atom a) acc )
      sa STerm.empty in
  let sa =
    SAtom.fold (fun a sa -> match a with
      | Comp (t1, op, t2) ->
	if STerm.mem t1 pts || STerm.mem t2 pts then SAtom.add a sa
	else sa
      | _ -> sa) init sa
  in
  elim_prime2 sa

let gauss_elim sa =
  SAtom.fold (fun a sa -> match a with
    | Comp ((Elem(_,Glob) as t1), Eq, (Elem(_,Glob) as t2)) ->
      let rsa = SAtom.remove a sa in
      let rsa = apply_subst_terms_atoms t1 t2 rsa in
      SAtom.add a rsa
    | _ -> sa
  ) sa sa


exception Found_prime_term of term

let choose_prime_term sa =
  try
    SAtom.iter (function
      | Comp (t1, eq, t2) ->
	if is_prime_term t1 then raise (Found_prime_term t1);
	if is_prime_term t2 then raise (Found_prime_term t2)
      | _ -> ()) sa;
    raise Not_found
  with Found_prime_term t -> t


let split_prime_atoms t sa =
  SAtom.fold (fun a (yes, no) -> match a with
    | Comp (t1, Eq, t2) when compare_term t t1 = 0 || compare_term t t2 = 0 ->
        SAtom.add a yes, no
    | _ -> yes, SAtom.add a no) sa (SAtom.empty, SAtom.empty)
    

let aux_corss t t' sa =
  SAtom.fold (fun a acc -> match a with
    | Comp (t1, Eq, t2) ->
        if compare_term t t1 = 0 then SAtom.add (Comp (t', Eq, t2)) acc
	else if compare_term t t2 = 0 then SAtom.add (Comp (t', Eq, t1)) acc
	else assert false
    | _ -> assert false) sa SAtom.empty
      

let cross t sa =
  SAtom.fold (fun a acc -> match a with
    | Comp (t1, Eq, t2) ->
        let t' = if compare_term t t1 = 0 then t2 else t1 in
        SAtom.union (aux_corss t t' (SAtom.remove a sa)) acc
    | _ -> assert false
  ) sa SAtom.empty


let rec gauss_prime_elim sa =
  try
    let t = choose_prime_term sa in
    let yes, no = split_prime_atoms t sa in
    let sa = SAtom.union (cross t yes) no in
    gauss_prime_elim sa
  with Not_found -> sa

(* let gauss_prime_elim sa = *)
(*   eprintf "gauss elim prime : %a@." Pretty.print_cube sa; *)
(*   let sa = gauss_prime_elim sa in *)
(*   eprintf "   == %a@." Pretty.print_cube sa; *)
(*   sa *)


module MH = Map.Make (Hstring)


let rec type_of_term = function
  | Const m ->
      MConst.fold (fun c _ _ -> match c with
	| ConstReal _ -> Smt.Type.type_real
	| ConstInt _ -> Smt.Type.type_int
	| ConstName x -> snd (Smt.Symbol.type_of (unprime_h x))
      ) m Smt.Type.type_int
  | Elem (x, _) | Access (x, _) -> 
      let x = if is_prime (Hstring.view x) then unprime_h x else x in
      snd (Smt.Symbol.type_of x)
  | Arith (t, _) -> type_of_term t

let rec type_of_atom = function
  | True | False -> None
  | Comp (t, _, _) -> Some (type_of_term t)
  | Ite (_, a1, a2) -> 
      let ty = type_of_atom a1 in if ty = None then type_of_atom a2 else ty

let partition_by_type sa =
  let mtype, other =
    SAtom.fold (fun a (mtype, other) ->
      match type_of_atom a with
	| None -> mtype, SAtom.add a other
	| Some ty ->
	  try
	    let sty = try MH.find ty mtype with Not_found -> SAtom.empty in
	    MH.add ty (SAtom.add a sty) mtype, other
	  with Not_found -> mtype, SAtom.add a other
    ) sa (MH.empty, SAtom.empty)
  in mtype, other

let elim_prime_type1 sa =
  let mtype, other = partition_by_type sa in
  MH.fold (fun _ sa acc ->
    SAtom.union (elim_prime2 sa) acc)
  mtype SAtom.empty

let is_finite_type ty = 
  try ignore(Smt.Variant.get_variants ty); true
  with Not_found -> Hstring.equal ty Smt.Type.type_bool

let elim_prime_type2 init sa =
  let i_mtype, i_other = partition_by_type init in
  let mtype, other = partition_by_type sa in
  MH.fold (fun ty sa acc ->
    let si = try MH.find ty i_mtype with Not_found -> SAtom.empty in
    let s = 
      if is_finite_type ty then elim_prime si sa
      else elim_prime2 (SAtom.union si sa)
    in SAtom.union s acc
  ) mtype SAtom.empty


let wrapper_elim_prime p_init sa =
  (* let ori = SAtom.union p_init sa in *)
  (* let sa' = elim_prime p_init sa in *)
  (* let sa = elim_prime p_init sa in *)
  (* (\* NO *\) let sa = elim_prime3 p_init sa in *)
  (* (\* NO *\) let sa = elim_prime2 (SAtom.union p_init sa) in *)
  (* (\* NO *\) let sa = elim_prime_type1 (SAtom.union p_init sa) in *)
  let sa = elim_prime_type2 p_init sa in
  (* if not (SAtom.equal *)
  (* 	    (simplification_atoms SAtom.empty sa) *)
  (* 	    (simplification_atoms SAtom.empty sa')) *)
  (* then begin *)
  (*   (\* eprintf "ELIM PRIME : %a\n@." Pretty.print_cube ori; *\) *)
  (*   let s1 = simplification_atoms SAtom.empty sa' in *)
  (*   let s2 = simplification_atoms SAtom.empty sa in *)
  (*   (\* eprintf "ONE : %a\n\nDEUX : %a\n@." *\) *)
  (*   (\*   Pretty.print_cube s1 *\) *)
  (*   (\*   Pretty.print_cube s2; *\) *)
  (*   eprintf "DIFF ONE : %a\n\nDIFF DEUX : %a\n@." *)
  (*     Pretty.print_cube (SAtom.diff s1 (SAtom.inter s1 s2)) *)
  (*     Pretty.print_cube (SAtom.diff s2 (SAtom.inter s1 s2)); *)
  (* end; *)
  (* let sa = gauss_prime_elim (SAtom.union p_init sa) in *)
  simplification_atoms SAtom.empty sa


let apply_assigns assigns sigma =
  List.fold_left 
    (fun (nsa, terms) (h, t) ->
      let nt = Elem (h, Glob) in
      let t = subst_term sigma t in
      SAtom.add (Comp (nt, Eq, prime_term t)) nsa,
      STerm.add nt terms)
    (SAtom.empty, STerm.empty) assigns


let add_update (sa, st) {up_arr=a; up_arg=lj; up_swts=swts} procs sigma =
  let rec sd acc = function
    | [] -> assert false
    | [d] -> acc, d
    | s::r -> sd (s::acc) r in
  let swts, (d, t) = sd [] swts in
  (* assert (d = SAtom.singleton True); *)
  let at = Access (a, lj) in
  let t = subst_term sigma (prime_term t) in
  let default = Comp (at, Eq, t) in
  let ites = 
    List.fold_left (fun ites (sa, t) ->
      let sa = subst_atoms sigma (prime_satom sa) in
      let t = subst_term sigma (prime_term t) in
      Ite (sa, Comp (at, Eq, t), ites)) default swts
  in
  let indexes = all_arrangements (arity a) procs in
  List.fold_left (fun (sa, st) li ->
    let sigma = List.combine lj li in
    SAtom.add (subst_atom sigma ites) sa,
    STerm.add (Access (a, li)) st
  ) (sa, st) indexes

let apply_updates upds procs sigma =
  List.fold_left 
    (fun acc up -> add_update acc up procs sigma)
    (SAtom.empty, STerm.empty) upds

let preserve_terms upd_terms sa =
  let unc = STerm.diff (variables_of sa) upd_terms in
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
  not (inconsistent (SAtom.union init reqs)) (* && *)
    (* try Prover.check_guard args init reqs; true *)
    (* with Smt.Unsat _ -> false *)

let possible_guard args all_args tr_args sigma init reqs ureqs =
  let reqs = subst_atoms sigma reqs in
  possible_init args init reqs &&
    let t_args_ef = 
      List.fold_left (fun acc p -> 
	try (svar sigma p) :: acc
	with Not_found -> p :: acc) [] tr_args in
    let udnfs = uguard_dnf sigma all_args t_args_ef ureqs in
    List.for_all (List.exists (possible_init all_args init)) udnfs


let possible_inst_guard args all_args init reqs udnfs =
  possible_init args init reqs &&
    List.for_all (List.exists (possible_init all_args init)) udnfs


let missing_args procs tr_args =
  let rec aux p t pv =
  match p, t, pv with
    | [], _::_, _ ->
      let f, s = List.split (build_subst t pv) in
      List.rev f, List.rev s
      (* List.rev (snd (List.split (build_subst t pv))) *)
    | _::rp, _::rt, _::rpv -> aux rp rt rpv
    | _, [], _ -> [],[]
    | _, _::_, [] -> assert false
  in
  aux procs tr_args proc_vars

let rec term_contains_arg z = function
  | Elem (x, Var) -> Hstring.equal x z
  | Access (_, lx) -> Hstring.list_mem z lx
  | Arith (x, _) -> term_contains_arg z x
  | _ -> false

let rec atom_contains_arg z = function
  | True | False -> false
  | Comp (t1, _, t2) -> term_contains_arg z t1 || term_contains_arg z t2
  | Ite (sa, a1, a2) -> atom_contains_arg z a1 || atom_contains_arg z a2 ||
                        SAtom.exists (atom_contains_arg z) sa


let abstract_others sa others =
  (* let sa = SAtom.filter (function *)
  (*   | Comp ((Elem (x, _) | Access (x,_,_)), _, _) -> *)
  (*     let x = if is_prime (Hstring.view x) then unprime_h x else x in *)
  (*     not (Smt.Typing.has_abstract_type x) *)
  (*   | Ite _ -> false *)
  (*   | _ -> true) sa in *)
  SAtom.filter (fun a ->
    not (List.exists (fun z -> atom_contains_arg z a) others)) sa


let post init all_procs procs { tr_args = tr_args; 
				tr_reqs = reqs; 
				tr_name = name;
				tr_ureq = ureqs;
				tr_assigns = assigns; 
				tr_upds = upds; 
				tr_nondets = nondets } =
  let tr_others, others = missing_args procs tr_args in
  let d = all_permutations tr_args procs in
  (* do it even if no arguments *)
  let d = if d = [] then [[]] else d in
  let p_init = prime_satom init in
  List.fold_left (fun acc sigma ->
    if possible_guard procs all_procs tr_args sigma init reqs ureqs then
      let assi, assi_terms = apply_assigns assigns sigma in
      let upd, upd_terms = apply_updates upds all_procs sigma in
      let unchanged = preserve_terms (STerm.union assi_terms upd_terms) init in
      let sa = simplification_atoms p_init
      	(SAtom.union unchanged (SAtom.union assi upd)) in
      let sa = abstract_others sa tr_others in
      List.fold_left (fun acc sa ->
        let sa = wrapper_elim_prime p_init sa in
        (* let sa = gauss_elim sa in *)
        let sa, (nargs, _) = proper_cube sa in
        (sa, nargs) :: acc)
        acc (Cube.simplify_atoms sa)
    else acc
  ) [] d




let post_inst init all_procs procs { i_reqs = reqs;
				     i_udnfs = udnfs;
				     i_actions = actions;
				     i_touched_terms = touched_terms } =
  if possible_inst_guard procs all_procs init reqs udnfs then
    let p_init = prime_satom init in
    let unchanged = preserve_terms touched_terms init in
    let sa = simplification_atoms p_init (SAtom.union unchanged actions) in
    List.fold_left (fun acc sa ->
      try
        let sa = wrapper_elim_prime p_init sa in
        let sa, (nargs, _) = proper_cube sa in
        (sa, nargs) :: acc
      with Exit -> acc)
      [] (Cube.simplify_atoms sa) 
  else []


module HSA : Hashtbl.S with type key = SAtom.t = Hashtbl.Make (SAtom)


module HI = Hashtbl.Make 
  (struct 
  type t = int 
  let equal = (=) 
  let hash x = x end)


let visited_from_h s h = HSA.fold (fun sa _ acc ->
  let sa, (nargs, _) = proper_cube sa in
  let ar = ArrayAtom.of_satom sa in
  { s with 
    t_unsafe = nargs, sa;
    t_arru = ar;
    t_alpha = ArrayAtom.alpha ar nargs } :: acc) h []


let already_seen sa args h =
  let d = all_permutations args args in
  List.exists (fun sigma ->
    let sa = subst_atoms sigma sa in
    HSA.mem h sa) d

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
		  s :: new_td
	        ) new_td (post_inst sa args procs tr)
	      ) [] trs
	    in
	    incr cpt_f;
	    if debug then 
	      eprintf "%d : %a\n@." !cpt_f Pretty.print_cube sa
	    else if !cpt_f mod 1000 = 0 then eprintf "%d (%d)@." !cpt_f
	      (List.length to_do + List.length new_td);
	    (* HSA.add h_visited sa (); *)
	    let d = all_permutations args args in
	    List.iter 
              (fun sigma -> HSA.add h_visited (subst_atoms sigma sa) ()) d;
	    forward_rec s procs trs (List.rev_append new_td to_do)
        )
  in
  forward_rec s procs trs l;
  h_visited


let var_term_unconstrained sa t =
  SAtom.for_all (function
    | Comp (t1, _, t2) -> compare_term t t1 <> 0 && compare_term t t2 <> 0
    | _ -> true) sa

let unconstrained_terms sa = STerm.filter (var_term_unconstrained sa)

module MA = Map.Make (Atom)

let lit_abstract = function
  | Comp ((Elem (x, _) | Access (x,_)), _, _) ->
      Smt.Symbol.has_abstract_type x
  | _ -> false

let add_compagnions_from_node all_var_terms sa =
  SAtom.fold (fun a mc ->
    if lit_abstract a then mc
    else
      let rsa = SAtom.remove a sa in
      let unc = unconstrained_terms rsa all_var_terms in 
      let old_comps, old_uncs = 
	try MA.find a mc with Not_found -> SAtom.empty, STerm.empty in
      MA.add a (SAtom.union rsa old_comps, STerm.union unc old_uncs) mc
  ) sa


let stateless_forward s procs trs all_var_terms l =
  let h_visited = HI.create 2_000_029 in
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
	        (* else *) 
	        (* if HI.mem h_visited (SAtom.hash (fst s)) then new_td else *)
	        s :: new_td
	      ) new_td (post_inst sa args procs tr)
	    ) [] trs
	  in
	  incr cpt_f;
	  
	  if debug then eprintf "%d : %a@." !cpt_f Pretty.print_cube sa
	  else if !cpt_f mod 1000 = 0 then eprintf "%d (%d)@." !cpt_f
	    (List.length to_do + List.length new_td);
	  (* HI.add h_visited hsa (); *)
	  (* let mc = add_compagnions_from_node all_var_terms sa mc in *)
	  let d = all_permutations args args in
	  let mc = 
	    List.fold_left (fun mc sigma ->
	      let sa = subst_atoms sigma sa in
	      HI.add h_visited (SAtom.hash sa) ();
	      add_compagnions_from_node all_var_terms sa mc
	    ) mc d in
	  forward_rec s procs trs mc (List.rev_append new_td to_do)
  in
  forward_rec s procs trs MA.empty l
  

(* let mkinit args init all_args = *)
(*   match args with *)
(*     | [] -> init *)
(*     | _ -> *)
(*         let abs_init = (\* SAtom.filter (function *\) *)
(* 	  (\* | Comp ((Elem (x, _) | Access (x,_,_)), _, _) -> *\) *)
(* 	  (\*     not (Smt.Typing.has_abstract_type x) *\) *)
(* 	  (\* | _ -> true) *\) init in *)
(* 	let abs_init = simplification_atoms SAtom.empty abs_init in *)
(* 	let sa, cst =  *)
(*           SAtom.partition (fun a ->  *)
(*             List.exists (fun z -> has_var z a) args) abs_init in *)
(*         let lsigs = all_instantiations args all_args in *)
(*         List.fold_left (fun acc sigma -> *)
(*             SAtom.union (subst_atoms sigma sa) acc) cst lsigs *)

(* let mkinits procs ({t_init = ia, l_init}) = *)
(*   List.map (fun init -> *)
(*     let sa, (nargs, _) = proper_cube (mkinit ia init procs) in *)
(*     sa, nargs *)
(*   ) l_init *)

let make_init_cdnf args lsa lvars =
  match args, lvars with
    | [], _ ->   
	[lsa]
    | _, [] ->
        [List.map 
            (SAtom.filter (fun a -> 
              not (List.exists (fun z -> has_var z a) args)))
            lsa]
    | _ ->
        let lsigs = all_instantiations args lvars in
        List.fold_left (fun conj sigma ->
          let dnf = List.fold_left (fun dnf sa ->
            (* let sa = abs_inf sa in *)
            let sa = subst_atoms sigma sa in
            try (simplification_atoms SAtom.empty sa) :: dnf
            with Exit -> dnf
          ) [] lsa in
          dnf :: conj
        ) [] lsigs

let rec cdnf_to_dnf_rec acc = function
  | [] ->
      List.rev_map (fun sa -> sa, args_of_atoms sa) acc
  | [] :: r ->
      cdnf_to_dnf_rec acc r
  | dnf :: r ->
      let acc = 
        List.flatten (List.rev_map (fun sac -> 
          List.rev_map (SAtom.union sac) dnf) acc) in
      cdnf_to_dnf_rec acc r

let cdnf_to_dnf = function
  | [] -> [SAtom.singleton Atom.False, []]
  | l -> cdnf_to_dnf_rec [SAtom.singleton Atom.True] l

let mkinits procs ({t_init = ia, l_init}) =
  cdnf_to_dnf (make_init_cdnf ia l_init procs) 

let mkforward_s s =
  List.map (fun fo ->
    let _,_,sa = fo in
    let sa, (nargs, _) = proper_cube sa in
    sa, nargs
  ) s.t_forward


let instance_of_transition { tr_args = tr_args; 
		             tr_reqs = reqs; 
		             tr_name = name;
		             tr_ureq = ureqs;
		             tr_assigns = assigns; 
		             tr_upds = upds; 
		             tr_nondets = nondets } all_procs tr_others sigma =
  let reqs = subst_atoms sigma reqs in
  let t_args_ef = 
    List.fold_left (fun acc p -> 
      try (svar sigma p) :: acc
      with Not_found -> p :: acc) [] tr_args in
  let udnfs = uguard_dnf sigma all_procs t_args_ef ureqs in
  let assi, assi_terms = apply_assigns assigns sigma in
  let upd, upd_terms = apply_updates upds all_procs sigma in
  let act = simplification_atoms SAtom.empty (SAtom.union assi upd) in
  let act = abstract_others act tr_others in
  {
    i_reqs = reqs;
    i_udnfs = udnfs;
    i_actions = act;
    i_touched_terms = STerm.union assi_terms upd_terms
  }


let instantiate_transitions all_procs procs trans = 
  let aux acc tr =
    let tr_others,others = missing_args procs tr.tr_args in
    let d = all_permutations tr.tr_args procs in
    (* do it even if no arguments *)
    let d = if d = [] then [[]] else d in
    List.fold_left (fun acc sigma ->
      instance_of_transition tr all_procs tr_others sigma :: acc
    ) acc d
  in
  List.fold_left aux [] trans



let search procs init =
  let inst_trans = instantiate_transitions procs procs init.t_trans in
  forward init procs inst_trans (mkinits procs init)

let search_stateless procs init =
  let var_terms = all_var_terms procs init in
  let inst_trans = instantiate_transitions procs procs init.t_trans in
  stateless_forward init procs inst_trans var_terms (mkinits procs init)

let procs_from_nb n =
  let rp, _ = 
    List.fold_left (fun (acc, n) v ->
      if n > 0 then v :: acc, n - 1
      else acc, n) ([], n) proc_vars in
  List.rev rp

let search_only s = assert false
  (* let ex_args =  *)
  (*   match s.t_forward with (_, args, _) :: _ -> args | _ -> assert false in *)
  (* forward s ex_args s.t_trans (mkforward_s s) *)

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

let compagnions_from_trace forward_nodes all_var_terms =
  let lits = all_litterals forward_nodes in
  SAtom.fold (fun a acc ->
    if lit_abstract a then acc else
      let compagnions_uncs =
	HSA.fold (fun sa _ (acc, uncs) ->
	  if SAtom.mem a sa then
	    let rsa = SAtom.remove a sa in
	    let unc = unconstrained_terms rsa all_var_terms in
	    SAtom.union rsa acc, STerm.union unc uncs
	  else acc, uncs)
	  forward_nodes (SAtom.empty, STerm.empty)
      in 
      MA.add a compagnions_uncs acc
  ) lits MA.empty

let contains_unconstrained uncs = function
  | Comp (t1, op, t2) -> STerm.mem t1 uncs || STerm.mem t2 uncs
  | _ -> false

let compagnions_values compagnions uncs =
  SAtom.fold (fun c (acc, compagnions) ->
    if contains_unconstrained uncs c then acc, SAtom.remove c compagnions
    else
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
  if Hstring.equal (snd (Smt.Symbol.type_of x)) Smt.Type.type_bool then
    H.HSet.add htrue (H.HSet.singleton hfalse)
  else Smt.Variant.get_variants x


let variable_term_has_value v t =
  SAtom.exists (function
    | Comp (t1, Eq, t2) -> 
        compare_term v t1 = 0 && compare_term t t2 = 0
    | _ -> false)

let variable_term_has_other_values v t =
  SAtom.exists (function
    | Comp (t1, Eq, t2) ->
        (compare_term v t1 = 0 && compare_term t t2 <> 0) ||
	(compare_term v t2 = 0 && compare_term t t1 <> 0)
    | Comp (t1, Neq, t2) -> 
        compare_term v t1 = 0 && compare_term t t2 = 0
    | _ -> false)

let only_value_possible c sa =
  let sa = SAtom.remove c sa in
  match c with
    | Comp (v, Eq, t) -> not (variable_term_has_other_values v t sa)
    | Comp (v, Neq, t) -> not (variable_term_has_value v t sa)
    | _ -> false


exception Reduced_cand of Atom.t

let add_cand (a1, la) acc =
  match la with
    | [] | _::_::_ -> (a1, la) :: acc
    | [a2] ->
        try
          List.iter (fun (b1,lb) ->
            match lb with
              | [b2] ->
                  if Atom.equal a2 b2 && 
                    Cube.inconsistent_list [Atom.neg a1; Atom.neg b1] then
                    raise (Reduced_cand a2);
                  if Atom.equal a1 b1 &&
                    Cube.inconsistent_list [Atom.neg a2; Atom.neg b2] then
                    raise (Reduced_cand a1);
                  if Atom.equal a1 b2 &&
                    Cube.inconsistent_list [Atom.neg a2; Atom.neg b1] then
                    raise (Reduced_cand a1);
                  if Atom.equal a2 b1 &&
                    Cube.inconsistent_list [Atom.neg a1; Atom.neg b2] then
                    raise (Reduced_cand a2)
              | _ -> ()
          ) acc;
          (a1, la) :: acc
        with
          | Reduced_cand a -> (a, []) :: acc
    

let add_cand (a1, la) acc = (a1, la) :: acc

let candidates_from_compagnions a (compagnions, uncs) acc =
  let mt, remaining = compagnions_values compagnions uncs in
  let acc = 
    SAtom.fold (fun c acc ->
      if only_value_possible c remaining then add_cand (a, [Atom.neg c])  acc
      else acc
    ) remaining acc
  in
  MT.fold (fun c vals acc -> match c with
    | Elem (x, _) | Access (x, _) ->
      begin
	match H.HSet.elements vals with
	  | [v] when Hstring.equal v htrue ->
	    add_cand (a, [Comp (c, Eq, (Elem (hfalse, Constr)))])  acc	
	  | [v] when Hstring.equal v hfalse ->
	    add_cand (a, [Comp (c, Eq, (Elem (htrue, Constr)))])  acc
	  | [v] -> (a, [Comp (c, Neq, (Elem (v, Constr)))]) :: acc
	  | vs ->
	    try
	      let dif = H.HSet.diff (get_variants x) vals in
	      match H.HSet.elements dif with
		| [] -> acc
		| [cs] -> 
		    add_cand (a, [Comp (c, Eq, (Elem (cs, Constr)))])  acc
		| _ -> raise Not_found
	    with Not_found ->
	      add_cand (a, List.map (fun v -> Comp (c, Neq, (Elem (v, Constr)))) vs) 
	      acc
      end
    | _ -> assert false)
    mt acc


let proc_present p a sa =
  let rest = SAtom.remove a sa in
  SAtom.exists (function
    | Comp (Elem (h, Var), _, _)
    | Comp (_, _, Elem (h, Var)) when Hstring.equal h p -> true
    | _ -> false) rest

let hsort = Hstring.make "Sort"

let useless_candidate sa =
  SAtom.exists (function
    (* heuristic: remove proc variables *)
    | (Comp (Elem (p, Var), _, _) as a)
    | (Comp (_, _, Elem (p, Var)) as a) -> not (proc_present p a sa)

    | (Comp (Access (s, [p]), _, _) as a)
    | (Comp (_, _, Access (s, [p])) as a) when Hstring.equal s hsort ->
       not (proc_present p a sa)

    | Comp ((Elem (x, _) | Access (x,_)), _, _)
    | Comp (_, _, (Elem (x, _) | Access (x,_))) ->
      let x = if is_prime (Hstring.view x) then unprime_h x else x in
      (* Smt.Symbol.has_type_proc x ||  *)
        (enumerative <> -1 && Smt.Symbol.has_abstract_type x)
        (* (Hstring.equal (snd (Smt.Symbol.type_of x)) Smt.Type.type_real) || *)
        (* (Hstring.equal (snd (Smt.Symbol.type_of x)) Smt.Type.type_int) *)

    | Comp ((Arith _), _, _) when not abstr_num -> true

    | _ -> false) sa
  (* || List.length (args_of_atoms sa) > 1 *)


let remove_subsumed_candidates cands = cands
  (* List.fold_left (fun acc c -> *)
  (*   let acc' = List.filter (fun c' -> c.t_nb <> c'.t_nb) acc in *)
  (*   if fixpoint ~invariants:[] ~visited:acc' c <> None *)
  (*   (\* if easy_fixpoint c acc' <> None *\) *)
  (*   (\* if List.exists (fun c' -> easy_fixpoint c' [c] <> None) acc' *\) *)
  (*   then acc' *)
  (*   else acc) cands cands *)
  
let make_satom_from_list s la = 
  List.fold_left (fun sa x -> SAtom.add x sa) s la

let no_conflict_with a b = 
  match a, b with
    | True, False | False, True -> false
    | Comp(ta1, Eq, ta2), Comp(tb1, Eq, tb2) ->
	not (compare_term ta1 tb1 = 0 && compare_term ta2 tb2 <> 0)
    | Ite _, _ | _, Ite _ -> assert false
    | _, _ -> true

let asym_union sa1 sa2 = 
  SAtom.fold 
    (fun a s -> SAtom.add a (SAtom.filter (no_conflict_with a) s) ) sa1 sa2

(* naive version *)
let global_var = function
  | Comp(Elem(_,Glob),_,Elem(_,Constr)) 
  | Comp(Elem(_,Constr),_,Elem(_,Glob)) -> true
  | _ -> false

let update_array up = function
  | Comp (Access(m,_),_,_) | Comp (_,_,Access(m,_)) -> 
      (Hstring.compare up.up_arr m = 0) && 
	List.exists 
	(fun (sa, t) -> 
	   SAtom.is_empty sa && (match t with Access _ -> false | _ -> true)) 
	up.up_swts

  | _ -> false

let potential_update l trs = 
  List.exists global_var l ||
    List.exists 
    (fun tr -> 
       List.exists 
	 (fun up -> List.exists (update_array up) l) tr.tr_upds) trs

module MM = Hstring.HMap

let mm_for_all f m = 
  try MM.iter (fun x y -> ignore (f x y || raise Exit)) m; true
  with Exit -> false

let subset_node s1 s2 = 
  SAtom.subset s1 s2 || 
    try
      let s = SAtom.diff s1 s2 in
      let neqs = 
	SAtom.fold 
	  (fun a neqs ->
	     match a with
	       | Comp((Access(x,_) | Elem(x,Glob)),Neq,Elem(c,Constr)) 
	       | Comp(Elem(c,Constr),Neq,(Access(x,_) | Elem(x,Glob))) -> 
		   let cs = try MM.find x neqs with Not_found -> [] in
		   MM.add x (c::cs) neqs
	       | _ -> raise Exit ) s MM.empty
      in
      if MM.is_empty neqs then raise Exit;
      mm_for_all 
	(fun x cs -> 
	   SAtom.exists 
	     (fun a ->
		match a with
		  | Comp((Access(y,_) | Elem(y,Glob)),Eq,Elem(c,Constr)) 
		  | Comp(Elem(c,Constr),Eq,(Access(y,_) | Elem(y,Glob))) -> 
		      Hstring.equal x y && not (List.mem c cs)
		  | _ -> false
	     ) s2
	) neqs
    with Exit -> false


let forward_and_check s procs trs l sla =
  let h_visited = HSA.create 200_029 in
  let cpt_f = ref 0 in
  let rec forward_rec s procs trs = function
    | [] -> eprintf "Total forward nodes : %d@." !cpt_f
    | (sa, args) :: to_do ->
	if subset_node sla sa then raise Exit;
	if HSA.mem h_visited sa then
	  forward_rec s procs trs to_do
	else
	  let new_td =
	    List.fold_left (fun new_td tr ->
			      List.fold_left (fun new_td s -> (s :: new_td)
	      ) new_td (post sa args procs tr)
	    ) [] trs
	  in
	  incr cpt_f;
	  if !cpt_f mod 1000 = 0 then eprintf "%d@." !cpt_f;
	  HSA.add h_visited sa ();
	  forward_rec s procs trs (List.rev_append new_td to_do)
  in
  forward_rec s procs trs l

let stateless_forward_and_check s procs trs l sla =
  let h_visited = HI.create 2_000_029 in
  let cpt_f = ref 0 in
  let rec forward_rec s procs trs = function
    | [] -> eprintf "Total forward nodes : %d@." !cpt_f
    | (sa, args) :: to_do ->
	if subset_node sla sa then raise Exit;
	let hsa = SAtom.hash sa in
	if HI.mem h_visited hsa then
	  forward_rec s procs trs to_do
	else
	  let new_td =
	    List.fold_left (fun new_td tr ->
			      List.fold_left (fun new_td s -> (s :: new_td)
					     ) new_td (post sa args procs tr)
			   ) [] trs
	  in
	  incr cpt_f;
	  if !cpt_f mod 1000 = 0 then eprintf "%d@." !cpt_f;
	  HI.add h_visited hsa ();
	  forward_rec s procs trs (List.rev_append new_td to_do)
  in
  forward_rec s procs trs l

let dead_candidate np args init_np s nodes a la = 
  let sla = make_satom_from_list (SAtom.singleton a) la in
  List.exists
    (fun node -> 
       if debug && verbose > 1 then
	 eprintf "The node in the trace is :%a@." Pretty.print_cube node;
       let depart = asym_union node init_np in
       if debug && verbose > 1 then
	 eprintf "We run the trace from :%a@." Pretty.print_cube depart;
       try  
	 stateless_forward_and_check s np s.t_trans [depart, args@np] sla; false
       with Exit -> true
    ) nodes

let still_alive fwd candidates s a la = 
  let sla = make_satom_from_list SAtom.empty la in
  if debug && verbose > 0 then 
    eprintf "We check that (%a, %a) is alive with an extra process@."
      Pretty.print_atom a Pretty.print_cube sla;

  let args = fst s.t_unsafe in
  let np = [Hstring.make ("#"^(string_of_int (List.length args + 1)))] in
  let init_np = assert false 
  (* TODO : change this for dnf init or remove all: mkinit (fst s.t_init) (snd s.t_init) np*)
  in

  let pla = potential_update la s.t_trans in
  let pa =  potential_update [a] s.t_trans in
  let nodes = 
    HSA.fold 
      (fun node _ nodes -> 
	 if (subset_node sla node && pa) || 
	    (subset_node (SAtom.singleton a) node && pla)
	 then node :: nodes else nodes) fwd [] in

  if debug && verbose > 0 then
    eprintf "We're running %d forward traces! @." (List.length nodes); 

  let dead = dead_candidate np args init_np s nodes a la in

  if debug && verbose > 0 then
    if dead then eprintf "Dead!@." else eprintf "Still alive!@.";
  not dead

 
let filter_alive_candidates fwd candidates = 
  let dead_candidates = ref 0 in
  if debug then 
    begin
      eprintf "Potential candidates:@.";
      List.iter 
	(fun (a, (la, _)) ->
	   let la = make_satom_from_list SAtom.empty la in
	   eprintf "candidate : %a && %a\n@." 
	     Pretty.print_atom a 
	     Pretty.print_cube la)
	candidates;
      eprintf "@."
    end;
  let candidates = 
    List.fold_left 
      (fun acc (a, (la, s)) -> 
	 if still_alive fwd candidates s a la then s::acc 
	 else (incr dead_candidates; acc)) [] candidates
  in
  eprintf "Number of dead candidates : %d@." !dead_candidates;
  candidates

let extract_candidates comps s =
  let cpt = ref (-1) in
  if debug then
    MA.iter (fun a (compagnions, uncs) ->
      eprintf "compagnons %a : %a@."
	Pretty.print_atom a Pretty.print_cube compagnions;
      eprintf "> unconstrained :\n";
      STerm.iter 
	(fun t -> eprintf "               %a\n" Pretty.print_term t)
	uncs;
      eprintf "@.";      
    ) comps;
  let sas = MA.fold candidates_from_compagnions comps [] in
  let sas = List.rev sas in
  Gc.full_major ();
  List.fold_left 
    (fun acc (a, la) ->
       let sa = make_satom_from_list (SAtom.singleton a) la in
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
	 if List.exists 
	   (fun (_,(_,s)) -> ArrayAtom.equal s.t_arru s'.t_arru) acc then acc
	 else 
	   (decr cpt; (a, (la, s')) :: acc)) [] sas

let compare_candidates s1 s2 =
  let v1 = Cube.size_system s1 in
  let v2 = Cube.size_system s2 in
  let c = Pervasives.compare v1 v2 in
  if c <> 0 then c else
    let c1 = Cube.card_system s1 in
    let c2 = Cube.card_system s2 in
    Pervasives.compare c1 c2


let sort_candidates =
  List.fast_sort compare_candidates

let extract_candidates_from_compagnons comps s =
  let c = extract_candidates comps s in
  let cands = List.rev_map (fun (_,(_,s)) -> s) c in
  (* sort_candidates *) (*cands*)
  remove_subsumed_candidates cands

let extract_candidates_from_trace forward_nodes all_var_terms s =
  let comps = compagnions_from_trace forward_nodes all_var_terms in
  let cands = 
    if refine then
      let c = extract_candidates comps s in
      filter_alive_candidates forward_nodes c
    else
      begin
	HSA.clear forward_nodes;
	extract_candidates_from_compagnons comps s
      end
  in
  (* sort_candidates *) cands
  
  
let select_relevant_candidates {t_unsafe = _, sa} =
  List.filter (fun {t_unsafe = _, ca} ->
    not (SAtom.is_empty (SAtom.inter ca sa))
  )

 
(*-------------- interface for inductification ---------------------------*)

let post_system ({ t_unsafe = uargs, u; t_trans = trs}) =
  List.fold_left
    (fun ls tr -> assert false ) 
    [] 
    trs 
    



(********************************************)
(* Check if formula is unreachable on trace *)
(********************************************)

exception Reachable of (transition * (Hstring.t * Hstring.t) list) list

let all_partitions s =
  List.fold_left (fun acc x ->
    [x] :: List.map (fun l -> x :: l) acc) [] (List.rev s)


let mkinits_up_to procs_sets s =
  if procs_sets = [] then mkinits [] s
  else
    List.fold_left
      (fun acc procs -> List.rev_append (mkinits procs s) acc) [] procs_sets

exception Spurious_step of t_system

let above s trace =
  let rec above_rec s acc = function
    | tx :: (_, _, y) :: _ when s.t_nb = y.t_nb -> List.rev (tx :: acc)
    | tx :: r -> above_rec s (tx :: acc) r
    | _ -> assert false
  in
  above_rec s [] trace


type possible_result = 
  | Reach of (transition * (Hstring.t * Hstring.t) list) list 
  | Spurious of (transition * Hstring.t list * t_system) list
  | Unreach


let possible_trace ~starts ~finish ~procs ~trace =
  let _, usa = finish.t_unsafe in
  let rec forward_rec ls rtrace = match ls, rtrace with
    | _, [] -> Unreach
    | [], (_, _, s) ::_ -> Spurious (above s trace)
    | _, (tr, _, _) :: rest_trace ->
        let nls =
	  if List.length tr.tr_args > List.length procs then []
	  else
           List.fold_left (fun acc sigma ->
            let itr = instance_of_transition tr procs [] sigma in
            List.fold_left (fun acc (sa, args, hist) ->
              List.fold_left (fun acc (nsa, nargs) ->
                let new_hist = (tr, sigma) :: hist in
                try Prover.reached procs usa nsa; raise (Reachable new_hist)
                with Smt.Unsat _ -> (nsa, nargs, new_hist) :: acc
              ) acc (post_inst sa args procs itr)
            ) acc ls
           ) [] (all_permutations tr.tr_args procs)
        in
        forward_rec nls rest_trace
  in
  try
    let init = List.map (fun (isa, iargs)-> isa, iargs, []) starts in
    forward_rec init trace
  with
    | Reachable hist -> Reach hist
  

let discharged_with_full_trace prefix above =
  (* eprintf "dwft: %d@." top.t_nb; *)
  (* begin *)
  (*   eprintf "\n@{<fg_red>3above:@} @["; *)
  (*   List.iter (fun (tr, sigma, x) -> *)
  (* 	       eprintf "%a(%a) ->%d-> @ " Hstring.print tr.tr_name *)
  (* 		       Pretty.print_args  sigma x.t_nb *)
  (* 	      ) above; *)
  (* end; *)
  let rec aux acc rev_top rest_above =
    match rest_above with
    | (_, _, x) as tx :: r ->
       let acc = 
	 List.fold_left 
	   (fun acc s ->
	    let rev_top = match rev_top with 
	      | [] -> [] 
	      | (tr, ar, _) :: rt -> (tr, ar, s) :: rt in
	    (rev_top, s.t_from) :: acc)
	   acc (Cube.discharged_on x) in
       aux acc (tx :: rev_top) r
    | [] -> acc
  in
  aux [] prefix above

let rec list_excedent = function
  | _, [] -> assert false
  | [], l2 -> l2
  | _ :: l1, _ :: l2 -> list_excedent (l1, l2)
  

let rec equal_trace_woargs tr1 tr2 =
  match tr1, tr2 with
  | [], [] -> true
  | [], _ -> false
  | _, [] -> false
  | (x, _, _)::r1, (y, _, _)::r2 ->
     Hstring.equal x.tr_name y.tr_name && equal_trace_woargs r1 r2

module HTrace = 
  Hashtbl.Make (
      struct
	type t = (transition * Hstring.t list * t_system) list
	let equal = equal_trace_woargs
	let hash = Hashtbl.hash_param 50 100
      end)
			       

let reachable_on_trace_from_init s trace =
  let all_procs_set =
    List.fold_left (fun acc (_, procs_t, {t_unsafe = procs_c, _}) ->
      List.fold_left (fun acc p -> Hstring.HSet.add p acc) acc
		     (List.rev_append procs_t procs_c)
    ) Hstring.HSet.empty trace in
  let all_procs = Hstring.HSet.elements all_procs_set in
  let proc_sets = (* all_partitions *) [all_procs] in
  let inits = mkinits_up_to proc_sets s in
  possible_trace ~starts:inits ~finish:s ~procs:all_procs ~trace

let reachable_on_all_traces_from_init s trace =
  let checked = HTrace.create 2001 in
  let all_procs_set =
    List.fold_left (fun acc (_, procs_t, {t_unsafe = procs_c, _}) ->
      List.fold_left (fun acc p -> Hstring.HSet.add p acc) acc
		     (List.rev_append procs_t procs_c)
    ) Hstring.HSet.empty trace in
  let all_procs = Hstring.HSet.elements all_procs_set in
  let proc_sets = (* all_partitions *) [all_procs] in
  let inits = mkinits_up_to proc_sets s in
  let rec reachable_split_from_init s prefix_tr trace_bot =
    eprintf "rsfi %d@." s.t_nb;
    let trace = List.rev_append prefix_tr trace_bot in
    eprintf "\n@{<fg_red>reach on trace:@} @[";
    List.iter (fun (tr, sigma, x) ->
	       eprintf "%a(%a) ->%d-> @ " Hstring.print tr.tr_name
		       Pretty.print_args  sigma x.t_nb
	      ) trace;
    HTrace.add checked trace ();
    match possible_trace ~starts:inits ~finish:s ~procs:all_procs ~trace with
    | (Unreach | Reach _) as r -> r
    | Spurious above_trace ->
       let problematic_trace_section = list_excedent (prefix_tr, above_trace) in
       try 
	 eprintf "\n\n>> check %d@." (List.length (discharged_with_full_trace prefix_tr problematic_trace_section));
	 List.iter
     	   (fun (prefix, trace) ->
	    if HTrace.mem checked (List.rev_append prefix trace) then ()
     	    else
	      match reachable_split_from_init s prefix trace with
     	      | Reach hist -> raise (Reachable hist)
     	      | _ -> ())
     	   (discharged_with_full_trace prefix_tr problematic_trace_section);
	 Unreach
       with Reachable hist -> Reach hist
  in
  reachable_split_from_init s [] trace

let possible_history s =
  let trace = s.t_from in
  let all_procs_set =
    List.fold_left (fun acc (_, procs_t, {t_unsafe = procs_c, _}) ->
      List.fold_left (fun acc p -> Hstring.HSet.add p acc) acc
		     (List.rev_append procs_t procs_c)
    ) Hstring.HSet.empty trace in
  let all_procs = Hstring.HSet.elements all_procs_set in
  let iargs, isa = s.t_unsafe in 
  possible_trace ~starts:[isa, iargs] ~finish:(origin s) ~procs:all_procs ~trace

		 
let spurious s =
  match possible_history s with
    | Unreach | Spurious _ -> true
    | Reach hist ->
        if debug then
	  begin
	    eprintf "\n@{<fg_red>Error trace:@} @[";
	    List.iter (fun (tr, sigma) ->
		       eprintf "%a(%a) ->@ " Hstring.print tr.tr_name
			       Pretty.print_args (List.map snd sigma)
		      ) (List.rev hist);
	    let nun = (origin s).t_nb in
	    if nun < 0 then 
	      eprintf "@{<fg_blue>approx[%d]@}" nun
	    else 
	      eprintf "@{<fg_magenta>unsafe[%d]@}" nun;
	    eprintf "@]@.";
	  end;
        false


let spurious_error_trace s =
  match reachable_on_all_traces_from_init (origin s) s.t_from with
  | Spurious _ -> assert false
  | Unreach -> true
  | Reach hist ->
        if debug then
	  begin
	    eprintf "\n@{<fg_red>Error trace:@} @[";
	    List.iter (fun (tr, sigma) ->
		       eprintf "%a(%a) ->@ " Hstring.print tr.tr_name
			       Pretty.print_args (List.map snd sigma)
		      ) (List.rev hist);
	    let nun = (origin s).t_nb in
	    if nun < 0 then 
	      eprintf "@{<fg_blue>approx[%d]@}" nun
	    else 
	      eprintf "@{<fg_magenta>unsafe[%d]@}" nun;
	    eprintf "@]@.";
	  end;
        false


let conflicting_from_trace s trace =
  let all_procs_set =
    List.fold_left (fun acc (_, procs_t, {t_unsafe = procs_c, _}) ->
      List.fold_left (fun acc p -> Hstring.HSet.add p acc) acc
		     (List.rev_append procs_t procs_c)
    ) Hstring.HSet.empty trace in
  let all_procs = Hstring.HSet.elements all_procs_set in
  let rec forward_rec acc ls trace = match trace with
    | [] -> acc
    | (tr, procs, _) :: rest_trace ->
        let sigma = List.combine tr.tr_args procs in
        let itr = instance_of_transition tr all_procs [] sigma in
        let nls, acc = 
          List.fold_left (fun (nls, acc) (sa, args) ->
            List.fold_left (fun (nls, acc) (nsa, nargs) ->
              (nsa, nargs) :: nls, nsa :: acc
            ) (nls, acc) (post_inst sa args all_procs itr)
          ) ([], acc) ls
        in
        forward_rec acc nls rest_trace
  in
  forward_rec [] (mkinits all_procs s) trace
