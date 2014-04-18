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

open Options
open Format
open Ast
open Types

module H = Hstring

module Debug = struct

  let fixpoint = 
    if not debug then fun _ -> () else 
      fun ls ->
	eprintf "\nAfter simplification, subsumption and fixpoint check : @.";
	match ls with
	  | [] -> eprintf "No new branches@."
	  | _ -> 
	      List.iter (eprintf "@.New branch : %a@." Node.print) ls

  let unsafe = 
    if not debug then fun _ -> () else 
      fun s -> eprintf "    %a@." Node.print s

  let invariant = 
      fun s -> eprintf "Invariant ?@. %a@." Cube.print s

  let pre = 
    if not debug then fun _ _ -> () else 
      fun tr p ->
	eprintf "\nResult of the pre for transition %s (%a):@.%a@."
	  (H.view tr.tr_name)
	  Variable.print_vars tr.tr_args
	  Cube.print p

  let pre_cubes = 
    if not debug then fun _ _ -> () else 
      fun p args ->
	eprintf "Cubes (%a) :%a@." Variable.print_vars args Cube.print p

end


(***********************************************************************)
(* Pre-image of an atom w.r.t a transition, simply represented here by *)
(* a function tau						       *)
(***********************************************************************)

let rec pre_atom tau a = 
  match a with
    | Atom.True | Atom.False -> a
    | Atom.Comp (x, op, y) -> tau x op y
    | Atom.Ite (sa, a1, a2) -> 
	let pre_sa = 
	  SAtom.fold (fun a -> SAtom.add (pre_atom tau a)) sa SAtom.empty 
	in
	let pre_a1 = pre_atom tau a1 in 
	let pre_a2 = pre_atom tau a2 in 
	Atom.Ite(pre_sa, pre_a1, pre_a2)

(****************************************)
(* Convert a transition into a function *)
(****************************************)

type assign = Single of term | Branch of update

let fresh_nondet = 
  let cpt = ref 0 in 
  fun (args, ret) -> 
    incr cpt; 
    let s = H.make ("*"^(string_of_int !cpt)) in
    Smt.Symbol.declare s args ret;
    s

let rec find_update a li = function
  | [] -> raise Not_found
  | { up_arr = a'; up_arg = lj; up_swts = ls} :: _ when a=a' ->
      let ls = 
	List.map 
	  (fun (ci, ti) ->
            let sigma  = List.combine lj li in
            SAtom.subst sigma (* ~sigma_sort:[Var, si] *) ci,
            Term.subst sigma (* ~sigma_sort:[Var, si] *) ti) ls in
      Branch { up_arr = a'; up_arg = li; up_swts = ls}
  | _ :: l -> find_update a li l


let rec find_assign tr = function
  | Elem (x, sx) -> 
      let t = 
	if H.list_mem x tr.tr_nondets then 
	  Elem (fresh_nondet (Smt.Symbol.type_of x), sx)
	else 
	  try H.list_assoc x tr.tr_assigns with Not_found -> Elem (x, sx)
      in 
      Single t

  | Const i as a -> Single a

  | Arith (x, cs1) ->
      begin
	let t = find_assign tr x in
	match t with
	  | Single (Const cs2) -> 
	      let c = 
		Const (add_constants cs1 cs2)
	      in
	      Single c
	  | Single (Arith (y, cs2)) ->
	      Single (Arith (y, add_constants cs1 cs2))
	  | Single y -> Single (Arith (y, cs1))
	  | Branch up ->
	      Branch { up with 
		up_swts = List.map (fun (sa, y) -> (sa, (Arith (y, cs1))))
		  up.up_swts
	      }
      end
  | Access (a, li) -> 
      let nli =
        List.map (fun i ->
	  if H.list_mem i tr.tr_nondets then 
	    fresh_nondet (Smt.Symbol.type_of i)
	  else 
	    try (match H.list_assoc i tr.tr_assigns with
	      | Elem (ni, _) -> ni
	      | Const _ | Arith _ | Access _ -> assert false)
	    with Not_found -> i
        ) li in
      try find_update a nli tr.tr_upds
      with Not_found -> 
	let na = 
	  try (match H.list_assoc a tr.tr_assigns with
		 | Elem (na, _) -> na
		 | Const _ | Arith _ | Access _ -> assert false)
	  with Not_found -> a
	in
	Single (Access (na, nli))

let make_tau tr x op y =
  match find_assign tr x, find_assign tr y with
    | Single tx, Single ty -> Atom.Comp (tx, op, ty)
    | Single tx, Branch {up_arr=a; up_arg=j; up_swts=ls} ->
	List.fold_right
	  (fun (ci, ti) f -> Atom.Ite(ci, Atom.Comp(tx, op, ti), f))
	  ls Atom.True
    | Branch {up_arr=a; up_arg=j; up_swts=ls}, Single tx ->
	List.fold_right
	  (fun (ci, ti) f -> Atom.Ite(ci, Atom.Comp(ti, op, tx), f))
	  ls Atom.True
    | Branch {up_arr=a1; up_arg=j1; up_swts = ls1 },
	Branch {up_arr=a2; up_arg=j2; up_swts= ls2 } ->
	List.fold_right
	  (fun (ci, ti) f -> 
	     List.fold_right 
	       (fun (cj, tj) f ->
		  Atom.Ite(SAtom.union ci cj, Atom.Comp(ti, op, tj), f)) ls2 f)
	  ls1 Atom.True

(**********************)
(* Postponed Formulas *)
(**********************)

let postpone args p np = 
  let sa1 = SAtom.filter (Atom.has_vars args) p in
  let sa2 = SAtom.filter (Atom.has_vars args) np in
  SAtom.equal sa2 sa1

let uguard sigma args tr_args = function
  | [] -> [SAtom.empty]
  | [j, dnf] ->
      let uargs = List.filter (fun a -> not (H.list_mem a tr_args)) args in
      List.fold_left 
	(fun lureq z ->
	   let m = List.map (SAtom.subst ((j, z)::sigma)) dnf in
	   List.fold_left 
	     (fun acc sa -> 
		(List.map (fun zy-> SAtom.union zy sa) m) @ acc ) [] lureq
	)
	[SAtom.empty]
	uargs

  | _ -> assert false

let add_list n l =
  if List.exists (fun n' -> Node.subset n' n) l then l
  else
    let l =
      if true || delete then
  	List.filter (fun n' -> not (Node.subset n n')) l
      else l
    in
      n :: l

let add_list a l = a :: l

let add_array_to_list n l =
  if List.exists (fun n' -> ArrayAtom.subset n' n) l then l
  else
    let l =
      if true || delete then
  	List.filter (fun n' -> not (ArrayAtom.subset n n')) l
      else l
    in
      n :: l

let make_cubes (ls, post) (args, rargs) s tr np =
  let { Node.cube = { Cube.vars = uargs; litterals = p}; tag = nb } = s in
      let nb_uargs = List.length uargs in
      let cube acc sigma =
	let lnp = Cube.elim_ite_simplify (SAtom.subst sigma np) in
	let tr_args = List.map (svar sigma) tr.tr_args in
	List.fold_left
	  (fun (ls, post) np ->
	     let np, (nargs, _) = proper_cube np in
	     let lureq = uguard sigma nargs tr_args tr.tr_ureq in
	     List.fold_left 
	       (fun (ls, post) ureq ->
		 try
		  let ureq = simplification_atoms np ureq in
		  let np = SAtom.union ureq np in 
		  if debug && verbose > 0 then Debug.pre_cubes np nargs;
		     if inconsistent np then begin
		    if debug && verbose > 0 then eprintf "(inconsistent)@.";
		    (ls, post)
		  end
		  else
		    if simpl_by_uc && 
		      already_closed s tr tr_args <> None 
		    then ls, post
		    else
		      let arr_np = ArrayAtom.of_satom np in
		      let from_forall = s.t_from_forall || tr.tr_ureq <> [] in
		      let new_s = 
			{ s with
			    t_from = (tr, tr_args, s)::s.t_from;
			    t_unsafe = nargs, np;
			    t_arru = arr_np;
			    t_alpha = ArrayAtom.alpha arr_np nargs;
			    t_nb = new_cube_id ();
			    t_nb_father = nb;
			    t_from_forall = from_forall;
			} in
		      match post_strategy with
			| 0 -> add_list new_s ls, post
			| 1 -> 
			    if List.length nargs > nb_uargs then
			      ls, add_list new_s post
			    else add_list new_s ls, post
			| 2 -> 
			    if not (SAtom.is_empty ureq) || postpone args p np 
			    then ls, add_list new_s post
			    else add_list new_s ls, post
			| _ -> assert false
		 with Exit -> ls, post
	       ) (ls, post) lureq ) acc lnp
      in
      if List.length tr.tr_args > List.length rargs then begin
        if !size_proc = 0 then assert false;
        (ls, post)
      end
      else
	(* let d_old = all_permutations tr.tr_args rargs in *)
	(* TODO: Benchmark this *)
	let d = permutations_missing tr.tr_args args in
	(* assert (List.length d_old >= List.length d); *)
	List.fold_left cube (ls, post) d


(* The following version computes the pre-image once for each transition and
   instantiates afterwards.
   FIXME: This is supposed to be faster but this implementation is not.
          (check order, ...)
*)
let make_cubes_new (ls, post) (args, rargs) s tr np =
  let { Node.cube = { Cube.vars = uargs; litterals = p}; tag = nb } = s in 
  if List.length tr.tr_args > List.length rargs then
    begin
      if !size_proc = 0 then assert false;
      (ls, post)
    end
  else
    let nb_uargs = List.length uargs in
    let np, (nargs, _) = proper_cube np in
    let lureq = uguard [] nargs tr.tr_args tr.tr_ureq in
    let new_arrs = 
      List.fold_left
	(fun acc ureq ->
	 try
	   let ureq = simplification_atoms np ureq in
	   let np = SAtom.union ureq np in 
	   if debug && verbose > 0 then Debug.pre_cubes np nargs;
	   if inconsistent np then acc
	   else np :: acc (* (ArrayAtom.of_satom np) acc *)
	 with Exit -> acc
	) [] lureq
    in
    (* let d = all_permutations tr.tr_args rargs in *)
    let d = permutations_missing tr.tr_args args in
    let from_forall = s.t_from_forall || tr.tr_ureq <> [] in
    List.fold_left 
      (fun acc np ->
       List.fold_left 
	 (fun (ls, post) sigma ->
	  let tr_args = List.map (svar sigma) tr.tr_args in
	  let np = subst_atoms sigma np in
	  let lnp = simplify_atoms np in
	  List.fold_left
	    (fun (ls, post) np ->
	     let np, (nargs, _) = proper_cube np in
	     let arr_np = ArrayAtom.of_satom np in
	     if inconsistent np then ls, post
	     else
	       let new_s = 
		 { s with
		   t_from = (tr, tr_args, s)::s.t_from;
		   t_unsafe = nargs, np;
		   t_arru = arr_np;
		   t_alpha = ArrayAtom.alpha arr_np nargs;
		   t_nb = new_cube_id ();
		   t_nb_father = nb;
		   t_from_forall = from_forall;
		 } in
	       match post_strategy with
	       | 0 -> add_list new_s ls, post
	       | 1 -> 
		  if List.length nargs > nb_uargs then
		    ls, add_list new_s post
		  else add_list new_s ls, post
	       | 2 -> 
		  if from_forall || postpone args p np 
		  then ls, add_list new_s post
		  else add_list new_s ls, post
	       | _ -> assert false
	    ) (ls, post) lnp
	 ) acc d
      ) (ls, post) new_arrs



let fresh_args ({ tr_args = args; tr_upds = upds} as tr) = 
  if args = [] then tr
  else
    let sigma = build_subst args fresh_vars in
    { tr with 
	tr_args = List.map (svar sigma) tr.tr_args; 
	tr_reqs = subst_atoms sigma tr.tr_reqs;
	tr_ureq = 
	List.map 
	  (fun (s, dnf) -> s, List.map (subst_atoms sigma) dnf) tr.tr_ureq;
	tr_assigns = 
	List.map (fun (x, t) -> x, subst_term sigma t) 
	  tr.tr_assigns;
	tr_upds = 
	List.map 
	  (fun ({up_swts = swts} as up) -> 
	     let swts = 
	       List.map 
		 (fun (sa, t) -> subst_atoms sigma sa, subst_term sigma t) swts
	     in
	     { up with up_swts = swts }) 
	  upds}


(*****************************************************)
(* Pre-image of an unsafe formula w.r.t a transition *)
(*****************************************************)

let pre tr unsafe =
  let tr = fresh_args tr in
  let tau = make_tau tr in
  let pre_unsafe = 
    SAtom.union tr.tr_reqs 
      (SAtom.fold (fun a -> SAtom.add (pre_atom tau a)) unsafe SAtom.empty)
  in
  if debug && verbose > 0 then Debug.pre tr pre_unsafe;
  let pre_unsafe, (args, m) = proper_cube pre_unsafe in
  if tr.tr_args = [] then tr, pre_unsafe, (args, args)
  else
    let nargs = Variable.append_extra_procs args tr.tr_args in
    if !size_proc <> 0 && List.length nargs > !size_proc then
      tr, pre_unsafe, (args, args)
    else tr, pre_unsafe, (args, nargs)


(*********************************************************************)
(* Pre-image of a system s : computing the cubes gives a list of new *)
(* systems							     *)
(*********************************************************************)

let pre_image trs s =
  TimePre.start (); 
  Debug.unsafe s;
  let u = Node.array s in
  let ls, post = 
    List.fold_left
    (fun acc tr ->
       let tr, pre_u, info_args = pre tr u in
       make_cubes acc info_args s tr pre_u) 
    ([], []) 
    trs 
  in
  TimePre.pause ();
  ls, post
