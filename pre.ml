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

open Options
open Format
open Ast
open Util
open Types

type reset_memo = unit -> unit
			    
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
    if not debug then fun _ -> () 
                 else fun s -> eprintf "    %a@." Node.print s

  let invariant = 
      fun s -> eprintf "Invariant ?@. %a@." Cube.print s

  let pre = 
    if not debug then fun _ _ -> () else 
      fun tr p ->
      eprintf "\nResult of the pre for transition %s (%a):@.%a@."
        (H.view tr.tr_name)
        Variable.print_vars tr.tr_args
        SAtom.print p

  let pre_cubes = 
    if not debug then fun _ _ -> () else 
      fun p args ->
      eprintf "Cubes (%a) :%a@." Variable.print_vars args SAtom.print p

end


(***********************************************************************)
(* Pre-image of an atom w.r.t a transition, simply represented here by *)
(* a function tau						                                           *)
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

type assign = Single of term | Branch of swts

let fresh_nondet = 
  let cpt = ref 0 in 
  fun (args, ret) -> 
    incr cpt; 
    let s = H.make ("!"^(string_of_int !cpt)) in
    Smt.Symbol.declare s args ret;
    s

let rec find_update a li = function
  | [] -> raise Not_found
  | { up_loc = loc; up_arr = a'; up_arg = lj; up_swts = ls} :: _ when a=a' ->
      let ls = 
        List.map 
        (fun (ci, ti) ->
          let sigma  = List.combine lj li in
          SAtom.subst sigma ci,
          Term.subst  sigma ti
        ) 
        ls 
      in
      Branch ls
  | _ :: l -> find_update a li l

exception Remove_lit_var of Hstring.t

let find_assign_vea memo tr tt = 
  match tt with 
  | Vea.Elem (x, sx) -> 
    let gu =
      if H.list_mem x tr.tr_nondets then 
             (*raise (Remove_lit_var x)*)
          try List.assoc (Hstring.view x) !memo with Not_found ->
          let nv = UTerm (Vea(Elem (fresh_nondet (Smt.Symbol.type_of x), sx))) in
          memo := (Hstring.view x,nv) :: !memo;
          nv
       else 
         try fst (H.list_assoc_triplet x tr.tr_assigns) with Not_found -> 
          (
            UTerm (Vea(Elem (x, sx)))
          )
    in
   
    begin match gu with
     | UTerm t    -> Single t
     | UCase swts -> Branch swts
    end
  | Vea.Access (a, li) -> 
      begin
        try find_update a li tr.tr_upds
        with Not_found -> Single (Vea tt)
      end

let rec create_switch_list ts vea_assign_map acc =
  match VMap.choose_opt vea_assign_map with 
  | Some (vea, ass) -> 
      let without = VMap.remove vea vea_assign_map in
      let c       = VMap.find vea ts in 
      let acc'    = 
        match ass with 
        | Single t ->
            List.map 
            (fun (sa',t') -> (sa', term_add (term_mult_by_const t c) t'))
            acc
        | Branch b ->
            let r = 
              List.map 
              (fun (sa', t') -> 
                List.map
                (fun (sa, t) -> SAtom.inter sa sa', term_add (term_mult_by_const t c) t')
                b)
              acc
            in List.flatten r
      in
      create_switch_list ts without acc'
  | None            -> acc

let find_assign memo tr tt =
  match tt with 
  | Vea  (vea)    -> find_assign_vea memo tr vea
  | Poly (cs, ts) ->
        let vea_assign_map = VMap.mapi (fun vea _ -> find_assign_vea memo tr vea) ts in 
        let true_satom = SAtom.singleton Atom.True in
        let empty_poly = Poly(cs, VMap.empty) in
        let res = create_switch_list ts vea_assign_map [(true_satom, empty_poly)] in
        match res with 
        | (_, t) :: [] -> Single t 
        | _            -> Branch res
				
let make_tau tr =
  let memo = ref [] in
  (fun x op y ->
  try
    match find_assign memo tr x, find_assign memo tr y with
    | Single tx, Single ty -> Atom.Comp (tx, op, ty)
    | Single tx, Branch ls ->
       List.fold_right
       (fun (ci, ti) f -> Atom.Ite(ci, Atom.Comp(tx, op, ti), f))
       ls Atom.True
    | Branch ls, Single tx ->
       List.fold_right
       (fun (ci, ti) f -> Atom.Ite(ci, Atom.Comp(ti, op, tx), f))
       ls Atom.True
    | Branch ls1, Branch ls2 ->
       List.fold_right
       (fun (ci, ti) f -> 
          List.fold_right 
          (fun (cj, tj) f ->
           Atom.Ite(SAtom.union ci cj, Atom.Comp(ti, op, tj), f)) ls2 f)
       ls1 Atom.True
  with Remove_lit_var _ -> Atom.True),
  (fun () -> memo := [])

(**********************)
(* Postponed Formulas *)
(**********************)

let postpone args p np = 
  let sa1 = SAtom.filter (Atom.has_vars args) p in
  let sa2 = SAtom.filter (Atom.has_vars args) np in
  SAtom.equal sa2 sa1

let uguard sigma args tr_args tr_ureq =
  match tr_ureq with
    | [] -> [SAtom.empty]
    | [j, dnf, _] ->
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

let make_cubes (ls, post) rargs s tr cnp =
  let { cube = { Cube.vars = uargs; litterals = p}; tag = nb } = s in
  let nb_uargs = List.length uargs in
  let args = cnp.Cube.vars in
  let cube acc sigma =
    let tr_args = List.map (Variable.subst sigma) tr.tr_args in
    let lnp = Cube.elim_ite_simplify (Cube.subst sigma cnp) in
    (* cubes are in normal form *)
    List.fold_left
      (fun (ls, post) cnp ->
       let np, nargs = cnp.Cube.litterals, cnp.Cube.vars in
       let lureq = uguard sigma nargs tr_args tr.tr_ureq in
       List.fold_left 
	 (fun (ls, post) ureq ->
	  try
	    let ureq = Cube.simplify_atoms_base np ureq in
	    let np = SAtom.union ureq np in 
	    if debug && verbose > 0 then Debug.pre_cubes np nargs;
	    if Cube.inconsistent_set np then
              begin
		if debug && verbose > 0 then eprintf "(inconsistent)@.";
		(ls, post)
	      end
	    else
        let new_cube = Cube.create nargs np in
        let new_s = Node.create ~from:(Some (tr, tr_args, s)) new_cube in
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
  if List.length tr.tr_args > List.length rargs then
    begin
      if !size_proc = 0 then assert false;
      (ls, post)
    end
  else
    (* let d_old = Variable.all_permutations tr.tr_args rargs in *)
    (* TODO: Benchmark this *)
    let d = Variable.permutations_missing tr.tr_args args in
    (* assert (List.length d_old >= List.length d); *)
    List.fold_left cube (ls, post) d


(* The following version computes the pre-image once for each transition and
   instantiates afterwards.
   FIXME: This is supposed to be faster but this implementation is not.
          (check order, ...)
*)
let make_cubes_new (ls, post) rargs s tr cnp =
  failwith "To implement"



(*****************************************************)
(* Pre-image of an unsafe formula w.r.t a transition *)
(*****************************************************)

let pre { tr_info = tri; tr_tau = tau; tr_reset = reset } unsafe =
  let pre_unsafe = 
    SAtom.union 
      (fst tri.tr_reqs) 
      (SAtom.fold (fun a -> SAtom.add (pre_atom tau a)) unsafe SAtom.empty)
  in
  let pre_u = Cube.create_normal pre_unsafe in
  if debug && verbose > 0 then Debug.pre tri pre_unsafe;
  reset();
  let args = pre_u.Cube.vars in
  if tri.tr_args = [] then tri, pre_u, args
  else
    let nargs = Variable.append_extra_procs args tri.tr_args in
    if !size_proc <> 0 && List.length nargs > !size_proc then
      tri, pre_u, args
    else tri, pre_u, nargs


(*********************************************************************)
(* Pre-image of a system s : computing the cubes gives a list of new *)
(* systems							                                             *)
(*********************************************************************)

let pre_image trs s =
  TimePre.start (); 
  Debug.unsafe s;
  let u = Node.litterals s in
  let ls, post = 
    List.fold_left
    (fun acc tr ->
       let trinfo, pre_u, info_args = pre tr u in
       make_cubes acc info_args s trinfo pre_u) 
    ([], []) 
    trs 
  in
  TimePre.pause ();
  List.rev ls, List.rev post
