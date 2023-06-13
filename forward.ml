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
open Ast
open Types
open Atom
open Stdlib

module H = Hstring

type inst_trans =
    {
      i_reqs : SAtom.t;
      i_udnfs : SAtom.t list list;
      i_actions : SAtom.t;
      i_touched_terms : Term.Set.t;
    }

let prime_h h =
  Hstring.make ((Hstring.view h)^"@0")

let prime_vea vea = match vea with 
  | Vea.Elem   (e, Glob)  -> Vea.Elem   (prime_h e, Glob)
  | Vea.Access (a, lx)    -> Vea.Access (prime_h a, lx)
  | _ -> vea

let prime_term t = match t with
  | Vea(v) -> Vea(prime_vea v)
  | Poly(cs, ts) ->
      let ts' = VMap.fold (fun v c acc -> VMap.add (prime_vea v) c acc) ts VMap.empty in
      Poly(cs,ts') 

let rec prime_atom a = match a with
  | True | False -> a
  | Comp (t1, op, t2) -> Comp (prime_term t1, op, prime_term t2)
  | Ite (sa, a1, a2)  -> 
      Ite (prime_satom sa, prime_atom a1, prime_atom a2)
  
and prime_satom sa =
  SAtom.fold (fun a acc -> SAtom.add (prime_atom a) acc) sa SAtom.empty

let unprime_h h =
  let s = Hstring.view h in
  try Hstring.make (String.sub s 0 (String.index s '@'))
  with Not_found -> h

let rec unprime_term t = 
  let unprime_vea vea = 
    match vea with 
    | Vea.Elem (e, Glob) -> Vea.Elem   (unprime_h e, Glob)
    | Vea.Access (a, lx) -> Vea.Access (unprime_h a, lx)
    | _ -> vea
  in
  match t with
  | Vea v -> Vea (unprime_vea v)
  | Poly(cs, ts) -> 
      let ts' = VMap.fold (fun v c acc -> VMap.add (unprime_vea v) c acc) ts VMap.empty in
      Poly(cs,ts') 

let is_prime s =
  try
    let pos_at = String.rindex s '@' in
    ignore (int_of_string
              (String.sub s (pos_at + 1) (String.length s - pos_at - 1)));
    true
  with
  | Not_found -> false
  | Invalid_argument _ -> false
  | Failure _ -> false

let is_prime_term t =
  let is_prime_vea = function  
    | Vea.Elem (s, _) | Access (s, _) -> is_prime (Hstring.view s)
  in match t with 
  | Vea v        -> is_prime_vea v
  | Poly (_, ts) -> VMap.exists (fun k _ -> is_prime_vea k) ts

let rec is_prime_atom = function
  | True | False -> false
  | Comp (t1, _, t2) ->
    is_prime_term t1 || is_prime_term t2
  | Ite (sa, a1, a2) ->
    is_prime_atom a1 || is_prime_atom a2 || SAtom.exists is_prime_atom sa


let rec is_const t = 
  let is_const_vea = function 
    | Vea.Elem (_, (Constr | Var))  -> true
    | _                             -> false
  in match t with
  | Vea v -> is_const_vea v
  | Poly (_, ts) -> VMap.for_all (fun k _ -> is_const_vea k) ts 
  (* TODO G : Verify this *)

exception Found_const of (op_comp * term)

let find_const_value g init =
  try
    SAtom.iter (function
      | Comp (g', op, t') when Term.compare g g' = 0 ->
	      if is_const t' then raise (Found_const (op, t'))
      | Comp (t', op, g') when Term.compare g g' = 0 ->
	      if is_const t' then raise (Found_const (op, t'))
      | _ -> ()
    ) init;
    Format.printf "ERR: find_const_value\n%!";
    raise Not_found
  with Found_const c -> c

let find_const_value g init = 
  failwith "todo find cnst value"
  (*
  match g with
  | Arith (g', c) -> 
      begin
	let op, t = find_const_value g' init in
	match t with
	  | Const c' -> op, Const (add_constants c c')
	  | _ -> assert false
      end
  | _ -> find_const_value g init
  *)


let rec elim_prime_atom init = function
  | True  -> None 
  | False -> Some False
  | Comp (t1, Eq, t2)  ->
      let t1, t2 = 
      if is_prime_term t1 && not (is_prime_term t2) then t2, t1
                                                    else t1, t2 
      in
      assert (not (is_prime_term t1));
      if not (is_prime_term t2) then Some (Comp (t1, Eq, t2))
      else begin try
        let op, t2' = find_const_value t2 init in
        Some (Comp (t1, op, t2'))
        with Not_found -> None (* Some (Comp (t1, Eq, t2)) *)
      end
  | Ite (sa, a1, a2) ->
      let a1 = match elim_prime_atom init a1 with
        | None -> True
        | Some a1 -> a1 
      in
      let a2 = match elim_prime_atom init a2 with
        | None -> True
        | Some a2 -> a2 
      in
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
      if Term.compare t t1 = 0 then Comp (t', op, t2)
      else if Term.compare t t2 = 0 then Comp (t1, op, t')
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
        if Term.compare t t1 = 0 && is_const t2 then raise (Found_eq (t1, t2, a));
        if Term.compare t t2 = 0 && is_const t1 then raise (Found_eq (t2, t1, a))
      | _ -> ()
      ) 
    sa;
    SAtom.iter (fun a -> match a with
      | Comp (t1, Eq, t2) -> 
        if Term.compare t t1 = 0 then raise (Found_eq (t1, t2, a));
        if Term.compare t t2 = 0 then raise (Found_eq (t2, t1, a))
      | _ -> ()) 
    sa;
    SAtom.iter (fun a -> match a with
      | Comp (t1, Neq, t2) -> 
        if Term.compare t t1 = 0 then raise (Found_neq (t1, t2, a));
        if Term.compare t t2 = 0 then raise (Found_neq (t2, t1, a))
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
        if Term.compare t t1 = 0 then
          match res with
          | None -> 
              Some (Eq, t1, t2, a)
          | Some (Eq, _, t', _) when Term.compare t2 t' < 0 ->
              Some (Eq, t1, t2, a)
          | _ -> res	    
        else if Term.compare t t2 = 0 then
            match res with
              | None ->
                  Some (Eq, t2, t1, a)
              | Some (Eq, _, t', _) when Term.compare t1 t' < 0 ->
                  Some (Eq, t2, t1, a)
              | _ -> res
        else res
      end
    | Comp (t1, Neq, t2) -> 
      begin
        if Term.compare t t1 = 0 then
          match res with
            | None -> Some (Neq, t1, t2, a)
            | _ -> res
        else if Term.compare t t2 = 0 then
          match res with
            | None -> Some (Neq, t2, t1, a)
            | _ -> res
        else res
      end
    | Comp (t1, op, t2) ->
        (* TODO: perform fourier motzkin instead *)
        if Term.compare t t1 = 0 || Term.compare t t2 = 0 then
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
    | True | False     -> acc
    | Comp (t1, _, t2) ->
      let acc = if is_prime_term t1 then Term.Set.add t1 acc else acc in
      if is_prime_term t2 then Term.Set.add t2 acc else acc
    | Ite (sa, a1, a2) -> 
      primed_terms_of_atom a1 
	(primed_terms_of_atom a2 
	   (SAtom.fold primed_terms_of_atom sa acc))
  in
  primed_terms_of_atom a Term.Set.empty

exception First_primed_atom of Atom.t * Term.Set.t

let first_primed_atom sa =
  try
    SAtom.iter (fun a -> 
      let pts = primed_terms_of_atom a in
      if not (Term.Set.is_empty pts) then raise (First_primed_atom (a, pts))
    ) sa;
    Format.printf "ERR: First primed atom not found\n%!";
    raise Not_found
  with First_primed_atom (a, pts) -> a, pts

let rec elim_prime2 sa =
  let sa =
    try
      let a, pts = first_primed_atom sa in
      let sa = Term.Set.fold elim_primed_term pts sa in
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
    SAtom.fold (fun a acc -> Term.Set.union (primed_terms_of_atom a) acc )
      sa Term.Set.empty in
  let sa =
    SAtom.fold (fun a sa -> match a with
      | Comp (t1, op, t2) ->
	if Term.Set.mem t1 pts || Term.Set.mem t2 pts then SAtom.add a sa
	else sa
      | _ -> sa) init sa
  in
  elim_prime2 sa

let gauss_elim sa =
  SAtom.fold (fun a sa -> match a with
    | Comp ((Vea(Elem(_,Glob)) as t1), Eq, (Vea(Elem(_,Glob)) as t2)) ->
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
    Format.printf "ERR: Couldn'g choose prime term\n%!";
    raise Not_found
  with Found_prime_term t -> t


let split_prime_atoms t sa =
  SAtom.fold (fun a (yes, no) -> match a with
    | Comp (t1, Eq, t2) when Term.compare t t1 = 0 || Term.compare t t2 = 0 ->
        SAtom.add a yes, no
    | _ -> yes, SAtom.add a no) sa (SAtom.empty, SAtom.empty)

let aux_corss t t' sa =
  SAtom.fold (fun a acc -> match a with
    | Comp (t1, Eq, t2) ->
        if Term.compare t t1 = 0 then SAtom.add (Comp (t', Eq, t2)) acc
	else if Term.compare t t2 = 0 then SAtom.add (Comp (t', Eq, t1)) acc
	else assert false
    | _ -> assert false) sa SAtom.empty
      

let cross t sa =
  SAtom.fold (fun a acc -> match a with
    | Comp (t1, Eq, t2) ->
        let t' = if Term.compare t t1 = 0 then t2 else t1 in
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

let rec type_of_atom = function
  | True | False    -> None
  | Comp (t, _, _)  -> Some (Term.type_of (unprime_term t))
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
  Cube.simplify_atoms sa


let swts_to_ites at swts sigma =
  let rec sd acc = function
    | [] -> assert false
    | [d] -> acc, d
    | s::r -> sd (s::acc) r in
  let swts, (d, t) = sd [] swts in
  (* assert (d = SAtom.singleton True); *)
  let t = Term.subst sigma (prime_term t) in
  let default = Comp (at, Eq, t) in
  List.fold_left (fun ites (sa, t) ->
    let sa = SAtom.subst sigma (prime_satom sa) in
    let t = Term.subst sigma (prime_term t) in
    Ite (sa, Comp (at, Eq, t), ites)
  ) default swts


let apply_assigns assigns sigma =
  List.fold_left 
    (fun (nsa, terms) (h, gu, _) ->
      let nt = Vea(Elem (h, Glob)) in
      let sa = 
        match gu with
        | UTerm t -> 
          let t = Term.subst sigma t in
          Comp (nt, Eq, prime_term t)
          (* TODO G : Comprendre ici
          begin match t with
            | Arith (t, c) ->
              let nt = Arith (nt, mult_const (-1) c) in
              Comp (nt, Eq, prime_term t)
            | _ -> Comp (nt, Eq, prime_term t)
          end
          *)
        | UCase swts -> swts_to_ites nt swts sigma
      in
      SAtom.add sa nsa, Term.Set.add nt terms)
    (SAtom.empty, Term.Set.empty) assigns

let add_update (sa, st) {up_arr=a; up_arg=lj; up_swts=swts} procs sigma =
  let at = Vea(Access (a, lj)) in
  let ites = swts_to_ites at swts sigma in
  let indexes = Variable.all_arrangements_arity a procs in
  List.fold_left (fun (sa, st) li ->
    let sigma = List.combine lj li in
    SAtom.add (Atom.subst sigma ites) sa,
    Term.Set.add (Vea(Access (a, li))) st
  ) (sa, st) indexes

let apply_updates upds procs sigma =
  List.fold_left 
    (fun acc up -> add_update acc up procs sigma)
    (SAtom.empty, Term.Set.empty) upds

let preserve_terms upd_terms sa =
  let unc = Term.Set.diff (Cube.satom_globs sa) upd_terms in
  Term.Set.fold (fun t acc ->
    SAtom.add (Comp (t, Eq, prime_term t)) acc)
    unc SAtom.empty

let uguard_dnf sigma args tr_args = function
  | [] -> []
  | [j, dnf, _] ->
      let uargs = List.filter (fun a -> not (H.list_mem a tr_args)) args in
      List.map (fun i ->
	List.map (fun sa -> SAtom.subst ((j, i)::sigma) sa) dnf) uargs
  | _ -> assert false


let possible_init args init reqs =
  (** Very incomplete semantic test **)
  not (Cube.inconsistent_set (SAtom.union init reqs)) (* && *)
    (* try Prover.check_guard args init reqs; true *)
    (* with Smt.Unsat _ -> false *)

let possible_guard args all_args tr_args sigma init (reqs,_) ureqs =
  let reqs = SAtom.subst sigma reqs in
  possible_init args init reqs &&
    let t_args_ef = 
      List.fold_left (fun acc p -> 
	try (Variable.subst sigma p) :: acc
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
      let f, s = List.split (Variable.build_subst t pv) in
      List.rev f, List.rev s
      (* List.rev (snd (List.split (build_subst t pv))) *)
    | _::rp, _::rt, _::rpv -> aux rp rt rpv
    | _, [], _ -> [],[]
    | _, _::_, [] -> assert false
  in
  aux procs tr_args Variable.procs

let term_contains_arg z t = 
  let vea_contains_arg = function 
  | Vea.Elem (x, Var)  -> Hstring.equal x z
  | Vea.Access (_, lx) -> Hstring.list_mem z lx
  | _                  -> false
  in 
  match t with 
  | Vea vea -> vea_contains_arg vea
  | Poly(_, ts) -> VMap.exists (fun v _ -> vea_contains_arg v) ts

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
  let d = Variable.all_permutations tr_args procs in
  (* do it even if no arguments *)
  let d = if d = [] then [[]] else d in
  let p_init = prime_satom init in
  List.fold_left (fun acc sigma ->
    if possible_guard procs all_procs tr_args sigma init reqs ureqs then
      let assi, assi_terms = apply_assigns assigns sigma in
      let upd, upd_terms = apply_updates upds all_procs sigma in
      let unchanged = preserve_terms (Term.Set.union assi_terms upd_terms) init in
      let sa = Cube.simplify_atoms_base p_init
      	(SAtom.union unchanged (SAtom.union assi upd)) in
      let sa = abstract_others sa tr_others in
      List.fold_left (fun acc sa ->
        let sa = wrapper_elim_prime p_init sa in
        (* let sa = gauss_elim sa in *)
        let csa = Cube.create_normal sa in
        let sa, nargs = csa.Cube.litterals, csa.Cube.vars in
        (sa, nargs) :: acc)
        acc (Cube.elim_ite_simplify_atoms sa)
    else acc
  ) [] d




let post_inst init all_procs procs { i_reqs = reqs;
				     i_udnfs = udnfs;
				     i_actions = actions;
				     i_touched_terms = touched_terms } =
  if possible_inst_guard procs all_procs init reqs udnfs then
    let p_init = prime_satom init in
    let unchanged = preserve_terms touched_terms init in
    let sa = Cube.simplify_atoms_base p_init (SAtom.union unchanged actions) in
    List.fold_left (fun acc sa ->
      try
        let sa = wrapper_elim_prime p_init sa in
        let csa = Cube.create_normal sa in
        let sa, nargs = csa.Cube.litterals, csa.Cube.vars in
        (sa, nargs) :: acc
      with Stdlib.Exit -> acc)
      [] (Cube.elim_ite_simplify_atoms sa) 
  else []


module HSA : Hashtbl.S with type key = SAtom.t = Hashtbl.Make (SAtom)


module HI = Hashtbl.Make 
  (struct 
  type t = int 
  let equal = (=) 
  let hash x = x end)

let already_seen sa args h =
  let d = Variable.all_permutations args args in
  List.exists (fun sigma ->
    let sa = SAtom.subst sigma sa in
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
	      eprintf "%d : %a\n@." !cpt_f SAtom.print sa
	    else if !cpt_f mod 1000 = 0 then eprintf "%d (%d)@." !cpt_f
	      (List.length to_do + List.length new_td);
	    (* HSA.add h_visited sa (); *)
	    let d = Variable.all_permutations args args in
	    List.iter 
              (fun sigma -> HSA.add h_visited (SAtom.subst sigma sa) ()) d;
	    forward_rec s procs trs (List.rev_append new_td to_do)
        )
  in
  forward_rec s procs trs l;
  h_visited


let var_term_unconstrained sa t =
  SAtom.for_all (function
    | Comp (t1, _, t2) -> Term.compare t t1 <> 0 && Term.compare t t2 <> 0
    | _ -> true) sa

let unconstrained_terms sa = Term.Set.filter (var_term_unconstrained sa)

module MA = Map.Make (Atom)

let lit_abstract = function
  | Comp ((Vea(Elem (x, _)) | Vea(Access (x,_))), _, _) ->
      Smt.Symbol.has_abstract_type x
  | _ -> false

let add_compagnions_from_node all_var_terms sa =
  SAtom.fold (fun a mc ->
    if lit_abstract a then mc
    else
      let rsa = SAtom.remove a sa in
      let unc = unconstrained_terms rsa all_var_terms in 
      let old_comps, old_uncs = 
	try MA.find a mc with Not_found -> SAtom.empty, Term.Set.empty in
      MA.add a (SAtom.union rsa old_comps, Term.Set.union unc old_uncs) mc
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
	  
	  if debug then eprintf "%d : %a@." !cpt_f SAtom.print sa
	  else if !cpt_f mod 1000 = 0 then eprintf "%d (%d)@." !cpt_f
	    (List.length to_do + List.length new_td);
	  (* HI.add h_visited hsa (); *)
	  (* let mc = add_compagnions_from_node all_var_terms sa mc in *)
	  let d = Variable.all_permutations args args in
	  let mc = 
	    List.fold_left (fun mc sigma ->
	      let sa = SAtom.subst sigma sa in
	      HI.add h_visited (SAtom.hash sa) ();
	      add_compagnions_from_node all_var_terms sa mc
	    ) mc d in
	  forward_rec s procs trs mc (List.rev_append new_td to_do)
  in
  forward_rec s procs trs MA.empty l
  

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
        let lsigs = Variable.all_instantiations args lvars in
        List.fold_left (fun conj sigma ->
          let dnf = List.fold_left (fun dnf sa ->
            (* let sa = abs_inf sa in *)
            let sa = SAtom.subst sigma sa in
            try (Cube.simplify_atoms_base SAtom.empty sa) :: dnf
            with Stdlib.Exit -> dnf
          ) [] lsa in
          dnf :: conj
        ) [] lsigs

let rec cdnf_to_dnf_rec acc = function
  | [] ->
      List.rev_map (fun sa ->
                    sa, Variable.Set.elements (SAtom.variables sa)) acc
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


let instance_of_transition { tr_args = tr_args; 
		             tr_reqs = (reqs,_); 
		             tr_name = name;
		             tr_ureq = ureqs;
		             tr_assigns = assigns; 
		             tr_upds = upds; 
		             tr_nondets = nondets } all_procs tr_others sigma =
  let reqs = SAtom.subst sigma reqs in
  let t_args_ef = 
    List.fold_left (fun acc p -> 
      try (Variable.subst sigma p) :: acc
      with Not_found -> p :: acc) [] tr_args in
  let udnfs = uguard_dnf sigma all_procs t_args_ef ureqs in
  let assi, assi_terms = apply_assigns assigns sigma in
  let upd, upd_terms = apply_updates upds all_procs sigma in
  let act = Cube.simplify_atoms (SAtom.union assi upd) in
  let act = abstract_others act tr_others in
  let nondet_terms =
    List.fold_left (fun acc h -> Term.Set.add (Vea(Elem (h, Glob))) acc)
      Term.Set.empty nondets in
  {
    i_reqs = reqs;
    i_udnfs = udnfs;
    i_actions = act;
    i_touched_terms =
      Term.Set.union (Term.Set.union assi_terms nondet_terms) upd_terms
  }


let instantiate_transitions all_procs procs trans = 
  let aux acc {tr_info = tr} =
    let tr_others,others = missing_args procs tr.tr_args in
    let d = Variable.all_permutations tr.tr_args procs in
    (* do it even if no arguments *)
    let d = if d = [] then [[]] else d in
    List.fold_left (fun acc sigma ->
      instance_of_transition tr all_procs tr_others sigma :: acc
    ) acc d
  in
  List.fold_left aux [] trans




let all_var_terms procs {t_globals = globals; t_arrays = arrays} =
  let acc, gp = 
    List.fold_left 
      (fun (acc, gp) g ->
	Term.Set.add (Vea(Elem (g, Glob))) acc, gp
      ) (Term.Set.empty, []) globals
  in
  List.fold_left (fun acc a ->
    let indexes = Variable.all_arrangements_arity a (procs@gp) in
    List.fold_left (fun acc lp ->
      Term.Set.add (Vea(Access (a, lp))) acc)
      acc indexes)
    acc arrays

let search procs init =
  let inst_trans = instantiate_transitions procs procs init.t_trans in
  forward init procs inst_trans (mkinits procs init)

let search_stateless procs init =
  let var_terms = all_var_terms procs init in
  let inst_trans = instantiate_transitions procs procs init.t_trans in
  stateless_forward init procs inst_trans var_terms (mkinits procs init)

let search_only s = assert false
  (* let ex_args =  *)
  (*   match s.t_forward with (_, args, _) :: _ -> args | _ -> assert false in *)
  (* forward s ex_args s.t_trans (mkforward_s s) *)



(********************************************)
(* Check if formula is unreachable on trace *)
(********************************************)

exception Reachable of
    (SAtom.t * transition_info * Variable.subst * SAtom.t) list 

let all_partitions s =
  List.fold_left (fun acc x ->
    [x] :: List.map (fun l -> x :: l) acc) [] (List.rev s)


let mkinits_up_to procs_sets s =
  match procs_sets with
  | [] | [[]] -> mkinits [] s
  | _ ->
    List.fold_left
      (fun acc procs -> List.rev_append (mkinits procs s) acc) [] procs_sets

let above s trace =
  let rec above_rec s acc = function
    | tx :: (_, _, y) :: _ when s.tag = y.tag -> List.rev (tx :: acc)
    | tx :: r -> above_rec s (tx :: acc) r
    | _ -> assert false
  in
  above_rec s [] trace


type possible_result = 
  | Reach of (SAtom.t * transition_info * Variable.subst * SAtom.t) list 
  | Spurious of trace
  | Unreach


let possible_trace ~starts ~finish ~procs ~trace =
  (* eprintf "Possible with %d procs?@." (List.length procs); *)
  let usa = Node.litterals finish in
  let rec forward_rec ls rtrace = match ls, rtrace with
    | _, [] ->
      List.iter (fun (sa, args, hist) ->
          try Prover.reached procs usa sa; raise (Reachable hist)
          with Smt.Unsat _ -> ()
        ) ls;
      Unreach
    | [], (_, _, s) ::_ ->
      Spurious (above s trace)
    | _, (tr, _, _) :: rest_trace ->
        let nls =
	  if List.length tr.tr_args > List.length procs then []
	  else
           List.fold_left (fun acc sigma ->
            let itr = instance_of_transition tr procs [] sigma in
            List.fold_left (fun acc (sa, args, hist) ->
              List.fold_left (fun acc (nsa, nargs) ->
                let new_hist = (sa, tr, sigma, nsa) :: hist in
                (* eprintf "%a\n@." SAtom.print nsa;     *)
                try Prover.reached procs usa nsa; raise (Reachable new_hist)
                with Smt.Unsat _ -> (nsa, nargs, new_hist) :: acc
              ) acc (post_inst sa args procs itr)
            ) acc ls
           ) [] (Variable.all_permutations tr.tr_args procs)
        in
        forward_rec nls rest_trace
  in
  try
    let init = List.map (fun (isa, iargs)-> isa, iargs, []) starts in
    forward_rec init trace
  with
    | Reachable hist -> Reach hist
  

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
	type t = (transition_info * Hstring.t list * t_system) list
	let equal = equal_trace_woargs
	let hash = Hashtbl.hash_param 50 100
      end)
			       

let procs_on_trace trace =
  let all_procs_set = 
    List.fold_left (fun acc (_, procs_t, n) ->
      List.fold_left (fun acc p -> Hstring.HSet.add p acc) acc
	(List.rev_append procs_t
    (Variable.Set.elements (SAtom.variables (Node.litterals n))))
    (* (Node.variables n)) *)
      ) Hstring.HSet.empty trace
  in
  Hstring.HSet.elements all_procs_set

let reachable_on_trace_from_init s unsafe trace =
  let all_procs = procs_on_trace  trace in
  let proc_sets = (* all_partitions *) [all_procs] in
  let inits = mkinits_up_to proc_sets s in
  match possible_trace ~starts:inits ~finish:unsafe ~procs:all_procs ~trace with
  | Spurious _ | Unreach -> Unreach
  | Reach _  as r -> r

let reachable_on_all_traces_from_init s unsafe trace =
  let all_procs = procs_on_trace trace in
  let proc_sets = (* all_partitions *) [all_procs] in
  let inits = mkinits_up_to proc_sets s in
  possible_trace ~starts:inits ~finish:unsafe ~procs:all_procs ~trace

let possible_history s =
  let trace = s.from in
  let all_procs = procs_on_trace trace in
  let iargs, isa = Node.variables s, Node.litterals s in 
  possible_trace ~starts:[isa, iargs] ~finish:(Node.origin s)
                 ~procs:all_procs ~trace

		 
let spurious s =
  match possible_history s with
    | Unreach | Spurious _ -> true
    | Reach hist -> false


let spurious_error_trace system s =
  match reachable_on_all_traces_from_init system (Node.origin s) s.from with
  | Spurious _ -> assert false
  | Unreach -> true
  | Reach hist -> false


let spurious_due_to_cfm system s =
  match reachable_on_trace_from_init system (Node.origin s) s.from with
  | Unreach | Spurious _ -> true
  | Reach hist -> false

let replay_history system s =
  match reachable_on_trace_from_init system (Node.origin s) s.from with
  | Unreach | Spurious _ -> None
  | Reach hist -> Some hist


let conflicting_from_trace s trace =
  let all_procs = procs_on_trace trace in
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
