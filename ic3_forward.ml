open Format
open Options
open Ast
open Types
open Atom
open Pervasives

module H = Hstring

type inst_trans =
    {
      i_reqs : SAtom.t;
      i_udnfs : SAtom.t list list;
      i_actions : SAtom.t;
      i_touched_terms : Term.Set.t;
      i_args : Variable.t list;
    }

let prime_h h =
  Hstring.make ((Hstring.view h)^"@0")

let rec prime_term t = match t with
  | Elem (e, Glob) -> Elem (prime_h e, Glob)
  | Arith (x, c) -> Arith (prime_term x, c)
  (* | Access (a, x, Glob) -> Access (prime_h a, prime_h x, Glob) *)
  | Access (a, lx) -> Access (prime_h a, lx)
  | _ -> t

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

let uguard_dnf sigma args tr_args = function
  | [] -> []
  | [j, dnf] ->
      let uargs = List.filter (fun a -> not (H.list_mem a tr_args)) args in
      List.map (fun i ->
	List.map (fun sa -> SAtom.subst ((j, i)::sigma) sa) dnf) uargs
  | _ -> assert false

let swts_to_ites at swts sigma =
  let rec sd acc = function
    | [] -> assert false
    | [d] -> acc, d
    | s::r -> sd (s::acc) r in
  let swts, (d, t) = sd [] swts in
  (* assert (d = SAtom.singleton True); *)
  let t = Term.subst sigma t in
  let at = prime_term at in
  let default = Comp (at, Eq, t) in
  List.fold_left (fun ites (sa, t) ->
    let sa = SAtom.subst sigma sa in
    let t = Term.subst sigma t in
    Ite (sa, Comp (at, Eq, t), ites)
  ) default swts


let apply_assigns assigns sigma =
  List.fold_left 
    (fun (nsa, terms) (h, gu) ->
      let nt = Elem (h, Glob) in
      let sa = 
        match gu with
        | UTerm t -> 
           let t = Term.subst sigma t in
	   let nt = Elem (prime_h h, Glob) in
	   Comp (nt, Eq, t)
        | UCase swts -> 
	  swts_to_ites nt swts sigma
      in
      SAtom.add sa nsa, Term.Set.add nt terms)
    (SAtom.empty, Term.Set.empty) assigns

let add_update (sa, st) {up_arr=a; up_arg=lj; up_swts=swts} procs sigma =
  let at = Access (a, lj) in
  let ites = swts_to_ites at swts sigma in
  let indexes = Variable.all_arrangements_arity a procs in
  List.fold_left (fun (sa, st) li ->
    let sigma = List.combine lj li in
    SAtom.add (Atom.subst sigma ites) sa,
    Term.Set.add (Access (a, li)) st
  ) (sa, st) indexes

let apply_updates upds procs sigma =
  List.fold_left 
    (fun acc up -> add_update acc up procs sigma)
    (SAtom.empty, Term.Set.empty) upds

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

let instance_of_transition { tr_args = tr_args; 
		             tr_reqs = reqs; 
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
  (* Format.eprintf "[Instance of trans] %a -> %a : %a @." *)
  (*   Variable.print_subst sigma Variable.print_vars tr_args *)
  (*   Variable.print_vars t_args_ef; *)
  let udnfs = uguard_dnf sigma all_procs t_args_ef ureqs in
  (* List.iter ( *)
  (*   fun (h, gu) -> *)
  (*     Format.eprintf "h : %a@." Hstring.print h; *)
  (*     match gu with  *)
  (* 	| UTerm t -> Format.eprintf "gu : %a@." Term.print t *)
  (* 	| UCase swts -> List.iter *)
  (* 	  ( *)
  (* 	    fun (sa, t) -> *)
  (* 	      Format.eprintf "| %a : %a@." (SAtom.print_sep "&&") sa Term.print t *)
  (* 	  ) swts *)
  (* ) assigns; *)
  let assi, assi_terms = apply_assigns assigns sigma in
  (* Format.eprintf "[Assi]%a@." (SAtom.print_sep "&&") assi; *)
  let upd, upd_terms = apply_updates upds all_procs sigma in
  let act = Cube.simplify_atoms (SAtom.union assi upd) in
  let act = abstract_others act tr_others in
  (* Format.eprintf "[Act]%a@." (SAtom.print_sep "&&") act; *)
  let nondet_terms =
    List.fold_left (fun acc h -> Term.Set.add (Elem (h, Glob)) acc)
      Term.Set.empty nondets in
  {
    i_reqs = reqs;
    i_udnfs = udnfs;
    i_actions = act;
    i_touched_terms =
      Term.Set.union (Term.Set.union assi_terms nondet_terms) upd_terms;
    i_args = t_args_ef;
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

let rec prime_match_satom sa st =
  let rec prime_match_atom a = match a with
    | True | False -> a
    | Comp (t1, op, t2) -> 
      let t1 = if Term.Set.mem t1 st then prime_term t1
        else t1 in
      let t2 = if Term.Set.mem t2 st then prime_term t2
        else t2 in
      Comp (t1, op, t2)
    | Ite (sa, a1, a2) -> 
      Ite (sa,
	   prime_match_atom a1,
	   prime_match_atom a2)
  in
  SAtom.fold (
    fun a acc -> 
      let pa = 
	if is_prime_atom a then a
	else prime_match_atom a
      in
      SAtom.add pa acc
  ) sa SAtom.empty
