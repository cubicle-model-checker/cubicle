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

let SA = Set.Make(Atom)

let bad_candidates = ref Cubetrie.empty

let register_bad system cand trace =
  let cvars = Node.variables cand in
  assert (cand.Node.kind = Node.Approx);
  let bads =
    List.fold_left 
      (fun acc sigma ->
       Cubetrie.add_array (Node.array (Cube.subst sigma cand.Node.cube)) () acc)
      !bad_candidates (Variable.all_permutations cvars cvars)
  in
  bad_candidates := !bads;
  match trace with
  | [] -> ()
  | _ ->
     List.iter (fun sa -> bad_candidates := sa :: !bad_candidates)
               (Forward.conflicting_from_trace system trace)


let cube_same c1 c2 = ArrayAtom.equal c1.Cube.array c2.Cube.array

let rec remove_bad_candidates sys faulty candidates =
  let trace = faulty.Node.from in
  let cand = Node.origin faulty in
  let nc = 
    List.fold_left 
      (fun acc c' ->
	if cube_same cand.Node.cube c'.Node.cube
	then
	  (* raise UNSAFE if we try to remove a candidate 
	     which is an unsafe property *)
	  if List.exists (cube_same c'.Node.cube) sys.unsafe then
	    raise (Safety.Unsafe faulty)
	  else (register_bad c' trace; acc)
        (* TODO apres avoir changé forward *)                 
        else if Forward.reachable_on_trace_from_init system trace <> Forward.Unreach
	then
          (register_bad c' []; acc)
	else c'::acc)
      [] candidates in
  List.rev nc


module SSAtoms = Set.Make(SAtom)

let nb_arrays_sa sa =
  SAtom.fold (fun a n -> match a with
    | Atom.Comp (Elem _, _, Elem _) -> n
    | Atom.Comp (Elem _, _, Access _) | Atom.Comp (Access _, _, Elem _) -> n + 1
    | Atom.Comp (Access _, _, Access _) -> n + 2
    | _ -> n
  ) sa 0

let nb_arrays s = nb_arrays_sa (snd s.t_unsafe)

let nb_neq s =
  SAtom.fold (fun a n -> match a with
    | Atom.Comp (_, Neq, _) -> n + 1
    | _ -> n
  ) (snd s.t_unsafe) 0


let nb_arith s =
  SAtom.fold (fun a n -> match a with
    | Atom.Comp (_, (Le|Lt), _)
    | Atom.Comp (Arith _, _, _) 
    | Atom.Comp (_, _, Arith _) 
    | Atom.Comp (Const _, _, _) 
    | Atom.Comp (_, _, Const _) -> n + 1
    | _ -> n
  ) (snd s.t_unsafe) 0

let respect_finite_order =
  SAtom.for_all (function
    | Atom.Comp (Elem (x, Var), Le, Elem (y, Var)) ->
        Hstring.compare x y <= 0
    | Atom.Comp (Elem (x, Var), Lt, Elem (y, Var)) ->
        Hstring.compare x y < 0
    | _ -> true
  )

let hsort = Hstring.make "Sort"
let hhome = Hstring.make "Home"

let sorted_variables sa =
  let procs = Cube.args_of_atoms sa in
  List.for_all (fun p ->
    SAtom.exists (function 
      | Atom.Comp (Access (s, [x]), _, _) 
        when Hstring.equal s hsort && Hstring.equal x p -> true
      | _ -> false) sa) procs

let isolate_sorts =
  SAtom.partition (function 
    | Atom.Comp (Access (s, _), _, _) -> Hstring.equal s hsort
    | Atom.Comp (Elem (h, Glob), _, _) -> Hstring.equal h hhome
    | _ -> false)


let reattach_sorts sorts sa =
  let procs = Cube.args_of_atoms sa in
  SAtom.fold (fun a sa -> match a with
    | Atom.Comp (Access (s, [x]), _, _) 
        when Hstring.equal s hsort && Hstring.list_mem x procs ->
        SAtom.add a sa
    | Atom.Comp (Elem (h, Glob), _, Elem (x, Var))
    | Atom.Comp (Elem (x, Var), _, Elem (h, Glob)) 
        when Hstring.equal h hhome && Hstring.list_mem x procs ->
        SAtom.add a sa
    | _ -> sa) sorts sa


let proc_present p a sa =
  let rest = SAtom.remove a sa in
  SAtom.exists (function
    | Atom.Comp (Elem (h, Var), _, _)
    | Atom.Comp (_, _, Elem (h, Var)) when Hstring.equal h p -> true
    | _ -> false) rest

let useless_candidate sa =
  let open Atom in
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

(*****************************************)
(* Potential approximations for a node s *)
(*****************************************)

let approx_arith a = match a with
  | Atom.Comp (t, Eq, Const c) ->
     begin
       match Cube.const_sign c with
       | None | Some 0 -> a
       | Some n ->
	  let zer = Const (Cube.add_constants c (Cube.mult_const (-1) c)) in
	  if n < 0 then Atom.Comp (t, Lt, zer)
	  else Atom.Comp (zer, Lt, t)
     end
  | _ -> a

let approximations ({ t_unsafe = (args, sa) } as s) =
    let sorts_sa, sa = isolate_sorts sa in
    let init = 
      SAtom.fold (fun a acc ->
        if useless_candidate (SAtom.singleton a) || lit_non_cfm a 
	then acc
        else SSAtoms.add (SAtom.singleton a) acc)
        sa SSAtoms.empty in
    (* All subsets of sa of relevant size *)
    let parts =
      SAtom.fold (fun a acc ->
	let a = approx_arith a in 
        if useless_candidate (SAtom.singleton a) then acc
        else if lit_non_cfm a then acc
        else
          SSAtoms.fold (fun sa' acc ->
            let nsa = SAtom.add a sa' in
            let nargs = Cube.args_of_atoms nsa in
            if List.length nargs > enumerative then acc
            else if SAtom.cardinal nsa > enumerative + 1 then acc
            else SSAtoms.add nsa acc
          ) acc acc
      ) sa init
    in
    (* Filter non interresting candidates *)
    let parts = SSAtoms.fold (fun sa' acc ->
      if SAtom.equal sa' sa then acc
      (* Heuristic : usefull for flash *)
      else if SAtom.cardinal sa' >= 3 && nb_arrays_sa sa' > enumerative - 1 then acc
      (* else if List.length (Cube.args_of_atoms sa') > SAtom.cardinal sa' then acc *)
      else
        let sa' = reattach_sorts sorts_sa sa' in
        if SAtom.equal sa' sa then acc
        else
        let sa', (args', _) = Cube.proper_cube sa' in
        if List.exists (fun sa -> SAtom.subset sa' sa || SAtom.subset sa sa')
          !bad_candidates then acc
        else
          let ar' = ArrayAtom.of_satom sa' in
          decr cpt_approx;
          let s' = 
            { s with
	      t_from = [];
	      t_unsafe = args', sa';
	      t_arru = ar';
	      t_alpha = ArrayAtom.alpha ar' args';
	      t_deleted = false;
	      t_nb = !cpt_approx;
	      t_nb_father = -1;
            } in
          s' :: acc
    ) parts []
    in
    (* Sorting heuristic of approximations with most general ones first *)
    List.fast_sort (fun s1 s2 ->
      let c = Pervasives.compare (Cube.card_system s1) (Cube.card_system s2) in
      if c <> 0 then c
      else 
        let c =
          Pervasives.compare (Cube.size_system s1) (Cube.size_system s2) in
        if c <> 0 then c
        else 
          let c = Pervasives.compare (nb_neq s2) (nb_neq s1) in
          if c <> 0 then c
          else
            Pervasives.compare (nb_arrays s1) (nb_arrays s2)
          (* if c <> 0 then c *)
          (* else *)
          (*   SAtom.compare (snd s1.t_unsafe) (snd s2.t_unsafe) *)
    ) parts

(* TODO : approx trees or bdds *)

let keep n l =
  let rec aux acc n l = match l,n with
    | [], _ | _, 0 -> List.rev acc
    | x::r, _ -> aux (x::acc) (n-1) r in
  aux [] n l

let subsuming_candidate s =
  let approx = approximations s in
  let approx = if max_cands = -1 then approx else keep max_cands approx in
  if verbose > 0 && not quiet then 
    eprintf "Checking %d approximations:@." (List.length approx);
  Oracle.first_good_candidate approx


let good n =
  if not do_brab then None
  else
    match n.Node.kind with
    | Approx ->
    (* It's useless to look for approximations of an approximation *)
       None
    | Node ->
       subsuming_candidate n
