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

let bad_candidates = ref []

let rec origin s = match s.t_from with
  | [] -> s
  | (_,_, p)::_ ->
      if p.t_nb < 0 then p
      else origin p

let add_bad_candidate ({t_unsafe = args, _; t_alpha = a_args, ar } as s) trace =
  List.iter (fun sigma ->
    bad_candidates := 
      fst 
        (Cube.proper_cube
           (ArrayAtom.to_satom (ArrayAtom.apply_subst sigma ar))) ::
      !bad_candidates
  ) (all_permutations a_args args);
  match trace with
    | Some tr ->
        List.iter (fun sa -> bad_candidates := sa :: !bad_candidates)
          (Forward.conflicting_from_trace s tr);
    | None -> ()

let rec remove_cand s faulty candidates uns =
  let trace = List.map (fun (tr, args, _) -> tr, args) faulty.t_from in 
  let nc = 
    List.fold_left 
      (fun acc s' -> 
	(* if fixpoint ~invariants:[] ~visited:[s'] s then acc *)
	
	if (* None <> fixpoint ~invariants:[] ~visited:[s'] s || *)
	   (* List.exists  *)
	   (* (fun (_,_,s) ->  *)
	   (*   None <> fixpoint ~invariants:[] ~visited:[s'] s) s.t_from *)
           ArrayAtom.equal s.t_arru s'.t_arru
	then
	  (* raise UNSAFE if we try to remove a candidate 
	     which is an unsafe property *)
	  if List.exists (fun s -> ArrayAtom.equal s.t_arru s'.t_arru) uns then
	    raise (Search.Unsafe s)
	  else (add_bad_candidate s' (Some trace); acc)
        else if Forward.reachable_on_trace s' trace then 
          (add_bad_candidate s' None; acc)
	else s'::acc)
      [] candidates in
  List.rev nc


let search_backtrack_brab search invariants uns =
  let candidates = ref [] in
  let rec search_rec uns =
    try
      search ~invariants ~visited:[] ~forward_nodes:[] ~candidates uns
    with
      | Search.Unsafe faulty ->
	  (* FIXME Bug when search is parallel *)
	  let o = origin faulty in
	  if not quiet then
            eprintf "The node %d = %a is UNSAFE@." o.t_nb Pretty.print_system o;
	  if o.t_nb >= 0 then raise (Search.Unsafe faulty);
          if not quiet then eprintf "%d used candidates :@." (List.length !candidates);
          if not quiet then 
            List.iter (fun s ->
              eprintf "   %a\n@." Pretty.print_system s) !candidates;
          candidates := remove_cand o faulty !candidates uns;
          if not quiet then eprintf "%d bad candidates :@." (List.length !bad_candidates);
          if not quiet then 
            List.iter (fun sa ->
              eprintf "   %a\n@." Pretty.print_cube sa) !bad_candidates;
          search_rec uns
  in
  search_rec uns


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
  

let approximations =
  let forward_procs = Forward.procs_from_nb enumerative in
  let cpt = ref 0 in
  fun ({ t_unsafe = (args, sa) } as s) ->
    let init = 
      SAtom.fold (fun a acc ->
        if Forward.useless_candidate (SAtom.singleton a) then acc
        else SSAtoms.add (SAtom.singleton a) acc)
        sa SSAtoms.empty in
    let parts =
      SAtom.fold (fun a acc ->
        if Forward.useless_candidate (SAtom.singleton a) then acc
        else
          SSAtoms.fold (fun sa' acc ->
            let nsa = SAtom.add a sa' in
            let nargs = Cube.args_of_atoms nsa in
            if List.length nargs > enumerative then acc
            else if SAtom.cardinal nsa > 3 then acc
            else SSAtoms.add nsa acc
          ) acc acc
      ) sa init
    in
    let parts = SSAtoms.fold (fun sa' acc ->
      if SAtom.equal sa' sa then acc
      (* Heuristic : usefull for flash *)
      else if SAtom.cardinal sa' >= 3 && nb_arrays_sa sa' > 1 then acc
      else
        let sa', (args', _) = Cube.proper_cube sa' in
        if List.exists (fun sa -> SAtom.subset sa' sa || SAtom.subset sa sa')
          !bad_candidates then acc
        else
          let d = List.rev (all_permutations args' forward_procs) in
          (* let d = List.rev (all_permutations args' args') in *)
          (* let d = [List.combine args' args'] in *)
          (* keep list.rev in order for the first element of perm to be
             a normalized cube as we will keep this only one if none of
             perm can be disproved *)
          let perms = List.fold_left (fun p sigma ->
            let sa' = subst_atoms sigma sa' in
            let ar' = ArrayAtom.of_satom sa' in
            decr cpt;
            let s' = 
              { s with
	        t_from = [];
	        t_unsafe = args', sa';
	        t_arru = ar';
	        t_alpha = ArrayAtom.alpha ar' args';
	        t_deleted = false;
	        t_nb = !cpt;
	        t_nb_father = -1;
              } in
            s' :: p) [] d
          in
          perms :: acc
    ) parts []
    in
    List.fast_sort (fun l1 l2 ->
      let s1 = List.hd l1 in
      let s2 = List.hd l2 in
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

(* TODO : approx trees *)

let subsuming_candidate s =
  let approx = approximations s in
  Enumerative.smallest_to_resist_on_trace approx


let brab search invariants uns =
    let procs = Forward.procs_from_nb enumerative in
    eprintf "STATEFULL ENUMERATIVE FORWARD :\n-------------\n@.";
    Enumerative.search procs (List.hd uns);

    eprintf "-------------\n@.";
    
    if only_forward then exit 0;
    search_backtrack_brab search invariants uns
