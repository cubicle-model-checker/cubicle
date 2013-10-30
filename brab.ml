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
  let trace = faulty.t_from in 
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
        else if Forward.reachable_on_trace_from_init s' trace <> None
                (* Enumerative.smallest_to_resist_on_trace (ref 0) [s'] = [] *)
	then 
          (add_bad_candidate s' None; acc)
	else s'::acc)
      [] candidates in
  List.rev nc


let search_backtrack_brab search invariants procs uns =
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
          
          (* Enumerative.replay_trace_and_expand procs faulty; *)
          
          candidates := remove_cand o faulty !candidates uns;
          (* candidates := []; *)

          if verbose > 0 && not quiet then begin
            eprintf "%d used candidates :@." (List.length !candidates);
            List.iter (fun s ->
              eprintf "   %a\n@." Pretty.print_system s) !candidates;
            eprintf "%d bad candidates :@." (List.length !bad_candidates);
            List.iter (fun sa ->
              eprintf "   %a\n@." Pretty.print_cube sa) !bad_candidates;
          end;

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


(*****************************************)
(* Potential approximations for a node s *)
(*****************************************)

let cpt_approx = ref 0

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
        if Forward.useless_candidate (SAtom.singleton a) then acc
        else SSAtoms.add (SAtom.singleton a) acc)
        sa SSAtoms.empty in
    (* All subsets of sa of relevant size *)
    let parts =
      SAtom.fold (fun a acc ->
	let a = approx_arith a in 
        if Forward.useless_candidate (SAtom.singleton a) then acc
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
	      t_card = AtLeast (List.length args');
	      t_arru = ar';
	      t_alpha = ArrayAtom.alpha ar' args';
	      t_deleted = false;
	      t_nb = !cpt_approx;
	      t_nb_father = -1;
	      t_refine = false;
	      t_spurious = false;
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

(* TODO : approx trees *)

let keep n l =
  let rec aux acc n l = match l,n with
    | [], _ | _, 0 -> List.rev acc
    | x::r, _ -> aux (x::acc) (n-1) r in
  aux [] n l

let subsuming_candidate s =
  let approx = approximations s in
  (* let approx = keep 70 approx in *)
  if verbose > 0 && not quiet then 
    eprintf "Checking %d approximations:@." (List.length approx);
  Enumerative.smallest_to_resist_on_trace cpt_approx approx


(**************************************************************)
(* Backward reachability with approximations and backtracking *)
(**************************************************************)
    
let brab search invariants uns =
  let low = if brab_up_to then 1 else enumerative in
  for i = enumerative downto low do
    let procs = Forward.procs_from_nb i in
    eprintf "STATEFULL ENUMERATIVE FORWARD [%d procs]:\n-------------\n@." i;

    Enumerative.search procs (List.hd uns);
    
    eprintf "-------------\n@.";
  done;

  if only_forward then exit 0;
  let procs = Forward.procs_from_nb enumerative in
  search_backtrack_brab search invariants procs uns
