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
open Types

module SA = SAtom

let bad_candidates = ref Cubetrie.empty

let non_cfm_literals = ref SA.empty

let contains_non_cfm s = not (SA.is_empty (SA.inter s !non_cfm_literals))
let lit_non_cfm a = SA.mem a !non_cfm_literals


let register_bad system cand trace =
  let cvars = Node.variables cand in
  assert (cand.kind = Approx);
  let bads =
    List.fold_left 
      (fun acc sigma ->
       Cubetrie.add_array (Cube.subst sigma cand.cube).Cube.array () acc)
      !bad_candidates (Variable.all_permutations cvars cvars)
  in
  bad_candidates := bads;
  match trace with
  | [] -> ()
  | _ ->
  let bads =
    List.fold_left 
      (fun acc sa ->
       Cubetrie.add (SAtom.elements sa) () acc)
      !bad_candidates (Forward.conflicting_from_trace system trace)
  in
  bad_candidates := bads


let remove_non_cfm_cand system candidates =
  List.filter (fun sc ->
	       if contains_non_cfm (Node.litterals sc) then false 
	       else (register_bad system sc []; true))
              candidates


let node_same n1 n2 = ArrayAtom.equal (Node.array n1) (Node.array n2)

let rec remove_bad_candidates sys faulty candidates =
  let trace = faulty.from in
  let cand = Node.origin faulty in
  let nc = 
    List.fold_left 
      (fun acc c' ->
	if node_same cand c'
	then
	  (* raise UNSAFE if we try to remove a candidate 
	     which is an unsafe property *)
	  if List.exists (node_same c') sys.t_unsafe then
	    raise (Safety.Unsafe faulty)
	  else (register_bad sys c' trace; acc)
        else 
          if Forward.spurious_due_to_cfm sys faulty then
            (* Find out if bactrack is due to crash failure model, in which
               case record literals that do not respect CMF model *)
            begin
              non_cfm_literals := SA.union (Node.litterals cand) !non_cfm_literals;
              if not quiet && verbose > 0 then 
                eprintf "Non CFM literals = %a@." SAtom.print !non_cfm_literals;
              remove_non_cfm_cand sys acc
            end
          else
            (* remove candidates that are reachable on the same trace modulo
               renaming of parameters *)
            if Forward.reachable_on_trace_from_init sys c' trace <> 
                 Forward.Unreach
	    then
              (register_bad sys c' []; acc)
	    else begin
              (* This candidate seems ok, reset its delete flag *)
              c'.deleted <- false;
              c'::acc
            end
      ) [] candidates in
  List.rev nc


module SSAtoms = Set.Make(SAtom)

let nb_arrays_sa sa =
  SAtom.fold (fun a n -> match a with
    | Atom.Comp (Elem _, _, Elem _) -> n
    | Atom.Comp (Elem _, _, Access _) | Atom.Comp (Access _, _, Elem _) -> n + 1
    | Atom.Comp (Access _, _, Access _) -> n + 2
    | _ -> n
  ) sa 0

let nb_arrays s = nb_arrays_sa (Node.litterals s)

let nb_neq s =
  SAtom.fold (fun a n -> match a with
    | Atom.Comp (_, Neq, _) -> n + 1
    | _ -> n
  ) (Node.litterals s) 0


let nb_arith s =
  SAtom.fold (fun a n -> match a with
    | Atom.Comp (_, (Le|Lt), _)
    | Atom.Comp (Arith _, _, _) 
    | Atom.Comp (_, _, Arith _) 
    | Atom.Comp (Const _, _, _) 
    | Atom.Comp (_, _, Const _) -> n + 1
    | _ -> n
  ) (Node.litterals s) 0

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
  let procs = SAtom.variables sa in
  Variable.Set.for_all (fun p ->
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
  let procs = Variable.Set.elements (SAtom.variables sa) in
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
      (* Smt.Symbol.has_type_proc x ||  *)
        (enumerative <> -1 && Smt.Symbol.has_abstract_type x)
        (* (Hstring.equal (snd (Smt.Symbol.type_of x)) Smt.Type.type_real) || *)
        (* (Hstring.equal (snd (Smt.Symbol.type_of x)) Smt.Type.type_int) *)

    | _ -> false) sa


let arith_atom = function
  | Atom.Comp ((Arith _), _, _) | Atom.Comp (_, _, (Arith _)) 
  | Atom.Comp ((Const _), _, _) | Atom.Comp (_, _, (Const _)) -> true
  | _ -> false


let cube_likely_bad c = (* heuristic *)
  Cubetrie.mem_array_poly c.Cube.array !bad_candidates

let cube_known_bad c = 
  try Cubetrie.iter_subsumed (fun _ -> raise Exit)
          (Array.to_list c.Cube.array) !bad_candidates;
      false
  with Exit -> true


(*****************************************)
(* Potential approximations for a node s *)
(*****************************************)

let approx_arith a = match a with
  | Atom.Comp (t, Eq, Const c) ->
     begin
       match const_sign c with
       | None | Some 0 -> a
       | Some n ->
	  let zer = Const (add_constants c (mult_const (-1) c)) in
	  if n < 0 then Atom.Comp (t, Lt, zer)
	  else Atom.Comp (zer, Lt, t)
     end
  | _ -> a

let approximations s =
  let args, sa = Node.variables s, Node.litterals s in
  let sorts_sa, sa = isolate_sorts sa in
  (* Heuristics for generating candidates *)
  let max_procs = enumerative in
  let max_literals = max 2 (candidate_heuristic + 1) in
  let max_ratio_arrays_after = (3, candidate_heuristic - 1) in
  let init = 
    SAtom.fold 
      (fun a acc ->
       if useless_candidate (SAtom.singleton a) || lit_non_cfm a 
       then acc
       else SSAtoms.add (SAtom.singleton a) acc)
      sa SSAtoms.empty in
  (* All subsets of sa of relevant size *)
  let parts =
    SAtom.fold
      (fun a acc ->
       let a = approx_arith a in
       if useless_candidate (SAtom.singleton a) then acc
       else if not abstr_num && arith_atom a then acc
       else if lit_non_cfm a then acc
       else
         SSAtoms.fold
           (fun sa' acc ->
            let nsa = SAtom.add a sa' in
            if Variable.Set.cardinal (SAtom.variables nsa) > max_procs then
              acc
            else if SAtom.cardinal nsa > max_literals then acc
            else SSAtoms.add nsa acc
           ) acc acc
      ) sa init
  in
  (* Filter non interresting candidates *)
  let parts =
    SSAtoms.fold
      (fun sa' acc ->
       if SAtom.equal sa' sa then acc
       (* Heuristic : usefull for flash *)
       else if SAtom.cardinal sa' >= fst max_ratio_arrays_after &&
                 nb_arrays_sa sa' > snd max_ratio_arrays_after then acc
       (* else if List.length (Cube.args_of_atoms sa') > SAtom.cardinal sa' then
               acc *)
       else
         let sa' = reattach_sorts sorts_sa sa' in
         if SAtom.equal sa' sa then acc
         else
           let c = Cube.create_normal sa' in
           if cube_known_bad c || cube_likely_bad c then acc
           else 
             let n = Node.create ~kind:Approx ~hist:(Some s) c in
             n :: acc
      ) parts []
  in
  (* Sorting heuristic of approximations with most general ones first *)
  List.fast_sort
    (fun s1 s2 ->
       let c = Pervasives.compare (Node.dim s1) (Node.dim s2) in
     if c <> 0 then c
     else 
     let c = Pervasives.compare (Node.size s1) (Node.size s2) in
       if c <> 0 then c
       else 
         let c = Pervasives.compare (nb_neq s2) (nb_neq s1) in
         if c <> 0 then c
         else
           Pervasives.compare (nb_arrays s1) (nb_arrays s2)
         (* if c <> 0 then c *)
         (* else *)
         (*   SAtom.compare (Node.litterals s1) (Node.litterals s1) *)
    ) parts
    
(* TODO : approx trees or bdds *)

let keep n l =
  let rec aux acc n l = match l,n with
    | [], _ | _, 0 -> List.rev acc
    | x::r, _ -> aux (x::acc) (n-1) r in
  aux [] n l



module type S = sig
    val good : Node.t -> Node.t option
    val all_goods : Node.t -> Node.t list
end

module Make ( O : Oracle.S ) : S = struct

  let subsuming_candidate s =
    let approx = approximations s in
    let approx = if max_cands = -1 then approx else keep max_cands approx in
    if verbose > 0 && not quiet then 
      begin
	eprintf "Checking %d approximations:@." (List.length approx);
      end;
    O.first_good_candidate approx


  let good n = match n.kind with
    | Approx ->
       (* It's useless to look for approximations of an approximation *)
       None
    | _ ->
      if approx_history && n.heuristic < hist_threshhold
      then None else
        subsuming_candidate n

  let all_goods s =
    let approx = approximations s in
    let approx = if max_cands = -1 then approx else keep max_cands approx in
    if verbose > 0 && not quiet then 
      eprintf "Checking %d approximations:@." (List.length approx);
    O.all_good_candidates approx

end


module GrumpyOracle : Oracle.S = struct

  let init ?(bwd=[]) _ = ()
  let first_good_candidate _ =
    failwith "You should not call Grumpy Oracle."
  let all_good_candidates _ =
    failwith "You should not call Grumpy Oracle."

end

module GrumpyApprox : S = struct

  let good _ = None
  let all_goods _ = []

end


let select_oracle =
  if do_brab then
    (module Enumerative : Oracle.S)
  else
    (module GrumpyOracle : Oracle.S)

module SelectedOracle : Oracle.S = (val select_oracle)



let select_approx =
  if do_brab then (module Make(SelectedOracle) : S)
  else (module GrumpyApprox)

module Selected : S = (val select_approx)
