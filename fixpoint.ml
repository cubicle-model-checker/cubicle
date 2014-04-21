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
open Util
open Ast
open Types

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
      fun s ->
	eprintf "FIX:    %a@." Node.print s

end





(* TODO ici *)

(********************************************************)
(* Incremental fixpoint check : s => \/_{p \in nodes} p *)
(********************************************************)



exception Fixpoint of int list


module FixpointList : sig

  val pure_smt_check : Node.t -> Node.t list -> int list option

  val check : Node.t -> Node.t list -> int list option

end = struct

  let check_fixpoint ?(pure_smt=false) n visited =
    Prover.assume_goal n;
    let n_array = n.cube.Cube.array in
    let nodes = 
      List.fold_left
        (fun nodes vis_n ->
         let vis_cube = vis_n.cube in
         let d = Instantiation.relevant ~of_cube:vis_cube ~to_cube:n.cube in
         List.fold_left
	   (fun nodes ss ->
	    let vis_renamed = ArrayAtom.apply_subst ss vis_cube.Cube.array in
	    if not pure_smt && ArrayAtom.subset vis_renamed n_array then
	        raise (Fixpoint [vis_n.tag])
	    (* Heuristic : throw away nodes too much different *)
	    (* else if ArrayAtom.nb_diff pp anp > 2 then nodes *)
	    (* line below useful for arith : ricart *)
	    else if not pure_smt &&
                    Cube.inconsistent_array
                      (ArrayAtom.union vis_renamed n_array) then nodes
	    else if ArrayAtom.nb_diff vis_renamed n_array > 1 then
              (vis_n, vis_renamed)::nodes
	    else (Prover.assume_node vis_n vis_renamed; nodes)
	   ) nodes d
        ) [] visited
    in
    TimeSort.start ();
    let nodes = 
      List.fast_sort 
        (fun (n1, a1) (n2, a2) -> ArrayAtom.compare_nb_common n_array a1 a2) 
        nodes 
    in
    TimeSort.pause ();
    List.iter (fun (vn, ar_renamed) -> Prover.assume_node vn ar_renamed) nodes


  let easy_fixpoint s nodes =
    if delete && (s.deleted || Node.has_deleted_ancestor s)
    then Some []
    else
      let db = ref None in
      let ars = Node.array s in
      ignore (List.exists 
	        (fun sp -> 
		 if ArrayAtom.subset (Node.array sp) ars then
		 begin db := Some [sp.tag]; true end
		 else false
                ) nodes);
      !db

  let hard_fixpoint s nodes =
    try
      check_fixpoint s nodes;
      None
    with 
    | Fixpoint db -> Some db
    | Exit -> None
    | Smt.Unsat db -> Some db


  let pure_smt_check s nodes =
    try
      check_fixpoint ~pure_smt:true s nodes;
      None
    with 
    | Fixpoint db -> Some db
    | Exit -> None
    | Smt.Unsat db -> Some db
                           


  let check s visited =
    Debug.unsafe s;
    TimeFix.start ();
    let r = 
      match easy_fixpoint s visited with
      | None -> hard_fixpoint s visited
      | r -> r
    in
    TimeFix.pause ();
    r

end

(*************** Operations with tries () *******************)

module FixpointTrie : sig

  val check : Node.t -> Node.t Cubetrie.t -> int list option

end = struct

  let check_and_add n nodes vis_n=
    let n_array = Node.array n in
    let vis_cube = vis_n.cube in
    let vis_array = vis_cube.Cube.array in
    let d = Instantiation.relevant ~of_cube:vis_cube ~to_cube:n.cube in
    List.fold_left
      (fun nodes ss ->
       let vis_renamed = ArrayAtom.apply_subst ss vis_array in
       (* if ArrayAtom.subset vis_renamed n_array then *)
       (*   raise (Fixpoint [vis_n.Node.tag]) *)
       (* Heuristic : throw away nodes too much different *)
       (* else if ArrayAtom.nb_diff pp anp > 2 then nodes *)
       (* line below useful for arith : ricart *)
       if Cube.inconsistent_array
                 (ArrayAtom.union vis_renamed n_array) then nodes
       else if ArrayAtom.nb_diff vis_renamed n_array > 1 then
         (vis_n, vis_renamed)::nodes
       else (Prover.assume_node vis_n vis_renamed; nodes)
      ) nodes d
      

  let check_fixpoint s visited =
    Prover.assume_goal s;
    let s_array = Node.array s in
    let unprioritize_cands = false in
    let nodes, cands =
      Cubetrie.fold
        (fun (nodes, cands) vis_p ->
         if unprioritize_cands && vis_p.kind = Approx then
           nodes, vis_p :: cands
         else check_and_add s nodes vis_p, cands
        ) ([], []) visited in
    let nodes = List.fold_left (check_and_add s) nodes cands in
    TimeSort.start ();
    let nodes = 
      List.fast_sort 
        (fun (n1, a1) (n2, a2) ->
         if unprioritize_cands &&
              n1.kind = Approx && n2.kind <> Approx then 1 
         (* a1 is a candidate *)
         else
         if unprioritize_cands &&
              n2.kind = Approx && n1.kind <> Approx then 1
         (* a2 is a candidate *)
         else ArrayAtom.compare_nb_common s_array a1 a2) 
        nodes 
    in
    TimeSort.pause ();
    List.iter (fun (vn, ar_renamed) -> Prover.assume_node vn ar_renamed) nodes
              
  let easy_fixpoint s nodes =
    if delete && (s.deleted || Node.has_deleted_ancestor s)
    then Some []
    else Cubetrie.mem_array (Node.array s) nodes

  let medium_fixpoint s visited  =
    let vars, s_array = Node.variables s, Node.array s in
    let substs = Variable.all_permutations vars vars in
    let substs = List.tl substs in (* Drop 'identity' permutation. 
                                    Already checked in easy_fixpoint. *)
    try
      List.iter (fun ss -> 
                 let u = ArrayAtom.apply_subst ss s_array in
                 match Cubetrie.mem_array u visited with
                 | Some uc -> raise (Fixpoint uc)
                 | None -> ()
                ) substs;
      None
    with Fixpoint uc -> Some uc

  let hard_fixpoint s nodes =
    try
      check_fixpoint s nodes;
      None
    with 
    | Fixpoint db -> Some db
    | Exit -> None
    | Smt.Unsat db -> Some db
                           

  let check s nodes =
    Debug.unsafe s;
    TimeFix.start ();
    let r =
      match easy_fixpoint s nodes with
      | None ->
         (match medium_fixpoint s nodes with
          | None -> hard_fixpoint s nodes
          | r -> r)
      | r -> r
    in
    TimeFix.pause ();
    r
end
