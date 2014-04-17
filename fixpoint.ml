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
open Util


module Debug = struct

  let fixpoint = 
    if not debug then fun _ -> () else 
      fun ls ->
	eprintf "\nAfter simplification, subsumption and fixpoint check : @.";
	match ls with
	  | [] -> eprintf "No new branches@."
	  | _ -> 
	      List.iter (eprintf "@.New branch : %a@." Pretty.print_system) ls

  let unsafe = 
    if not debug then fun _ -> () else 
      fun s ->
	eprintf "    %a@." Pretty.print_unsafe s

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
    let n_array = n.Node.cube.Cube.array in
    let nodes = 
      List.fold_left
        (fun nodes vis_n ->
         let vis_cube = vis_n.Node.cube in
         let d = Instantitaion.relevant
                   ~of_cube:vis_cube ~to_cube:n.Node.cube in
         List.fold_left
	   (fun nodes ss ->
	    let vis_renamed = Atom.Array.apply_subst ss vis_cube.Cube.array in
	    if not pure_smt && Atom.Array.subset vis_renamed n_array then
	        raise (Fixpoint [vis_n.Node.tag])
	    (* Heuristic : throw away nodes too much different *)
	    (* else if Atom.Array.nb_diff pp anp > 2 then nodes *)
	    (* line below useful for arith : ricart *)
	    else if not pure_smt &&
                    Cube.inconsistent_array
                      (Atom.Array.union vis_renamed n_array) then nodes
	    else if Atom.Array.nb_diff vis_renamed n_array > 1 then
              (vis_n, vis_renamed)::nodes
	    else (Prover.assume_node vis_n vis_renamed; nodes)
	   ) nodes d
        ) [] visited
    in
    TimeSort.start ();
    let nodes = 
      List.fast_sort 
        (fun (n1, a1) (n2, a2) -> Atom.Array.compare_nb_common n_array a1 a2) 
        nodes 
    in
    TimeSort.pause ();
    List.iter (fun (vn, ar_renamed) -> Prover.assume_node vn ar_renamed) nodes


  let easy_fixpoint s nodes =
    if delete && (s.Node.deleted || Node.has_deleted_ancestor s)
    then Some []
    else
      let db = ref None in
      let ars = Node.array s in
      ignore (List.exists 
	        (fun sp -> 
		 if Atom.Array.subset (Node.array sp) ars then
		 begin db := Some [sp.Node.tag]; true end
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

  let check_and_add n vis_n nodes =
    let n_array = Node.array n in
    let vis_cube = vis_n.Node.cube in
    let vis_array = vis_cube.Cube.array in
    let d = Instantitaion.relevant ~of_cube:vis_cube ~to_cube:n.Node.cube in
    List.fold_left
      (fun nodes ss ->
       let vis_renamed = Atom.Array.apply_subst ss vis_array in
       (* if Atom.Array.subset vis_renamed n_array then *)
       (*   raise (Fixpoint [vis_n.Node.tag]) *)
       (* Heuristic : throw away nodes too much different *)
       (* else if Atom.Array.nb_diff pp anp > 2 then nodes *)
       (* line below useful for arith : ricart *)
       if Cube.inconsistent_array
                 (Atom.Array.union vis_renamed n_array) then nodes
       else if Atom.Array.nb_diff vis_renamed n_array > 1 then
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
         if unprioritize_cands && vis_p.Node.kind = Node.Approx then
           nodes, vis_p :: cands
         else check_and_add nargs s vis_p nodes, cands
        ) ([], []) visited in
    let nodes = List.fold_left (check_and_add nargs anp) nodes cands in
    TimeSort.start ();
    let nodes = 
      List.fast_sort 
        (fun (n1, a1) (n2, a2) ->
         if unprioritize_cands &&
              n1.Node.kind = Node.Approx && n2.Node.kind <> Node.Approx then 1 
         (* a1 is a candidate *)
         else
         if unprioritize_cands &&
              n2.Node.kind = Node.Approx && n1.Node.kind <> Node.Approx then 1
         (* a2 is a candidate *)
         else Atom.Array.compare_nb_common s_array a1 a2) 
        nodes 
    in
    TimeSort.pause ();
    List.iter (fun (vn, ar_renamed) -> Prover.assume_node vn ar_renamed) nodes
              
  let easy_fixpoint s nodes =
    if delete && (s.Node.deleted || Node.has_deleted_ancestor s)
    then Some []
    else Cubetrie.mem_array npa nodes

  let medium_fixpoint s visited  =
    let vars, s_array = Node.variables s, Node.array s in
    let substs = Variable.all_permutations vars vars in
    let substs = List.tl substs in (* Drop 'identity' permutation. 
                                    Already checked in easy_fixpoint. *)
    try
      List.iter (fun ss -> 
                 let u = Atom.Array.apply_subst ss s_array in
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
