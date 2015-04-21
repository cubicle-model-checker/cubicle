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
                      Cube.inconsistent_2arrays vis_renamed n_array then nodes
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


(*************** Certificates from fixpoints  *******************)


module FixpointCertif : sig

  val useful_instances : Node.t -> Node.t list -> (Node.t * Variable.subst) list

end = struct

  type env = {
      mutable hid_cubes : (int, (Node.t * Variable.subst)) Hashtbl.t;
      mutable cur_id : int;
    }
               
  let empty_env = {
      hid_cubes = Hashtbl.create 17;
      cur_id = 0
    }
                    
  let fresh_id env =
    env.cur_id <- env.cur_id + 1;
    env.cur_id + 1

  let assume_node env n sigma a =
    let nid = fresh_id env in
    Hashtbl.add env.hid_cubes nid (n, sigma);
    Prover.assume_node { n with tag = nid } a

  let check_fixpoint env ?(pure_smt=false) n visited =
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
	        begin
                  let nid = fresh_id env in
                  Hashtbl.add env.hid_cubes nid (vis_n, ss);
                  raise (Fixpoint [nid])
                end
	    (* Heuristic : throw away nodes too much different *)
	    (* else if ArrayAtom.nb_diff pp anp > 2 then nodes *)
	    (* line below useful for arith : ricart *)
	    else if not pure_smt &&
                      Cube.inconsistent_2arrays vis_renamed n_array then nodes
	    else if ArrayAtom.nb_diff vis_renamed n_array > 1 then
              (vis_n, ss, vis_renamed)::nodes
	    else (assume_node env vis_n ss vis_renamed; nodes)
	   ) nodes d
        ) [] visited
    in
    TimeSort.start ();
    let nodes = 
      List.fast_sort 
        (fun (n1,_,a1) (n2,_,a2) -> ArrayAtom.compare_nb_common n_array a1 a2) 
        nodes 
    in
    TimeSort.pause ();
    List.iter (fun (vn, ss, ar_renamed) ->
               assume_node env vn ss ar_renamed) nodes


  let easy_fixpoint env s nodes =
    if delete && (s.deleted || Node.has_deleted_ancestor s)
    then Some []
    else
      let db = ref None in
      let ars = Node.array s in
      ignore (List.exists 
	        (fun sp -> 
		 if ArrayAtom.subset (Node.array sp) ars then
	           begin
                     let nid = fresh_id env in
                     let vars = Node.variables sp in
                     let ss = Variable.build_subst vars vars in
                     Hashtbl.add env.hid_cubes nid (sp, ss);
                     db := Some [nid]; true
                   end
		 else false
                ) nodes);
      !db

  let hard_fixpoint env s nodes =
    try
      check_fixpoint env s nodes;
      None
    with 
    | Fixpoint db -> Some db
    | Exit -> None
    | Smt.Unsat db -> Some db


  let pure_smt_check env s nodes =
    try
      check_fixpoint env ~pure_smt:true s nodes;
      None
    with 
    | Fixpoint db -> Some db
    | Exit -> None
    | Smt.Unsat db -> Some db
                           

  let check env s visited =
    Debug.unsafe s;
    TimeFix.start ();
    let r = 
      match easy_fixpoint env s visited with
      | None -> hard_fixpoint env s visited
      | r -> r
    in
    TimeFix.pause ();
    r

  let useful_instances s visited =
    let env = {
        hid_cubes = Hashtbl.create (3 * (List.length visited));
        cur_id = s.tag
      } in
    match check env s visited with
    | None -> assert false
    | Some db ->
       (* eprintf "\n> mon id %d \n" s.tag; *)
       (* List.iter (eprintf "\n>%d ") db; eprintf "@."; *)
       let db = List.filter (fun id -> not (id = s.tag)) db in
       (* List.iter (eprintf "\n>>%d ") db; eprintf "@."; *)
       (* Hashtbl.iter (fun id (n, sigma) ->  *)
       (*               eprintf "id:%d == %d[%a]@." id n.tag *)
       (*                       Variable.print_subst sigma) env.hid_cubes; *)
       List.map (Hashtbl.find env.hid_cubes) db


end

(*************** Operations with tries () *******************)

module FixpointTrie : sig

  val easy_fixpoint : Node.t -> Node.t Cubetrie.t -> int list option
  val peasy_fixpoint : Node.t -> Node.t Cubetrie.t -> int list option
  val hard_fixpoint : Node.t -> Node.t Cubetrie.t -> int list option

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
       if Cube.inconsistent_2arrays vis_renamed n_array then nodes
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
                           
  let peasy_fixpoint s nodes = 
    match easy_fixpoint s nodes with
    | None -> medium_fixpoint s nodes
    | r -> r

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
    begin match r with
    | None -> ();
    | Some db ->
        Format.fprintf Format.std_formatter "---- Node %d (from " s.tag;
        List.iter (fun (_, _, next_node) ->
          Format.fprintf Format.std_formatter "%d " next_node.tag) s.from;
        Format.fprintf Format.std_formatter ") ----\nFP : ";
        List.iter (fun i -> Format.fprintf Format.std_formatter "%d " i) db;
        Format.fprintf Format.std_formatter ".\n";
    end;
    let nops_match nops1 nops2 =
      try List.for_all2 (fun (p1, op1, wops2) (p2, op2, wops2) ->
	 p1 = p2 && op1 = op2 (* ALSO CHECK WOPS *)
      ) nops1 nops2
      with Invalid_argument _ -> false		
    in
    let r = begin match r with
    | None -> None
    | Some [] -> Some []
    | Some db ->
        let r = begin try
          let _, _, nd = List.find (fun (t_info, vars, next_node) ->
            List.exists (fun tag -> next_node.tag = tag) db
          ) s.from in (*
          Format.fprintf Format.std_formatter "Node %d matches\n" nd.tag; *)
          Some db
          with Not_found -> None
        end in
	if r <> None then r else begin (* if it loops, fixpoint *)
        let nds = Cubetrie.fold (fun nds n ->
          if List.exists (fun tag -> n.tag = tag) db then n :: nds else nds
        ) [] nodes in
        let new_db = List.fold_left (fun db n ->
          (* if n.ops = s.ops then n.tag :: db else db *)
          if nops_match n.nops s.nops then n.tag :: db else db
        ) [] nds in
        if new_db <> [] then begin
          Format.fprintf Format.std_formatter "%d subsumed\n" s.tag;
          Some new_db end
	else None end
    end in

    r (*; None*)  (* TSO : Turn off fixpoint for now *)
end



module FixpointTrieNaive : sig

  val check : Node.t -> Node.t Cubetrie.t -> int list option

end = struct

  let check_and_add n nodes vis_n=
    let vis_cube = vis_n.cube in
    let vis_array = vis_cube.Cube.array in
    let d = Instantiation.exhaustive ~of_cube:vis_cube ~to_cube:n.cube in
    List.fold_left
      (fun nodes ss ->
       let vis_renamed = ArrayAtom.apply_subst ss vis_array in
         (vis_n, vis_renamed)::nodes
      ) nodes d
      

  let check_fixpoint s visited =
    let nodes =
      Cubetrie.fold
        (fun nodes vis_p ->
         check_and_add s nodes vis_p) [] visited in
    Prover.assume_goal_nodes s nodes

              
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
    let r = hard_fixpoint s nodes in
    (*   match easy_fixpoint s nodes with *)
    (*   | None -> *)
    (*      (match medium_fixpoint s nodes with *)
    (*       | None -> hard_fixpoint s nodes *)
    (*       | r -> r) *)
    (*   | r -> r *)
    (* in *)
    TimeFix.pause ();
    r
end
