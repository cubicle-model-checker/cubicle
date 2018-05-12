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

  let first_action =
    match Prover.SMT.check_strategy with
    | Smt.Eager -> Prover.assume_goal
    | Smt.Lazy -> Prover.assume_goal_no_check

  let assume =
    match Prover.SMT.check_strategy with
    | Smt.Eager -> Prover.assume_node
    | Smt.Lazy -> Prover.assume_node_no_check
    
  let last_action =
    match Prover.SMT.check_strategy with
    | Smt.Eager -> fun () -> ()
    | Smt.Lazy -> Prover.run

  
  let filter_events sa =
    let open Channels in
    SAtom.filter (function
      | Atom.Comp (Access (a, [_]), Eq, _)
      | Atom.Comp (_, Eq, Access (a, [_]))
           when is_event a && not (is_value a) -> false
      | _ -> true) sa

  let preprocess_n n =
    let open Channels in
    let sa = n.cube.Cube.litterals in
    let _, _, _, _, evts = Chanevent.extract_events_set sa in
    let rels = Chanrel.extract_rels_set sa in
    let sa = Chanrel.filter_rels_set sa in
    let sa = filter_events sa in (* optional *)
    { n with cube = Cube.create n.cube.Cube.vars sa }, evts, rels

  let get_evts_rels_ar ar = (* this is now done before renaming *)
    let _, _, _, _, evts = Chanevent.extract_events_array ar in
    let rels = Chanrel.extract_rels_array ar in
    evts, rels

(* module HAA = Hashtbl.Make (ArrayAtom) *)
module HAA = Hashtbl.Make (Chanevent.Int)
let cache = HAA.create 10000


  let check_and_add (n, to_evts, to_rels) nodes vis_n=
    let vis_n_cube = Cube.create vis_n.cube.Cube.vars (*for inst only*)
                    (* (Chanrel.filter_rels_set vis_n.cube.Cube.litterals) in *)
    (filter_events (Chanrel.filter_rels_set vis_n.cube.Cube.litterals)) in
    let n_array = Node.array n in
    let vis_array = vis_n.cube.Cube.array in
    (* if !Options.size_proc <> 0 then begin *)
    (*   let from_evts = Weakfp.get_evts vis_array in *)
    (*   let vis_array_l = (Weakfp.remap_events vis_array *)
    (*     (Weakfp.build_event_substs from_evts to_evts)) in *)
    (*   let vis_array_l = List.filter (fun v_ar -> *)
    (*     not (Cube.inconsistent_2arrays v_ar n_array)) vis_array_l in *)
    (*   List.fold_left (fun nodes v_ar -> *)
    (*     (vis_n, v_ar) :: nodes) nodes vis_array_l *)
    (* end else *)
    (* TimePESubst.start (); *)
      let d = Instantiation.relevant ~of_cube:vis_n_cube ~to_cube:n.cube in

      let from_evts, from_rels =
        if d = [] then
          Channels.HMap.empty, Chanrel.Rel.empty
        else begin
          (* TimeFPRels.start (); *)
          (* let from_evts, from_rels = get_evts_rels_ar vis_array in *)
          let from_evts, from_rels =
            try
              (* HAA.find cache vis_array *)
              HAA.find cache vis_n.tag
            with Not_found ->
              let r = get_evts_rels_ar vis_array in
              (* HAA.add cache vis_array r; *)
              HAA.add cache vis_n.tag r;
              r
          in
          (* TimeFPRels.pause (); *)
          from_evts, from_rels
        end
      in

      let n = if Channels.HMap.cardinal to_evts <
                   Channels.HMap.cardinal from_evts then nodes
              else List.fold_left (fun nodes ss ->
      (* let n = List.fold_left (fun nodes ss -> *)
        (* let vis_renamed = ArrayAtom.apply_subst ss vis_array in *)
        let vis_renamed = ArrayAtom.apply_subst ss vis_n_cube.Cube.array in
        let from_evts = Chanevent.subst ss from_evts in
        (* let from_rels = Chanrel.subst ss from_rels in *)
        let from_rels = from_rels in
        let vis_renamed_l = (Chanfp.remap_events vis_renamed
          (Chanfp.build_event_substs from_evts from_rels to_evts to_rels)) in
        let vis_renamed_l = List.filter (fun v_ren -> (* IMPROVE INCONSISTENT *)
          not (Cube.inconsistent_2arrays v_ren n_array)) vis_renamed_l in
(* Format.fprintf Format.std_formatter "Matches for perm : %d (proc perms : %d)\n" (List.length vis_renamed_l) (List.length d); *)
        List.fold_left (fun nodes v_ren ->
	  (vis_n, v_ren) :: nodes) nodes vis_renamed_l      
        ) nodes d in
    (* TimePESubst.pause (); *)
(* let lnodes = List.length nodes in *)
(* let perms = ((List.length n) - lnodes) in *)
(* if perms > 0 then begin *)
(* Format.fprintf Format.std_formatter "Visited node %d, " vis_n.tag; *)
(* Format.fprintf Format.std_formatter "proc perms : %d, " (List.length d); *)
(* Format.fprintf Format.std_formatter "total perms : %d\n" perms; *)
(* (\* if perms > 0 then Format.fprintf Format.std_formatter "%a\n" Node.print vis_n; *\) *)
(* Format.print_flush (); end; *)
n


(*  let check_and_add n nodes vis_n=
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
       else if true || ArrayAtom.nb_diff vis_renamed n_array > 1 then
         (vis_n, vis_renamed)::nodes
       else
         (* These are worth assuming and checking right away because they might
            yield unsatifisability sooner *)
         (Prover.assume_node vis_n vis_renamed; nodes)
      ) nodes d *)
      

  let check_fixpoint s visited =
    let s,e,r  = preprocess_n s in
    first_action s;
    let s_array = Node.array s in
    let unprioritize_cands = false in
    let nodes, cands =
      Cubetrie.fold
        (fun (nodes, cands) vis_p ->
         if unprioritize_cands && vis_p.kind = Approx then
           nodes, vis_p :: cands
         else check_and_add (s,e,r) nodes vis_p, cands
        ) ([], []) visited in
    let nodes = List.fold_left (check_and_add (s,e,r)) nodes cands in
    TimeSort.start ();
    let nodes = match Prover.SMT.check_strategy with
      | Smt.Lazy -> nodes
      | Smt.Eager ->
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
    List.iter (fun (vn, ar_renamed) -> assume vn ar_renamed) nodes;
    last_action ()

  
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
    r
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
