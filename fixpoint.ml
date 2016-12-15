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



module H = Hstring
module HMap = Hstring.HMap
module HSet = Hstring.HSet
module H3Map = Weakmem.H3Map
let hE = H.make "_e"
let hS1 = H.make "_s1"
let hVar = H.make "_var"
let hVal = H.make "_val"
let hFence = H.make "_fence"
let hRf = H.make "_rf"
let hW = H.make "_W"

let get_evts ar = (* just use regular split + sort params *)
  let evts = Array.fold_left (fun evts a -> Weakmem.split_event a evts) H3Map.empty ar in
  H3Map.fold (fun (p, e, s) (d, v, vi, vals) evts ->
    let pevts = try HMap.find p evts with Not_found -> HMap.empty in
    let sevts = try HMap.find e pevts with Not_found -> HMap.empty in
    let evt = (d, v, List.sort (fun (p1, _) (p2, _) -> H.compare p1 p2) vi, vals) in
    if HMap.mem s sevts then evts (* should not happen *)
    else HMap.add p (HMap.add e (HMap.add s evt sevts) pevts) evts
  ) evts HMap.empty


(* Are e1 and e2 compatible / is e1 more general than e2 *)
let compatible_values r1 op1 t1 r2 op2 t2 =
  match t1, t2 with
  | Const c1, Const c2 ->
     begin match r1, op1 with
     | false, Eq | true, Neq -> (* = *)
        begin match r2, op2 with
	| false, Eq | true, Neq -> Types.compare_constants c1 c2 = 0
	| _ -> false
	end
     | false, Neq | true, Eq -> (* <> *)
        begin match r2, op2 with
	| false, Eq | true, Neq -> Types.compare_constants c1 c2 <> 0
	| false, Neq | true, Eq -> Types.compare_constants c1 c2 = 0
	| false, Lt -> Types.compare_constants c1 c2 >= 0
	| false, Le -> Types.compare_constants c1 c2 > 0
	| true, Le -> Types.compare_constants c1 c2 <= 0
	| true, Lt -> Types.compare_constants c1 c2 < 0
	end
     | false, Lt -> (* < *)
        begin match r2, op2 with
	| false, Eq | true, Neq -> Types.compare_constants c1 c2 > 0
	| false, Lt -> Types.compare_constants c1 c2 >= 0
	| false, Le -> Types.compare_constants c1 c2 > 0
	| _ -> false
	end
     | false, Le -> (* <= *)
        begin match r2, op2 with
	| false, Eq | true, Neq -> Types.compare_constants c1 c2 >= 0
	| false, Lt -> Types.compare_constants c1 c2 >= 0 (* +1 *)
	| false, Le -> Types.compare_constants c1 c2 >= 0
	| _ -> false
	end
     | true, Le -> (* > *)
        begin match r2, op2 with
	| false, Eq | true, Neq -> Types.compare_constants c1 c2 < 0
	| true, Le -> Types.compare_constants c1 c2 <= 0
	| true, Lt -> Types.compare_constants c1 c2 < 0
	| _ -> false
	end
     | true, Lt -> (* >= *)
        begin match r2, op2 with
	| false, Eq | true, Neq -> Types.compare_constants c1 c2 <= 0
	| true, Le -> Types.compare_constants c1 c2 <= 0 (* +1 *)
	| true, Lt -> Types.compare_constants c1 c2 <= 0
	| _ -> false
	end
     end			  
  | _ -> true

(*= v1  = !<> v2      v1 = v2
  = v1  <> != v2      false
  = v1      < v2      false
  = v1     <= v2      false
  = v1    !<= v2      false
  = v1     !< v2      false

 <> v1  = !<> v2      v1 <> v2         eg : x <> 4 / x = 4 // x <> 4 / x = 5 
 <> v1  <> != v2      v1 = v2
 <> v1      < v2      v1 >= v2         eg : x <> 4 / x = 3 // x <> 4 / x = 4
 <> v1     <= v2      v1 > v2
 <> v1    !<= v2      v1 <= v2
 <> v1     !< v2      v1 < v2          eg : x <> 4 / x = 4 // x <> 4 / x = 5

  < v1  = !<> v2      v1 > v2          eg : x < 4 / x = 3 // x < 4 / x = 4 
  < v1  <> != v2      false
  < v1      < v2      v1 >= v2         eg : x < 4 / x <= 3 // x < 4 / x <= 4
  < v1     <= v2      v1 > v2
  < v1    !<= v2      false
  < v1     !< v2      false

 <= v1  = !<> v2      v1 >= v2         eg : x < 4 / x = 4 // x < 4 / x = 5 
 <= v1  <> != v2      false
 <= v1      < v2      v1+1 >= v2       eg : x <= 4 / x < 5 // x <= 4 / x < 6
 <= v1     <= v2      v1 >= v2
 <= v1    !<= v2      false
 <= v1     !< v2      false

  > v1  = !<> v2      v1 < v2          eg : x > 4 / x = 4 // x > 4 / x = 5 
  > v1  <> != v2      false
  > v1      < v2      false
  > v1     <= v2      false
  > v1    !<= v2      v1 <= v2
  > v1     !< v2      v1 < v2          eg : x > 4 / x >= 4 // x > 4 / x >= 5

 >= v1  = !<> v2      v1 <= v2         eg : x >= 4 / x = 3 // x >= 4 / x = 4 
 >= v1  <> != v2      false
 >= v1      < v2      false
 >= v1     <= v2      false
 >= v1    !<= v2      v1 <= v2+1
 >= v1     !< v2      v1 <= v2         eg : x >= 4 / x >= 3 // x <= 4 / x >= 4

x >= 4    x > 2   x > 3   x > 4   x > 5   x > 6    *)

(* Are e1 and e2 compatible / is e1 more general than e2 *)
let compat_evts (d1, v1, vi1, vals1) (d2, v2, vi2, vals2) =
  H.equal d1 d2 && H.equal v1 v2 &&
  List.for_all2 (fun (_, i1) (_, i2) -> H.equal i1 i2) vi1 vi2 &&
    (vals1 = [] && vals2 = [] ||
     vals1 <> [] && vals2 <> [] &&
     List.for_all (fun (r1, op1, t1) ->
       List.for_all (fun (r2, op2, t2) ->
         compatible_values r1 op1 t1 r2 op2 t2
       ) vals2
     ) vals1)

let cartesian_product op l1 l2 =
  List.fold_left (fun rl e1 ->
    List.fold_left (fun rl e2 ->
      (op e1 e2) :: rl
    ) rl l2
  ) [] l1

let cartesian_product_h3m =
  cartesian_product (H3Map.union (fun k v1 v2 -> failwith "cartesian_product : duplicate"))

let rec make_s_combs2 p ef et ssf sst = (* use min_binding *)
  let rec aux cc rcl ssf sst =
    try
      let sf, evtf = HMap.choose ssf in
      let ssf = HMap.remove sf ssf in
      HMap.fold (fun st evtt rcl ->
        let sst = HMap.remove st sst in
        (* let cc = (p, ef, sf, et, st) :: cc in *)
	(* let cc = H3Map.add (p, ef, sf) (et, st) cc in *)
	(* aux cc rcl ssf sst *)
	if compat_evts evtf evtt then
	  let cc = H3Map.add (p, ef, sf) (et, st) cc in
	  aux cc rcl ssf sst
	else rcl
      ) sst rcl (* To Set is finished -> combinations done for this sf *)
    with Not_found -> cc :: rcl (* From Set is empty -> the combination is good *)
  in
  aux H3Map.empty [] ssf sst

let rec make_s_combs p ef et ssf sst =
  let rec aux cc rcl ssf sst =
    try
      let sf, evtf = HMap.choose ssf in
      let ssf = HMap.remove sf ssf in
      HMap.fold (fun st evtt rcl ->
        let sst = HMap.remove st sst in
        (* let cc = (p, ef, sf, et, st) :: cc in *)
	(* let cc = H3Map.add (p, ef, sf) (et, st) cc in *)
	(* aux cc rcl ssf sst *)
	if compat_evts evtf evtt then
	  let cc = H3Map.add (p, ef, sf) (et, st) cc in
	  aux cc rcl ssf sst
	else rcl
      ) sst rcl (* To Set is finished -> combinations done for this sf *)
    with Not_found -> cc :: rcl (* From Set is empty -> the combination is good *)
  in
  aux H3Map.empty [] ssf sst

let rec make_e_combs p esf est =
  let rec aux ccl rcl esf est =
    try
      let ef, ssf = HMap.choose esf in
      let esf = HMap.remove ef esf in
      let rcl, _ = HMap.fold (fun et sst (rcl, est) ->
        let est = HMap.remove et est in
        (* let ccl = cartesian_product (@) (make_s_combs p ef et ssf sst) ccl in *)
        let ccl = cartesian_product_h3m (make_s_combs p ef et ssf sst) ccl in
        aux ccl rcl esf est, est
      ) est (rcl, est) (* To Set is finished -> combinations done for this ef *)
      in rcl
    with Not_found -> ccl @ rcl (* From Set is empty -> the combinations are good *)
  in
  aux [H3Map.empty] [] esf est

let rec make_p_combs psf pst =
  let rec aux ccl psf pst =
    try
      let p, esf = HMap.choose psf in
      let psf = HMap.remove p psf in
      try
        let est = HMap.find p pst in
        let pst = HMap.remove p pst in
        (* let ccl = cartesian_product (@) (make_e_combs p esf est) ccl in *)
        let ccl = cartesian_product_h3m (make_e_combs p esf est) ccl in
        aux ccl psf pst (* Next process *)
      with Not_found -> [H3Map.empty]
    with Not_found -> ccl (* From Set is empty -> we're done *)
  in
  aux [H3Map.empty] psf pst


let remap_events_ar ar sub =
  let subst p e s =
    (* try HMap.find (p, e, s) sub with Not_found -> e, s in *)
    try H3Map.find (p, e, s) sub with Not_found -> failwith "remap_events : no substitution !"
  in
  let rec remap_t = function
    | Arith (t, c) -> Arith (remap_t t, c)
    | Field (t, f) -> Field (remap_t t, f)
    | Access (a, [p;e;s]) when H.equal a hE ->
        let e, s = subst p e s in Access (a, [p;e;s])
    | Access (a, [p;e]) when H.equal a hFence ->
        let e, _ = subst p e hS1 in Access (a, [p;e])
    | Access (a, [p1;e1;s1;p2;e2;s2]) when H.equal a hRf ->
        let e1, s1 = subst p1 e1 s1 in
        let e2, s2 = subst p2 e2 s2 in
        Access (a, [p1;e1;s1;p2;e2;s2])
    | t -> t
  in
  let rec remap_a = function
    | Atom.Comp (t1, op, t2) -> Atom.Comp (remap_t t1, op, remap_t t2)
    | Atom.Ite (sa, a1, a2) -> Atom.Ite (sa, remap_a a1, remap_a a2)
    | a -> a
  in
  let ar = Array.map remap_a ar in
  Array.fast_sort Atom.compare ar;
  ar

let remap_events ar substs =
  List.fold_left (fun nodes s ->
    if H3Map.is_empty s then nodes
    else (remap_events_ar ar s) :: nodes
  ) [] substs    



let check_and_add n nodes vis_n=
  let n_array = Node.array n in
  let vis_cube = vis_n.cube in
  let vis_array = vis_cube.Cube.array in
  let to_eids = get_evts n_array in
  if !Options.size_proc <> 0 then (
    let from_eids = get_evts vis_array in
    let vis_array_l = (remap_events vis_array (make_p_combs from_eids to_eids)) in
    let vis_array_l = List.filter (fun v_ar ->
		        not (Cube.inconsistent_2arrays v_ar n_array)) vis_array_l in
    List.fold_left (fun nodes v_ar -> (vis_n, v_ar) :: nodes) nodes vis_array_l) 
  else
    let d = Instantiation.relevant ~of_cube:vis_cube ~to_cube:n.cube in
    List.fold_left (fun nodes ss ->
      let vis_renamed = ArrayAtom.apply_subst ss vis_array in
      let from_eids = get_evts vis_renamed in
      let vis_renamed_l = (remap_events vis_renamed (make_p_combs from_eids to_eids)) in
      let vis_renamed_l = List.filter (fun v_ren ->
		            not (Cube.inconsistent_2arrays v_ren n_array)) vis_renamed_l in
      List.fold_left (fun nodes v_ren -> (vis_n, v_ren) :: nodes) nodes vis_renamed_l      
    ) nodes d


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
    first_action s;
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
    (*if !Options.size_proc <> 0 then None else*)
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
