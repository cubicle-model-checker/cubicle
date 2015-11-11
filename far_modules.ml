open Ast
open Types

module Solver = Smt.Make(Options)
module Oracle = Approx.SelectedOracle
  
exception FUnsafe
exception FSafe

module type SigQ = sig

  type 'a t

  exception Empty

  val create : unit -> 'a t
  val push : 'a -> 'a t -> unit
  val pop : 'a t -> 'a
end

let select_strat =
  (match Options.far_priority with
    | "bfs" -> (module Queue : SigQ)
    | "dfs" -> (module Stack)
    | _ -> assert false
  )

module Q : SigQ = (val (select_strat))

module Vertex = struct

  type t = vertex_far

  let create =
    let cpt = ref 0 in
    fun ?is_root:(ir=false) w ac b ->
      incr cpt;
      let v =
        {
	  id = !cpt;
          world = w;
          added_clauses = ac;
	  bad = b;
	  is_root = ir;
        } in
      (* Stats.new_vertex v; *)
      v

  let create_world l = 
    List.fold_left (
      fun acc (vl, sa) -> 
        let c = Cube.create vl sa in
        (Far_cube.create c)::acc
    ) [] l

  let create_bad = create_world
      
  let create_from_refinement v2 r =
    let w = if v2.is_root then r
      else List.rev_append r v2.world in
    create w r []

  let equal t1 t2 = t1.id = t2.id

  let compare t1 t2 = t1.id - t2.id

  let hash t = t.id

  let is_bad t = 
    List.exists (
      fun n -> 
        not (SAtom.is_empty (Node.litterals n))
    ) t.bad

  let is_root t = t.is_root

  let (=!>) v1 v2 = v1.id >= v2.id

  let update_bad v1 b t v2 = v1.bad <- b
    
  let find_all_sf2_implying_f1 f1 f2 =
    List.filter (
      fun sf -> match Fixpoint.FixpointList.check sf f1 with
        | Some _ -> true
        | None -> false
    ) f2

      
  let imply_by_trans_ww v1 t v2 =
    let nw2 = Far_cube.negate_pre_and_filter t v2.added_clauses in
    match find_all_sf2_implying_f1 v1.world nw2 with
      | [] -> true
      | _ -> false


  let find_bads_from_w v1 t v2 =
    let nb2 = Far_cube.pre_and_filter t v2.bad in
    find_all_sf2_implying_f1 v1.world nb2
    
end

let init_trans_from trans =
  let empty = [Node.create (Cube.create [] SAtom.empty)] in
  let twl = List.map (fun t -> (t, Far_util.compute_pre t empty)) trans in
  fun v1 ->
    List.fold_left (
      fun acc (t, w) -> 
        match Vertex.find_all_sf2_implying_f1 v1.world w with
          | [] -> acc
          | _ -> t::acc
    ) [] twl

let queue : Vertex.t Q.t = Q.create ()

module OrdTrans = struct
  type t = transition
  let compare t1 t2 = Hstring.compare t1.tr_info.tr_name t2.tr_info.tr_name
end

module TMap = Map.Make (OrdTrans)
module VSet = Set.Make (Vertex)
