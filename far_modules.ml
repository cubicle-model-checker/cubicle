open Ast
open Types

module Solver = Smt.Make(Options)
module Oracle = Approx.SelectedOracle
  
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
    fun ?is_root:(ir=false) ?is_top:(it=false) w ac b ->
      incr cpt;
      let v =
        {
	  id = !cpt;
          world = w;
          added_clauses = ac;
	  bad = b;
	  is_root = ir;
          is_top = it;
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

  let string_of_id v =
    match v.id with
      | 1 -> "top"
      | 2 -> "root"
      | i -> string_of_int i


  let print_id fmt v = Format.printf "%s" (string_of_id v)
    
  let print_world fmt t =
    List.iter (
      fun n -> Format.eprintf "\t\tForall %a, @[%a@] AND\n@." 
        Variable.print_vars (Far_cube.variables n)
        (SAtom.print_sep "||") (Far_cube.litterals n)
    ) t.world

  let print_bad fmt t =
    List.iter (
      fun n -> Format.eprintf "\t\tExists %a, @[%a@] AND\n@." 
        Variable.print_vars (Far_cube.variables n)
        (SAtom.print_sep "&&") (Far_cube.litterals n)
    ) t.bad

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

  let base_implication dnf1 dnf2 =
    List.for_all (
      fun c ->
        match Fixpoint.FixpointList.check c dnf1 with
          | Some _ -> true
          | None -> false
    ) dnf2

      
  let imply_by_trans_ww v1 t v2 =
    let pnw2 = Far_cube.negate_pre_and_filter t v2.added_clauses in
    let nw1 = Far_cube.negate_litterals_to_ecubes v1.world in
    base_implication nw1 pnw2

  let find_bads_from_w v1 t v2 =
    let nb2 = Far_cube.pre_and_filter t v2.bad in
    let nw1 = Far_cube.negate_litterals_to_ecubes v1.world in
    List.filter (
      fun c ->
        match Fixpoint.FixpointList.check c nw1 with
          | Some _ -> false
          | None -> true
    ) nb2

end

let init_trans_from trans =
  let empty = [Node.create (Cube.create [] SAtom.empty)] in
  let twl = List.rev (List.map (fun t -> 
    let w = Far_util.compute_pre t empty in (t, w)
  ) trans) in
  fun v1 ->
    let nw1 = Far_cube.negate_litterals_to_ecubes v1.world in
    List.fold_left (
      fun acc (t, w) -> if Vertex.base_implication nw1 w then acc else t::acc
    ) [] twl
      
let queue : Vertex.t Q.t = Q.create ()

module OrdCpl = struct
  type t = Vertex.t * transition
  let compare (v1, t1) (v2, t2) = 
    let c1 =  Pervasives.compare v1.id v2.id in
    if c1 = 0 then Hstring.compare t1.tr_info.tr_name t2.tr_info.tr_name
    else c1
end

module OrdTrans = struct
  type t = transition
  let compare t1 t2 = Hstring.compare t1.tr_info.tr_name t2.tr_info.tr_name
end

module TVSet = Set.Make (OrdCpl)
module TMap = Map.Make (OrdTrans)
module VSet = Set.Make (Vertex)
