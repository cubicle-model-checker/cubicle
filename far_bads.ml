open Ast
open Far_modules.Vertex

let find_included_bads v graph = 
  let rec frec acc v =
    match Far_graph.find_refiners v graph with
      | [] -> acc
      | rs -> List.fold_left (fun acc r -> List.rev_append (frec acc r) acc) acc rs
  in frec [] v
        

let regroup = List.rev_append 


let simplify_dnf w1 b2 dnf =
  let nw1 = Far_cube.negate_litterals_to_ecubes w1 in
  let sdnf = List.fold_left (
    fun acc cube ->
      let cig = Far_cube.cube_implies cube nw1 in
      match cig with 
        | Some _ -> acc
        | None ->
          let cib = Far_cube.cube_implies cube b2 in
          match cib with
            | Some c -> c::acc
            | None -> 
              match Fixpoint.FixpointList.check cube acc with
                | None -> cube::acc
                | Some l -> acc
  ) [] dnf in
  sdnf


let select_procs slb v1 v2 =
  let gbd =
    let slb = List.fast_sort Far_cube.compare_decr_fcubes slb in
    let rec group (cacc, acc, dim) = function
      | [] -> (
        match cacc with 
          | [] -> acc
          | _ -> (dim, cacc) :: acc
      )
      | hd :: tl ->
        let d = Far_cube.dim hd in
        if d = dim then group (hd::cacc, acc, dim) tl
        else 
          let acc =
            match cacc with 
              | [] -> acc
              | _ -> (dim, cacc) :: acc
          in group ([], acc, d) tl
    in group ([], [], 0) slb in
  let rec s l =
    match l with
      | [] -> assert false
      | (dim, lcubes) :: st ->
        let nl = simplify_dnf v1.world v2.bad lcubes in
        match nl with
          | [] -> s st
          | _ -> List.iter Stats.new_node nl; nl
  in s gbd


let select_parts bad_parts v1 v2 =
  select_procs bad_parts v1 v2
       
