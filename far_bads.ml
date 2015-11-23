open Ast
open Far_modules.Vertex

let print_bads bl =
  List.iter (
    fun n -> Format.printf "\t\tExists %a, @[%a@] AND\n@." 
      Variable.print_vars (Far_cube.variables n)
      (Types.SAtom.print_sep "&&") (Far_cube.litterals n)
  ) bl    

let find_included_bads v graph = 
  let rec frec acc v =
    match Far_graph.find_refiners v graph with
      | [] -> acc
      | rs -> 
        List.fold_left (
          fun acc r -> let acc = List.rev_append r.bad acc in
                       frec acc r
        ) acc rs
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
    let rec group (actual_group, done_group, dim) = function
      | [] -> (
        match actual_group with 
          | [] -> done_group
          | _ -> (dim, actual_group) :: done_group
      )
      | hd :: tl ->
        let d = Far_cube.dim hd in
        if d = dim then group (hd::actual_group, done_group, dim) tl
        else 
          let done_group =
            match actual_group with 
              | [] -> done_group
              | _ -> (dim, actual_group) :: done_group
          in group ([hd], done_group, d) tl
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
       
