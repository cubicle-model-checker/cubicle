open Ast
open Far_modules

let print_bads bl =
  List.iter (
    fun n -> Format.eprintf "\t\tExists %a, @[%a@] AND\n@." 
      Variable.print_vars (Far_cube.variables n)
      (Cubtypes.SAtom.print_sep "&&") (Far_cube.litterals n)
  ) bl    

let find_included_bads v graph = 
  let rec frec acc v =
    match Far_graph.find_refiners v graph with
      | [] -> acc
      | rs -> List.fold_left (fun acc r -> 
        let acc = List.rev_append r.bad acc in frec acc r
      ) acc rs
  in frec [] v   

let regroup = List.rev_append 

let add_list_to_set l s = List.fold_left (fun a e -> FCSet.add e a) s l
 
let check_validity w1 b2 c =
  let nw1 = Far_cube.negate_litterals_to_ecubes w1 in
  let cig = Far_cube.cube_implies c nw1 in
  match cig with 
    | Some _ -> false
    | None ->
      let cib = Far_cube.cube_implies c b2 in
      match cib with
        | Some _ -> false
        | None -> true
  
let select_parts v1 bads graph system  =
  let w1 = v1.world in
  let selb, _ = List.fold_left (
    fun (selb, ibs) (t, v2, b) ->
      let ob, ibs' = 
        try
          SMap.find v2 ibs, ibs
        with Not_found -> 
          let ib = find_included_bads v2 graph in
          ib, SMap.add v2 ib ibs
      in
      let pob = Far_cube.pre_and_filter ~b:b t ob in
      let pob = List.filter (check_validity w1 v2.bad) pob in
      add_list_to_set pob selb, ibs'
  ) (FCSet.empty, SMap.empty) bads in
  FCSet.elements selb
    
