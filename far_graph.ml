open Ast
open Far_modules

include Hashtbl.Make (Far_modules.Vertex)


type content = {
  parents : TVSet.t;
  edges : Vertex.t TMap.t;
  extra_by : VSet.t;
  extra_from : VSet.t;
}

let empty_content = {parents = TVSet.empty; 
                     edges = TMap.empty; 
                     extra_by = VSet.empty; 
                     extra_from = VSet.empty}
  
let sec_find v g = try find g v with Not_found -> empty_content
  
let find_refiners v g = let cont = sec_find v g in VSet.elements cont.extra_by

let trans_map v g =
  let {edges = e} = 
    match v.parent with
      | Some v -> sec_find v g
      | None -> empty_content
  in e

let get_trans m tf v =
  if TMap.is_empty m then tf v else List.rev (TMap.fold (fun key _ l -> key::l) m [])

let get_node t e =
  try
    Some (TMap.find t e)
  with Not_found -> None

let list_trans_to v g =
  match v.parent with
    | None -> ()
    | Some v ->
      let {edges = e} = sec_find v g in
      TMap.iter (fun t v ->
        Format.eprintf "\t--%a--> %a@." Hstring.print t.tr_info.tr_name 
          Vertex.print_id v
      ) e

let add_vertex v g =
  add g v empty_content
                 
let add_edge v1 t v2 g = 
  let cv1 = sec_find v1 g in
  let cv1 = {cv1 with edges = TMap.add t v2 cv1.edges} in
  replace g v1 cv1;
  let cv2 = sec_find v2 g in
  let cv2 = {cv2 with parents = TVSet.add (v1, t) cv2.parents} in
  replace g v2 cv2

let get_parents v g = 
  let cont = sec_find v g in
  TVSet.elements cont.parents

let update_edge v1 t delv newv g =
  let cv1 = sec_find v1 g in
  let cv1 = {cv1 with edges = TMap.add t newv cv1.edges} in
  replace g v1 cv1;
  let cdv = sec_find delv g in
  let cdv = {
    cdv with
      parents = TVSet.remove (v1, t) cdv.parents;
      extra_by = VSet.add newv cdv.extra_by
  } in
  replace g delv cdv;
  let cnv = sec_find newv g in
  let cnv = {
    cnv with
      parents = TVSet.add (v1, t) cnv.parents;
      extra_from = VSet.add delv cnv.extra_from
  } in
  replace g newv cnv
  
    
  
