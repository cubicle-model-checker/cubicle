open Far_modules

include Hashtbl.Make (Far_modules.Vertex)


type content = {
  parents : Vertex.t TMap.t;
  edges : Vertex.t TMap.t;
  extra_by : VSet.t;
  extra_from : VSet.t;
}

let empty_content = {parents = TMap.empty; 
                     edges = TMap.empty; 
                     extra_by = VSet.empty; 
                     extra_from = VSet.empty}

let sec_find g v = try find g v with Not_found -> empty_content
  
let find_refiners v g = 
  let cont = sec_find g v in
  VSet.elements cont.extra_by

let add_vertex v g =
  add g v empty_content
                 
let add_edge v1 t v2 g = 
  let cv1 = sec_find g v1 in
  let cv2 = sec_find g v2 in
  let cv1 = {cv1 with edges = TMap.add t v2 cv1.edges} in
  let cv2 = {cv2 with parents = TMap.add t v1 cv2.parents} in
  replace g v1 cv1;
  replace g v2 cv2

let get_parents v g = 
  let cont = sec_find g v in
  TMap.bindings cont.parents

let update_edge v1 t delv newv g =
  let cv1 = sec_find g v1 in
  let cdv = sec_find g delv in
  let cnv = sec_find g newv in
  let cv1 = {cv1 with edges = TMap.add t newv cv1.edges} in
  let cdv = {
    cdv with
      parents = TMap.remove t cdv.parents;
      extra_by = VSet.add newv cdv.extra_by
  } in
  let cnv = {
    cnv with
      parents = TMap.add t v1 cnv.parents;
      extra_from = VSet.add delv cnv.extra_from
  } in
  replace g v1 cv1;
  replace g delv cdv;
  replace g newv cnv
  
    
  
