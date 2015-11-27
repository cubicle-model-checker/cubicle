open Ast
open Far_util
open Far_modules

type cresult = 
  | Covered of Vertex.t
  | Refined of ucnf
  | Bad_part of ednf


let find_covering v1 t v2 graph =
  let cands = Far_graph.find_refiners v2 graph in
  List.filter (Vertex.imply_by_trans_ww v1 t) cands
        

let close v1 t v2 graph system =
  let vcl = find_covering v1 t v2 graph in
  match vcl with
    | vc :: _ -> Covered vc
    | _ ->
      let bp = Vertex.find_bads_from_w v1 t v2 in
      match bp with
        (* The node v1 doesn't contain a part going to the bad part of
           v2 by t, it means that v1, by t, goes to a part smaller than 
           the one described by v2 but bigger than the one (if it exists) 
           described by the refinement of v2 *)
        | [] -> let r1 = Far_refine.refine v1 t v2 in Refined r1
                                        
        (* The node v1 contains a part going to the bad part of v2 by t. 
           In that case, there exists some parts in v1 which go to the 
           bad parts of the successive bad refinements of v2, we select
           the most generals bad parts *)
        | _ -> let bad_parts = Far_bads.select_parts v1 t v2 bp graph system in
               Bad_part bad_parts
