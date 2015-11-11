open Ast
open Far_util
open Far_modules

type cresult = 
  | Covered of Vertex.t
  | Refined of ucnf
  | Bad_part of ednf


let find_covering v1 t v2 graph =
  let cands = Far_graph.find_refiners v2 graph in
  List.filter (
    fun vs -> Vertex.(vs =!> v2) && 
      Vertex.imply_by_trans_ww v1 t vs
  ) cands
        

let close v1 t v2 graph =
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
        | _ -> let other_bads = Far_bads.find_included_bads v2 graph in
               let all_bads = Far_bads.regroup other_bads bp in
               let bad_parts = Far_util.compute_pre t all_bads in
               let bad_parts = Far_bads.select_parts bad_parts v1 v2 in
               Bad_part bad_parts
        
