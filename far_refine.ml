open Ast
open Far_modules.Vertex

let contains us s = failwith "TODO"

let all_subs fc = failwith "TODO"

let find_extra_no_oracle v1 t v2 used_sub fc =
  let subs = all_subs fc in
  let rec fe = function
    | [] -> assert false
    | [_] -> Far_cube.negate_formula_to_uclause fc
    | sub::tl -> 
      if contains used_sub sub then fe tl
      else 
        let ucl = Far_cube.negate_formula_to_uclause fc in
        failwith "TODO"
  in fe subs  

let find_extra_oracle v1 t v2 us fc = failwith "TODO"

let approximate_negation v1 t v2 us fc = 
  if Options.far_level = 0 then Far_cube.negate_formula_to_uclause fc
  else if Options.far_level = 1 then find_extra_no_oracle v1 t v2 us fc
  else if Options.far_level = 2 then find_extra_oracle v1 t v2 us fc
  else assert false
      
let refine v1 t v2 =
  List.fold_left (
    fun (used_sub, node_list) fc ->
      let sub, node = approximate_negation v1 t v2 used_sub fc in
      (sub :: used_sub, node :: node_list)
  ) [] v2.bad
      
