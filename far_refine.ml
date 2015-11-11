open Ast
open Far_modules.Vertex

let approximate_negation cube = 
  if Options.far_level = 0 then Far_cube.negate_formula_to_uclause cube
  else failwith "TODO"

let refine v1 t v2 =
  List.fold_left (
    fun acc cube ->
      (approximate_negation cube) :: acc
  ) [] v2.bad
      
