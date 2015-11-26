open Ast
open Types
open Far_modules

let contains_sa us s = List.exists (SAtom.equal s) us

let contains_node cnf n = List.exists (Far_cube.equivalent n) cnf

let all_subs fc = 
  let rec all_rec acc = function
    | [] -> acc
    | x :: l ->
      let nacc = List.rev_map (
        fun a -> SAtom.add x a ) acc
      in
      let acc = List.rev_append nacc acc in
      all_rec acc l
  in
  let elts = SAtom.elements (Far_cube.litterals fc) in
  let l = all_rec [SAtom.empty] elts in
  List.tl (List.fast_sort (
    fun sa1 sa2 -> Pervasives.compare 
      (SAtom.cardinal sa1) (SAtom.cardinal sa2)
  ) l)


let find_extra_no_oracle v1 t v2 used_sub fc =
  let subs = all_subs fc in
  let rec fe = function
    | [] -> assert false
    | [s] -> Some (s, Far_cube.negate_formula_to_uclause fc)
    | sub::tl -> 
      let fc = Far_cube.create (Cube.create_normal sub) in
      let ucl = Far_cube.negate_formula_to_uclause fc in
      if contains_node v2.world ucl then fe tl
      else
        if Vertex.world_to_cube v1 t fc then
          fe tl
        else (
          if contains_sa used_sub sub then None
          else Some (sub, ucl)
        )
  in fe subs  

let find_extra_oracle v1 t v2 used_sub fc = 
  let subs = Approx.Selected.all_goods fc in
  let rec fe = function
    | [] -> Some (Far_cube.litterals fc, Far_cube.negate_formula_to_uclause fc)
    | sub::tl -> 
      let fc = Far_cube.create (Cube.create_normal sub) in
      let ucl = Far_cube.negate_formula_to_uclause fc in
      if contains_node v2.world ucl then fe tl
      else
        if Vertex.world_to_cube v1 t fc then
          fe tl
        else (
          if contains_sa used_sub sub then None
          else Some (sub, ucl)
        )
  in fe (List.map (fun s -> Far_cube.litterals s) subs)

let approximate_negation v1 t v2 us fc = 
  if Options.far_level = 0 then 
    Some (Far_cube.litterals fc, Far_cube.negate_formula_to_uclause fc)
  else if Options.far_level = 1 then find_extra_no_oracle v1 t v2 us fc
  else if Options.far_level = 2 then find_extra_oracle v1 t v2 us fc
  else assert false
      
let refine v1 t v2 =
  let (_, nl) = List.fold_left (
    fun (used_sub, node_list) fc ->
      let r = approximate_negation v1 t v2 used_sub fc in
      match r with
        | None -> used_sub, node_list
        | Some (sub, node) -> (sub :: used_sub, node :: node_list)
  ) ([], []) v2.bad in
  nl
      
