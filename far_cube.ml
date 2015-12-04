open Ast
open Types

include Node

let negate_formula_same_vars c =
  let l = litterals c in
  let l = SAtom.fold (
    fun a l -> SAtom.add (Atom.neg a) l
  ) l SAtom.empty in
  let v = variables c in
  create (Cube.create v l), v
    
let negate_formula_to_ecube c = 
  let c, v = negate_formula_same_vars c in
  let subst = Variable.build_subst v Variable.procs in
  create (Cube.subst subst c.cube)

let negate_formula_to_uclause cube = 
  let c, v = negate_formula_same_vars cube in
  let subst = Variable.build_subst v Variable.generals in
  create (Cube.subst subst c.cube)

let negate_litterals_to_ecubes = List.map negate_formula_to_ecube

let compare_fcubes fc1 fc2 =
  let s = dim fc1 - dim fc2 in
    if s = 0 then
      size fc1 - size fc2
    else s

let compare_decr_fcubes fc1 fc2 = (~-) (compare_fcubes fc1 fc2)

let inconsistent_clause_cube fcl fcu =
  if compare_fcubes fcl fcu > 0 then false
  else 
    begin
      let vl = variables fcl in
      let vc = variables fcu in
      let sal = litterals fcl in
      let sau = litterals fcu in
      let sigmas = Variable.all_permutations vl vc in
      List.exists (
        fun sigma ->
          let sal = SAtom.subst sigma sal in
          Cube.inconsistent_far sal sau
      ) sigmas
    end        

let cube_implies c cl =
  try 
    let res = List.find (
      fun b -> 
        subset b c
        || inconsistent_clause_cube (negate_formula_to_ecube b) c
    ) cl in
    Some res
  with Not_found -> None

let equivalent fc1 fc2 =
  if compare_fcubes fc1 fc2 <> 0 then false
  else 
    begin
      let c1 = fc1.cube in
      let c2 = fc2.cube in
      let sigmas = Instantiation.relevant ~of_cube:c1 ~to_cube:c2 in
      (* let sigmas = Variable.all_permutations c1.Cube.vars c2.Cube.vars in *)
      let sa1 = c1.Cube.litterals in
      let sa2 = c2.Cube.litterals in
      List.exists (
        fun sigma ->
          let sa1 = SAtom.subst sigma sa1 in
          SAtom.equal sa1 sa2
      ) sigmas
    end

let filter cl =
  let rec fr cl acc =
    match cl with
      | [] -> acc
      | c :: tl -> match cube_implies c acc with
          | Some _ -> fr tl acc
          | None -> fr tl (c::acc)
  in List.rev (fr cl [])

let pre_and_filter t nf =
  let pnf = Far_util.compute_pre t nf in
  let tnf = List.fast_sort (fun n1 n2 -> compare_fcubes n1 n2) pnf in
  let ftnf = filter tnf in
  ftnf


let negate_pre_and_filter t ucnf =
  let nf = negate_litterals_to_ecubes ucnf in
  pre_and_filter t nf
    
let equal fc1 fc2 = ArrayAtom.equal (array fc1) (array fc2)
