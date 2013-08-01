(* This file has been generated from Why3 theory Reachability *)

(*---------- Helper functions ----------------*)
let conj_to_cube = function
  | And l -> 
    List.fold_left (fun acc x -> SAtom.add x acc) SAtom.empty l
  | _ -> assert false

let fol_to_cubes = function
  | Lit x -> [SAtom.singleton x]
  | And _ as f -> [conj_to_cube f]
  | Or l -> List.map conj_to_cube l
  | _ -> assert false

let cube_to_fol sa = 
  And (SAtom.fold (fun x acc -> Lit x :: acc) sa [])

let cubes_to_fol = function
  | [] -> []
  | [sa] -> cubes_to_fol sa
  | lsa -> Or (List.map cube_to_fol lsa)
(*--------------------------------------------*)


let pre (x: Fol__FOL.t) : Fol__FOL.t =
  let res_cubes = 
    List.fold_left (fun acc sa ->
      let sa, (args, _) = proper_cube sa in
      let arr_sa = ArrayAtom.of_satom sa in
      let sys = { global_system with 
	t_unsafe = args, sa;
	t_arru = arr_sa;
	t_alpha = ArrayAtom.alpha arr_sa args } in
      pre_system sys :: acc
    ) [] (fol_to_cubes x)
  in
  cubes_to_fol res_cubes



let pre_star (x: Fol__FOL.t) : Fol__FOL.t =
  failwith "to be implemented" (* uninterpreted symbol *)

let reachable (init: Fol__FOL.t) (f: Fol__FOL.t) : bool =
  Fol__FOL.sat Fol__FOL.infix_et (pre_star f) init


