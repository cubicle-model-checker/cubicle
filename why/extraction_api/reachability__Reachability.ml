(* This file has been generated from Why3 theory Reachability *)

module CPretty = Pretty
open Why3
open Ast
open Format


let pre (x: Fol__FOL.t) : Fol__FOL.t =
  let res_cubes = 
    List.fold_left (fun acc s ->
      let ls, post = Bwreach.pre_system s in
      List.rev_append ls (List.rev_append post  acc)
    ) [] (Fol__FOL.fol_to_cubes x)
  in
  Fol__FOL.cubes_to_fol res_cubes




let pre_star (x: Fol__FOL.t) : Fol__FOL.t =
  failwith "to be implemented" (* uninterpreted symbol *)

let reachable (init: Fol__FOL.t) (f: Fol__FOL.t) : bool =
  (*-----------------  Begin manually edited ------------------*)
  Fol__FOL.sat (Fol__FOL.infix_et (pre_star f) init)
  (*------------------  End manually edited -------------------*)


