(* This file has been generated from Why3 theory Reachability *)

let pre (x: Fol__FOL.t) : Fol__FOL.t =
  failwith "to be implemented" (* uninterpreted symbol *)

let pre_star (x: Fol__FOL.t) : Fol__FOL.t =
  failwith "to be implemented" (* uninterpreted symbol *)

let reachable (init: Fol__FOL.t) (f: Fol__FOL.t) : bool =
  Fol__FOL.sat Fol__FOL.infix_et (pre_star f) init


