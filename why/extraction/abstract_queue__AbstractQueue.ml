(* This file has been generated from Why3 module AbstractQueue *)

type f = Fol__FOL.t

type t =
  { mutable formula: Fol__FOL.t; mutable elts: Fol__FOL.t Set__Fset.set }

let create (us: unit) : t = failwith "to be implemented" (* val *)



let push (f: Fol__FOL.t) (q: t) : unit =
  failwith "to be implemented" (* val *)



exception Empty

let is_empty (q: t) : bool = failwith "to be implemented" (* val *)



let pop (q: t) : Fol__FOL.t = failwith "to be implemented" (* val *)



let clear (q: t) : unit = failwith "to be implemented" (* val *)



let copy (q: t) : t = failwith "to be implemented" (* val *)




