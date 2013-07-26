(* This file has been generated from Why3 theory FOL *)
open Ast
open Set__Fset

type t = set

(* type structure to be defined (uninterpreted type) *)

(* let infix_breq (x: structure) (x1: t) : bool = *)
(*   failwith "to be implemented" (\* uninterpreted symbol *\) *)

let ffalse  : t = SAtom.singleton False

let ttrue  : t = SAtom.singleton True

let neg (x: t) : t =
  

  failwith "to be implemented" (* uninterpreted symbol *)

let (&) (x: t) (x1: t) : t =
  failwith "to be implemented" (* uninterpreted symbol *)

let (++) (x: t) (x1: t) : t =
  failwith "to be implemented" (* uninterpreted symbol *)

let (=>) (x: t) (x1: t) : t =
  failwith "to be implemented" (* uninterpreted symbol *)

let (|=) (x: t) (x1: t) : bool =
  failwith "to be implemented" (* uninterpreted symbol *)

let sat (f: t) : bool =
  failwith "to be implemented" (* not executable *)
  (* exists m:structure. m |= f *)

let valid (f: t) : bool = not (sat (prefix_tl f))


