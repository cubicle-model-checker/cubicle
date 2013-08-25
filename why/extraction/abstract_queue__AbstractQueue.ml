(* This file has been generated from Why3 module AbstractQueue *)
module F = Fol__FOL
(* module S = Set__Fset *)
module Q = Queue
open F

type f = F.t

type t =
  { mutable formula: Fol__FOL.t;
    (* mutable elts: Fol__FOL.t Set__Fset.set *)
    elts : Fol__FOL.t Queue.t }

let create (us: unit) : t =
  { formula = ffalse;
    elts = Q.create () }
  

let push (f: Fol__FOL.t) (q: t) : unit =
  let l = match f with
    | Lit _ | And _ | Exists _ | Forall _ | Not _ -> [f]
    | Or l -> l
  in
  List.iter (fun f ->
    q.formula <- f ++ q.formula;
    Q.push f q.elts
  ) l


exception Empty

let is_empty (q: t) : bool = Q.is_empty q.elts


let pop (q: t) : Fol__FOL.t =
  let r = try Q.pop q.elts with Q.Empty -> raise Empty in
  q.formula <- (neg r) & q.formula;
  r


let clear (q: t) : unit =
  Q.clear q.elts;
  q.formula <- ffalse


let copy (q: t) : t =
  { formula = q.formula;
    elts = Q.copy q.elts }

