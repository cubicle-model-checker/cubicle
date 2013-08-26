module M = Map.Make (Fol__FOL)

type ('a, 'b) map = 'b M.t

open Fol__FOL

let mixfix_lblsmnrb m a b =
  let l = match a with
    | Lit _ | And _ | Exists _ | Forall _ | Not _ -> [a]
    | Or l -> l
  in
  List.fold_left (fun m f -> M.add f b m) (M.add a b m) l

let mixfix_lbrb m a = M.find a m

let empty = M.empty
