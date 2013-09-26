module M = Why3.Term.Mterm

type ('a, 'b) map = 'b M.t

open Fol__FOL

let mixfix_lblsmnrb m a b =
  List.fold_left (fun m f -> M.add f b m) (M.add a b m)
		 (Translation.dnf_to_conj_list a)
  (* M.add a b m *)

let mixfix_lbrb m a = M.find a m

let empty = M.empty
