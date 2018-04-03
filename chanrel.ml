
open Channels



module Rel = struct

  type t = HSet.t HMap.t * HSet.t HMap.t * HSet.t HMap.t

  let empty = HMap.empty, HMap.empty, HMap.empty

  let iter_internal f = HMap.iter (fun ef -> HSet.iter (f ef))

  let iter_lt f (_, succ, _) = iter_internal f succ

  let iter_eq f (_, _, equ) = iter_internal f equ

  let fold_internal f = HMap.fold (fun ef -> HSet.fold (f ef))

  let fold_lt f (_, succ, _) = fold_internal f succ

  let fold_eq f (_, _, equ) = fold_internal f equ

  let exists_internal f = HMap.exists (fun ef -> HSet.exists (f ef))

  let exists_lt f (_, succ, _) = exists_internal f succ

  let exists_eq f (_, _, equ) = exists_internal f equ

  let mem_internal ef et rel =
    try HSet.mem et (HMap.find ef rel)
    with Not_found -> false

  let mem_lt ef et (_, succ, _) = mem_internal ef et succ

  let mem_eq e1 e2 (_, _, equ) = mem_internal e1 e2 equ

  let print_lt fmt =
    iter_lt (fun ef et -> Format.fprintf fmt "%a < %a " H.print ef H.print et)

  let print_eq fmt =
    iter_eq (fun e1 e2 -> Format.fprintf fmt "%a = %a " H.print e1 H.print e2)

  (* let find_pred e (pred, _, _) = HMap.find e pred *)

  (* let find_succ e (_, succ, _) = HMap.find e succ *)

  (* let find_eq e (_, _, equ) = HMap.find e equ *)

  let get_pred e (pred, _, _) =
    try HMap.find e pred with Not_found -> HSet.empty

  let get_succ e (_, succ, _) =
    try HMap.find e succ with Not_found -> HSet.empty

  let get_equ e (_, _, equ) =
    try HMap.find e equ with Not_found -> HSet.empty

  let add_internal nef net rel =
    HSet.fold (fun ef rel ->
      let cet = try HMap.find ef rel with Not_found -> HSet.empty in
      HMap.add ef (HSet.union net cet) rel
    ) nef rel

  let add_lt ef et ((pred, succ, equ) as rel) =
    let ef' = HSet.add ef (get_equ ef rel) in
    let et' = HSet.add et (get_equ et rel) in
    let pef = HSet.union (get_pred ef rel) ef' in
    let set = HSet.union (get_succ et rel) et' in
    let pred = add_internal set pef pred in
    let succ = add_internal pef set succ in
    (* Format.fprintf Format.std_formatter "Added %a, %a, rel is : %a\n" *)
    (*   H.print ef H.print et print_lt (pred, succ, equ); *)
    (pred, succ, equ)

  let add_eq e1 e2 ((pred, succ, equ) as rel) =
    let e1' = HSet.add e1 (get_equ e1 rel) in
    let e2' = HSet.add e2 (get_equ e2 rel) in
    let pe1 = get_pred e1 rel in
    let pe2 = get_pred e2 rel in
    let se1 = get_succ e1 rel in
    let se2 = get_succ e2 rel in
    let pred = add_internal se1 pe2 pred in
    let pred = add_internal se1 e2' pred in
    let pred = add_internal e1' pe2 pred in
    let pred = add_internal se2 pe1 pred in
    let pred = add_internal se2 e1' pred in
    let pred = add_internal e2' pe1 pred in
    let succ = add_internal pe1 se2 succ in
    let succ = add_internal pe1 e2' succ in
    let succ = add_internal e1' se2 succ in
    let succ = add_internal pe2 se1 succ in
    let succ = add_internal pe2 e1' succ in
    let succ = add_internal e2' se1 succ in
    let equ = add_internal e1' e2' equ in
    let equ = add_internal e2' e1' equ in
    (pred, succ, equ)

  let diff_internal rel1 rel2 =
    HMap.fold (fun e es1 rel ->
      let es2 = try HMap.find e rel2 with Not_found -> HSet.empty in
      let es = HSet.diff es1 es2 in
      if HSet.is_empty es then rel
      else HMap.add e es rel
    ) rel1 HMap.empty

  let diff (pred1, succ1, equ1) (pred2, succ2, equ2) = (* R1 - R2 *)
    let pred = diff_internal pred1 pred2 in
    let succ = diff_internal succ1 succ2 in
    let equ = diff_internal equ1 equ2 in
    (pred, succ, equ)

  let acyclic (_, succ, _) =
    not (HMap.exists HSet.mem succ)

end



open Types
open Util (* for timers *)



let extract_rels ghb = function
  | Atom.Comp (Access (a, [ef; et]), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a, [ef; et])) when H.equal a hGhb ->
     Rel.add_lt ef et ghb
  | Atom.Comp (Access (a, [e1; e2]), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a, [e1; e2])) when H.equal a hSync ->
     Rel.add_eq e1 e2 ghb
  | _ -> ghb

let extract_rels_array ar =
  (* TimeGhb.start (); *)
  let r = Array.fold_left (fun acc a -> extract_rels acc a) Rel.empty ar in
  (* TimeGhb.pause (); *)
  r

let extract_rels_set sa =
  (* TimeGhb.start (); *)
  let r = SAtom.fold (fun a acc -> extract_rels acc a) sa Rel.empty in
  (* TimeGhb.pause (); *)
  r



let filter_rels_array ar =
  Array.fold_left (fun sa at -> match at with
    | Atom.Comp (Access (a, _), Eq, Elem _)
    | Atom.Comp (Elem _, Eq, Access (a, _))
       when H.equal a hSync || H.equal a hGhb -> sa
    | _ -> SAtom.add at sa
  ) SAtom.empty ar

let filter_rels_set sa =
  SAtom.filter (function
    | Atom.Comp (Access (a, _), Eq, Elem _)
    | Atom.Comp (Elem _, Eq, Access (a, _))
       when H.equal a hSync || H.equal a hGhb -> false
    | _ -> true
  ) sa
