
open Types
open Util
open Weakmem
open Weakevent



let filter_rels_array ar =
  Array.fold_left (fun sa at -> match at with
    | Atom.Comp (Access (a, _), Eq, Elem _)
    | Atom.Comp (Elem _, Eq, Access (a, _))
       when H.equal a hFence || H.equal a hSync || H.equal a hGhb -> sa
    | _ -> SAtom.add at sa
  ) SAtom.empty ar

let filter_rels_set sa =
  SAtom.filter (function
    | Atom.Comp (Access (a, _), Eq, Elem _)
    | Atom.Comp (Elem _, Eq, Access (a, _))
       when H.equal a hFence || H.equal a hSync || H.equal a hGhb -> false
    | _ -> true
  ) sa


(* process could be removed in fence (kept for simplicity) *)
(*let extract_rels (fce, ghb, sync) at = match at with
  | Atom.Comp (Access (a, [p; e]), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a, [p; e])) when H.equal a hFence ->
     HMap.add p e fce, ghb, sync
  | Atom.Comp (Access (a, [ef; et]), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a, [ef; et])) when H.equal a hGhb ->
     fce, H2Set.add (ef, et) ghb, sync
  | Atom.Comp (Access (a, [e1; e2]), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a, [e1; e2])) when H.equal a hSync ->
     fce, ghb, H2Set.add (e1, e2) sync
  | _ -> fce, ghb, sync



let init_acc = HMap.empty, H2Set.empty, H2Set.empty

let extract_rels_array ar =
  Array.fold_left (fun acc a -> extract_rels acc a) init_acc ar

let extract_rels_set sa =
  SAtom.fold (fun a acc -> extract_rels acc a) sa init_acc
 *)

(*
(* ghb = ppo U fence U co U rfe U fr *)
let make_ghb evts (_, po, f, rf, co, fr, s) =
  TimeProp.start ();
  
  let prop = H2Set.empty in

  (* ppo *)
  let prop = HMap.fold (fun p ppo prop ->
    H2Set.fold (fun (ef, et) prop ->
      let edf, _ = HMap.find ef evts in
      let edt, _ = HMap.find et evts in
      if is_write edf && is_read edt then prop
      else H2Set.add (ef, et) prop
    ) ppo prop
  ) po prop in

  (* fence *)
  let prop = HMap.fold (fun p pfence prop ->
    H2Set.fold (fun (ef, et) prop ->
      let pre = H2Set.filter (fun (_, pet) -> H.equal pet ef) prop in
      let post = H2Set.filter (fun (pef, _) -> H.equal et pef) prop in
      let pre = H2Set.add (ef, et) pre in
      let post = H2Set.add (ef, et) post in
      H2Set.fold (fun (pef, _) prop ->
        H2Set.fold (fun (_, pet) prop ->
          H2Set.add (pef, pet) prop
        ) post prop
      ) pre prop
    ) pfence prop
  ) f prop in

  (* co *)
  let prop = H2Set.fold (fun (ef, et) prop ->
    let pre = H2Set.filter (fun (_, pet) -> H.equal pet ef) prop in
    let post = H2Set.filter (fun (pef, _) -> H.equal et pef) prop in
    let pre = H2Set.add (ef, et) pre in
    let post = H2Set.add (ef, et) post in
    H2Set.fold (fun (pef, _) prop ->
      H2Set.fold (fun (_, pet) prop ->
        H2Set.add (pef, pet) prop
      ) post prop
    ) pre prop
  ) co prop in

  (* rfe *)  
  let prop = HMap.fold (fun wef retl prop ->
    let (pf, _, _, _), _ = HMap.find wef evts in
    let retl = List.filter (fun ret ->
      let (pt, _, _, _), _ = HMap.find ret evts in
      not (H.equal pf pt)
    ) retl in
    let pre = H2Set.filter (fun (_, pet) -> H.equal pet wef) prop in
    let post = H2Set.filter (fun (pef, _) ->
                 List.exists (fun ret -> H.equal ret pef) retl) prop in
    let pre = List.fold_left (fun pre ret ->
                H2Set.add (wef, ret) pre) pre retl in
    let post = List.fold_left (fun post ret ->
                 H2Set.add (wef, ret) post) post retl in
    H2Set.fold (fun (pef, _) prop ->
      H2Set.fold (fun (_, pet) prop ->
        H2Set.add (pef, pet) prop
      ) post prop
    ) pre prop
  ) rf prop in

  (* fr *)
  let prop = HMap.fold (fun _ref wetl prop ->
    let pre = H2Set.filter (fun (_, pet) -> H.equal pet _ref) prop in
    let post = H2Set.filter (fun (pef, _) ->
                 List.exists (fun wet -> H.equal wet pef) wetl) prop in
    let pre = List.fold_left (fun pre wet ->
                H2Set.add (_ref, wet) pre) pre wetl in
    let post = List.fold_left (fun post wet ->
                 H2Set.add (_ref, wet) post) post wetl in
    H2Set.fold (fun (pef, _) prop ->
      H2Set.fold (fun (_, pet) prop ->
        H2Set.add (pef, pet) prop
      ) post prop
    ) pre prop
  ) fr prop in

  let sync = List.fold_left (fun ss sync ->
    let ss = ref ss in
    let sync = ref sync in
    while not (HSet.is_empty !sync) do
      let e1 = HSet.choose !sync in
      sync := HSet.remove e1 !sync;
      try
        let e2 = HSet.choose !sync in
        ss := H2Set.add (e1, e2) !ss
      with Not_found -> ()
    done;
    !ss
  ) H2Set.empty s in

  let prop = H2Set.fold (fun (e1, e2) prop ->
    let pre_e1 = H2Set.fold (fun (pef, pet) pre_e1 ->
      if H.equal pet e1 then HSet.add pef pre_e1 else pre_e1
    ) prop HSet.empty in
    let pre_e2 = H2Set.fold (fun (pef, pet) pre_e2 ->
      if H.equal pet e2 then HSet.add pef pre_e2 else pre_e2
    ) prop HSet.empty in
    let post_e1 = H2Set.fold (fun (pef, pet) post_e1 ->
      if H.equal pef e1 then HSet.add pet post_e1 else post_e1
    ) prop HSet.empty in
    let post_e2 = H2Set.fold (fun (pef, pet) post_e2 ->
      if H.equal pef e2 then HSet.add pet post_e2 else post_e2
    ) prop HSet.empty in
    let prop = HSet.fold (fun pre prop ->
      HSet.fold (fun post prop -> H2Set.add (pre, post) prop) post_e2 prop
    ) pre_e1 prop in
    let prop = HSet.fold (fun pre prop ->
      HSet.fold (fun post prop -> H2Set.add (pre, post) prop) post_e1 prop
    ) pre_e2 prop in
    let prop = HSet.fold (fun pre prop ->
      H2Set.add (pre, e2) prop) pre_e1 prop in
    let prop = HSet.fold (fun pre prop ->
      H2Set.add (pre, e1) prop) pre_e2 prop in
    let prop = HSet.fold (fun post prop ->
      H2Set.add (e2, post) prop) post_e1 prop in
    let prop = HSet.fold (fun post prop ->
      H2Set.add (e1, post) prop) post_e2 prop in
    prop
  ) sync prop in

  TimeProp.pause ();

  prop
 *)


(*
(* scloc = po_loc U co U rf U fr *)
let make_scloc evts (_, po, f, rf, co, fr, s) =
  TimeProp.start ();
  
  let scloc = H2Set.empty in

  (* po_loc *)
  let scloc = HMap.fold (fun p ppo scloc ->
    H2Set.fold (fun (ef, et) scloc ->
      let edf, _ = HMap.find ef evts in
      let edt, _ = HMap.find et evts in
      if not (same_var edf edt) then scloc
      else H2Set.add (ef, et) scloc
    ) ppo scloc
  ) po scloc in

  (* co *)
  let scloc = H2Set.fold (fun (ef, et) scloc ->
    let pre = H2Set.filter (fun (_, pet) -> H.equal pet ef) scloc in
    let post = H2Set.filter (fun (pef, _) -> H.equal et pef) scloc in
    let pre = H2Set.add (ef, et) pre in
    let post = H2Set.add (ef, et) post in
    H2Set.fold (fun (pef, _) scloc ->
      H2Set.fold (fun (_, pet) scloc ->
        H2Set.add (pef, pet) scloc
      ) post scloc
    ) pre scloc
  ) co scloc in

  (* rf *)  
  let scloc = HMap.fold (fun wef retl scloc ->
    let pre = H2Set.filter (fun (_, pet) -> H.equal pet wef) scloc in
    let post = H2Set.filter (fun (pef, _) ->
                 List.exists (fun ret -> H.equal ret pef) retl) scloc in
    let pre = List.fold_left (fun pre ret ->
                H2Set.add (wef, ret) pre) pre retl in
    let post = List.fold_left (fun post ret ->
                 H2Set.add (wef, ret) post) post retl in
    H2Set.fold (fun (pef, _) scloc ->
      H2Set.fold (fun (_, pet) scloc ->
        H2Set.add (pef, pet) scloc
      ) post scloc
    ) pre scloc
  ) rf scloc in

  (* fr *)
  let scloc = HMap.fold (fun _ref wetl scloc ->
    let pre = H2Set.filter (fun (_, pet) -> H.equal pet _ref) scloc in
    let post = H2Set.filter (fun (pef, _) ->
                 List.exists (fun wet -> H.equal wet pef) wetl) scloc in
    let pre = List.fold_left (fun pre wet ->
                H2Set.add (_ref, wet) pre) pre wetl in
    let post = List.fold_left (fun post wet ->
                 H2Set.add (_ref, wet) post) post wetl in
    H2Set.fold (fun (pef, _) scloc ->
      H2Set.fold (fun (_, pet) scloc ->
        H2Set.add (pef, pet) scloc
      ) post scloc
    ) pre scloc
  ) fr scloc in

  let sync = List.fold_left (fun ss sync ->
    let ss = ref ss in
    let sync = ref sync in
    while not (HSet.is_empty !sync) do
      let e1 = HSet.choose !sync in
      sync := HSet.remove e1 !sync;
      try
        let e2 = HSet.choose !sync in
        ss := H2Set.add (e1, e2) !ss
      with Not_found -> ()
    done;
    !ss
  ) H2Set.empty s in

  let scloc = H2Set.fold (fun (e1, e2) scloc ->
    let pre_e1 = H2Set.fold (fun (pef, pet) pre_e1 ->
      if H.equal pet e1 then HSet.add pef pre_e1 else pre_e1
    ) scloc HSet.empty in
    let pre_e2 = H2Set.fold (fun (pef, pet) pre_e2 ->
      if H.equal pet e2 then HSet.add pef pre_e2 else pre_e2
    ) scloc HSet.empty in
    let post_e1 = H2Set.fold (fun (pef, pet) post_e1 ->
      if H.equal pef e1 then HSet.add pet post_e1 else post_e1
    ) scloc HSet.empty in
    let post_e2 = H2Set.fold (fun (pef, pet) post_e2 ->
      if H.equal pef e2 then HSet.add pet post_e2 else post_e2
    ) scloc HSet.empty in
    let scloc = HSet.fold (fun pre scloc ->
      HSet.fold (fun post scloc -> H2Set.add (pre, post) scloc) post_e2 scloc
    ) pre_e1 scloc in
    let scloc = HSet.fold (fun pre scloc ->
      HSet.fold (fun post scloc -> H2Set.add (pre, post) scloc) post_e1 scloc
    ) pre_e2 scloc in
    let scloc = HSet.fold (fun pre scloc ->
      H2Set.add (pre, e2) scloc) pre_e1 scloc in
    let scloc = HSet.fold (fun pre scloc ->
      H2Set.add (pre, e1) scloc) pre_e2 scloc in
    let scloc = HSet.fold (fun post scloc ->
      H2Set.add (e2, post) scloc) post_e1 scloc in
    let scloc = HSet.fold (fun post scloc ->
      H2Set.add (e1, post) scloc) post_e2 scloc in
    scloc
  ) sync scloc in

  TimeProp.pause ();

  scloc
 *)



             

let add_pairs_aux rel nef net =
  let pre = H2Set.filter (fun (_, et) -> H.equal et nef) rel in
  let post = H2Set.filter (fun (ef, _) -> H.equal net ef) rel in
  let pre = H2Set.add (nef, net) pre in
  let post = H2Set.add (nef, net) post in
  H2Set.fold (fun (ef, _) rel ->
    H2Set.fold (fun (_, et) rel -> H2Set.add (ef, et) rel) post rel
  ) pre rel

let add_pairs_internal sync rel nef net nrel =
  let sef, set = H2Set.fold (fun (e1, e2) (sef, set) ->
    let sef = if H.equal e1 nef then HSet.add e2 sef
              else if H.equal e2 nef then HSet.add e1 sef
              else sef in
    let set = if H.equal e1 net then HSet.add e2 set
              else if H.equal e2 net then HSet.add e1 set
              else set in
    sef, set
  ) sync (HSet.singleton nef, HSet.singleton net) in
  HSet.fold (fun nef nrel ->
    HSet.fold (fun net nrel ->
      let npairs = add_pairs_aux rel nef net in
      H2Set.union npairs nrel
    ) set nrel
  ) sef nrel (* MUST DO SIMPLER : query pre/post first, then add
                                  pairs for all elems in sync *)

let add_pairs sync rel nef net =
  add_pairs_internal sync rel nef net rel

let get_new_pairs sync rel nef net =
  add_pairs_internal sync rel nef net H2Set.empty


(* let acyclic rel = not (H2Set.exists (fun (e1, e2) -> H.equal e1 e2) rel) *)
let acyclic rel =
  not (H2Set.exists (fun (e1a, e2a) ->
    H2Set.exists (fun (e1b, e2b) -> H.equal e1a e2b && H.equal e2a e1b) rel
  ) rel)

(*
let acyclic_n ({ Ast.tag = id; cube = cube } as n) = failwith "Acyclic to fix" (*
  let _, evts, rels = extract_events_set (cube.Cube.litterals) in
  let prop = make_prop evts rels in
  if H2Set.exists (fun (e1a, e2a) ->
     H2Set.exists (fun (e1b, e2b) ->
       H.equal e1a e2b && H.equal e2a e1b
     ) prop
  ) prop
  then raise (Smt.Unsat [])
*)
*)







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


(* process could be removed in fence (kept for simplicity) *)
(* fence do not belong here, should be in events *)
let extract_rels (fce, ghb) at = match at with
  | Atom.Comp (Access (a, [p; e]), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a, [p; e])) when H.equal a hFence ->
     HMap.add p e fce, ghb
  | Atom.Comp (Access (a, [ef; et]), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a, [ef; et])) when H.equal a hGhb ->
     fce, Rel.add_lt ef et ghb
  | Atom.Comp (Access (a, [e1; e2]), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a, [e1; e2])) when H.equal a hSync ->
     fce, Rel.add_eq e1 e2 ghb
  | _ -> fce, ghb


let init_acc = HMap.empty, Rel.empty

let extract_rels_array ar =
  TimeGhb.start ();
  let r = Array.fold_left (fun acc a -> extract_rels acc a) init_acc ar in
  TimeGhb.pause ();
  r

let extract_rels_set sa =
  TimeGhb.start ();
  let r = SAtom.fold (fun a acc -> extract_rels acc a) sa init_acc in
  TimeGhb.pause ();
  r



let subst sigma (fces, ghb) =
  let fces = HMap.fold (fun p e fces ->
    HMap.add (Variable.subst sigma p) e fces
  ) fces HMap.empty in
  fces, ghb


