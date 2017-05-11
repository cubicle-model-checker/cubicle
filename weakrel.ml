
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



let find_event_safe e evts =
  try HMap.find e evts with Not_found -> (hNone, hNone, hNone, [])

let extract_rels (sa, (fce, ghb, sync)) at = match at with
  | Atom.Comp (Access (a, [p; e]), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a, [p; e])) when H.equal a hFence ->
     let pfce = try HMap.find p fce with Not_found -> HSet.empty in
     let fce = HMap.add p (HSet.add e pfce) fce in
     (sa, (fce, ghb, sync))
  | Atom.Comp (Access (a, [ef; et]), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a, [ef; et])) when H.equal a hGhb ->
     (sa, (fce, H2Set.add (ef, et) ghb, sync))
  | Atom.Comp (Access (a, sl), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a, sl)) when H.equal a hSync ->
     (sa, (fce, ghb, (HSet.of_list sl) :: sync))
  | _ -> (SAtom.add at sa, (fce, ghb, sync))



let init_acc = (SAtom.empty, (HMap.empty, H2Set.empty, []))

let extract_rels_array evts ar =
  Array.fold_left (fun acc a -> extract_rels acc a) init_acc ar

let extract_rels_set evts sa =
  SAtom.fold (fun a acc -> extract_rels acc a) sa init_acc


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


let add_rel_aux rel nef net =
  let pre = H2Set.filter (fun (_, et) -> H.equal et nef) rel in
  let post = H2Set.filter (fun (ef, _) -> H.equal net ef) rel in
  let pre = H2Set.add (nef, net) pre in
  let post = H2Set.add (nef, net) post in
  H2Set.fold (fun (ef, _) rel ->
    H2Set.fold (fun (_, et) rel -> H2Set.add (ef, et) rel) post rel
  ) pre rel

let add_rel sync rel nef net =
  let sef = try List.find (HSet.mem nef) sync
            with Not_found -> HSet.singleton nef in
  let set = try List.find (HSet.mem net) sync
            with Not_found -> HSet.singleton net in
  HSet.fold (fun nef rel ->
    HSet.fold (fun net rel -> add_rel_aux rel nef net) set rel
  ) sef rel



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
