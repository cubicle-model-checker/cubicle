
open Weakmem
open Types
open Util

module T = Smt.Term
module F = Smt.Formula



module RInt = struct
  type t = int
  let compare x y = - (Pervasives.compare x y)
end

module RIntMap = Map.Make (RInt)



(* Used internally by extract_event *)
let find_event_safe e evts =
  try HMap.find e evts with Not_found -> (hNone, hNone, hNone, [])

(* Extract events, rf, fences and sync from sa (rf/fences/sync removed)
   Used when making formula for safety / fixpoint check *)
let extract_events (sa, evts, fce, rf, co, fr, rmw, sync) at = match at with
  | Atom.Comp (Access (a, [p; e]), Eq, Elem _)(*warning,several procs possible*)
  | Atom.Comp (Elem _, Eq, Access (a, [p; e])) when H.equal a hFence ->
     let pfce = try HMap.find p fce with Not_found -> HSet.empty in
     let fce = HMap.add p (HSet.add e pfce) fce in (*or use a better predicate*)
     (sa, evts, fce, rf, co, fr, rmw, sync)
  | Atom.Comp (Access (a, [ew; er]), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a, [ew; er])) when H.equal a hRf ->
     let erl = try HMap.find ew rf with Not_found -> [] in
     (sa, evts, fce, HMap.add ew (er :: erl) rf, co, fr, rmw, sync)
  | Atom.Comp (Access (a, [ewf; ewt]), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a, [ewf; ewt])) when H.equal a hCo ->
     let ewtl = try HMap.find ewf co with Not_found -> [] in
     (sa, evts, fce, rf, HMap.add ewf (ewt :: ewtl) co, fr, rmw, sync)
  | Atom.Comp (Access (a, [er; ew]), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a, [er; ew])) when H.equal a hFr ->
     let ewl = try HMap.find er fr with Not_found -> [] in
     (sa, evts, fce, rf, co, HMap.add er (ew :: ewl) fr, rmw, sync)
  | Atom.Comp (Access (a, [er; ew]), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a, [er; ew])) when H.equal a hRmw ->
     let ewl = try HMap.find er rmw with Not_found -> [] in
     (sa, evts, fce, rf, co, fr, HMap.add er (ew :: ewl) rmw, sync)
  | Atom.Comp (Access (a, sl), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a, sl)) when H.equal a hSync ->
     (sa, evts, fce, rf, co, fr, rmw, (HSet.of_list sl) :: sync)
  | Atom.Comp (Field (Access (a, [e]), f), Eq, Elem (c, t))
  | Atom.Comp (Elem (c, t), Eq, Field (Access (a, [e]), f)) when H.equal a hE ->
     let (p, d, v, vi) as evt = find_event_safe e evts in
     let evt = if H.equal f hThr then (c, d, v, vi)
          else if H.equal f hDir then (p, c, v, vi)
	  else if H.equal f hVar then (p, d, c, vi)
          else if is_param f then (p, d, v, (f, c) :: vi)
          else evt in
     (SAtom.add at sa, HMap.add e evt evts, fce, rf, co, fr, rmw, sync)
  | Atom.Comp (Read _, _, _) | Atom.Comp (_, _, Read _) ->
     failwith "Weakorder.extract_events : Read should not be there"
  | Atom.Comp (Write _, _, _) | Atom.Comp (_, _, Write _) ->
     failwith "Weakorder.extract_events : Write should not be there"
  | Atom.Comp (Fence _, _, _) | Atom.Comp (_, _, Fence _) ->
     failwith "Weakorder.extract_events : Fence should not be there"
  | Atom.Ite _ ->
     failwith "Weakorder.extract_events : Ite should not be there"
  | _ -> (SAtom.add at sa, evts, fce, rf, co, fr, rmw, sync)



let are_sync sync e1 e2 =
  List.exists (fun ss -> HSet.mem e1 ss && HSet.mem e2 ss) sync

let make_po eids sync =
  HMap.fold (fun p peids po ->
    let peids = ref peids in
    let ppo = ref H2Set.empty in
    while not (RIntMap.is_empty !peids) do
      let ef, hEf = RIntMap.min_binding !peids in
      peids := RIntMap.remove ef !peids;
      ppo := RIntMap.fold (fun et hEt ppo ->
        if are_sync sync hEf hEt then ppo
        else H2Set.add (hEf, hEt) ppo
      ) !peids !ppo
    done;
    HMap.add p !ppo po
  ) eids HMap.empty

let make_fence eids fce evts = (* no need to use sync *)
  HMap.fold (fun p peids fence ->
    let pfce = try HMap.find p fce with Not_found -> HSet.empty in
    let peids = ref peids in
    let pfence = ref H2Set.empty in
    while not (RIntMap.is_empty !peids) do
      let ef, hEf = RIntMap.min_binding !peids in
      peids := RIntMap.remove ef !peids;
      let (_, df, _, _) = HMap.find hEf evts in
      if H.equal df hW then
        let f = ref false in
        pfence := RIntMap.fold (fun et hEt pfence ->
          if HSet.mem hEt pfce then f := true;
          if !f = false then pfence else
          let (_, dt, _, _) = HMap.find hEt evts in
          if H.equal dt hR then H2Set.add (hEf, hEt) pfence else pfence
        ) !peids !pfence;
    done;
    HMap.add p !pfence fence
  ) eids HMap.empty

let make_co co =
  HMap.fold (fun wef wetl co ->
    List.fold_left (fun co wet -> H2Set.add (wef, wet) co) co wetl
  ) co H2Set.empty



let init_acc =
  (SAtom.empty, HMap.empty, HMap.empty, HMap.empty,
   HMap.empty, HMap.empty, HMap.empty, [])

let post_process (sa, evts, fce, rf, co, fr, rmw, sync) =
  let eids = HMap.fold (fun e ((p, _, _, _)) eids ->
    let peids = try HMap.find p eids with Not_found -> RIntMap.empty in
    HMap.add p (RIntMap.add (int_of_e e) e peids) eids) evts HMap.empty in
  let evts = HMap.map sort_params evts in
  sa, evts, (make_po eids sync, make_fence eids fce evts,
             rf, make_co co, fr, rmw, sync)

(* Used when making formula for safety / fixpoint check *)
let extract_events_array ar =
  post_process (Array.fold_left (fun acc a -> extract_events acc a) init_acc ar)

(* Used when making formula for safety / fixpoint check *)
let extract_events_set sa =
  post_process (SAtom.fold (fun a acc -> extract_events acc a) sa init_acc)



let is_rmw ef et rmw =
  try
    let ewl = HMap.find ef rmw in
    List.exists (fun ew -> H.equal ew et) ewl
  with Not_found -> false
                                        
let gen_po_pred pred evts (po, _, _, _, _, rmw, _) =
  HMap.fold (fun p ppo pol ->
    H2Set.fold (fun (ef, et) pol ->
      if pred (HMap.find ef evts) (HMap.find et evts)
         && not (is_rmw ef et rmw)
      then [ef; et] :: pol else pol
    ) ppo pol
  ) po []

let gen_po_loc = gen_po_pred (fun ed1 ed2 -> same_var ed1 ed2)

let gen_ppo_tso = gen_po_pred (fun ed1 ed2 -> not (is_write ed1 && is_read ed2))

let gen_fence evts (_, fence, _, _, _, _, _) =
  HMap.fold (fun p pfence fl ->
    H2Set.fold (fun (ew, er) fl -> [ew; er] :: fl) pfence fl
  ) fence []

let gen_rf_pred pred evts (_, _, rf, _, _, _, _) =
  HMap.fold (fun ew erl rfl ->
    let pw, _, _, _ = HMap.find ew evts in
    List.fold_left (fun rfl er ->
      let pr, _, _, _ = HMap.find er evts in
      if pred (pw, ew) (pr, er)
      then [ew; er] :: rfl else rfl
    ) rfl erl
  ) rf []

let gen_rf = gen_rf_pred (fun _ _ -> true)

let gen_rfe = gen_rf_pred (fun (pw, _) (pr, _) -> not (H.equal pw pr))

let gen_co evts (_, _, _, co, _, _, _) =
  H2Set.fold (fun (ewf, ewt) col -> [ewf; ewt] :: col) co []

let gen_rmw evts (_, _, _, _, _, rmw, _) =
  HMap.fold (fun er ewl rmwl ->
    List.fold_left (fun rmwl ew ->    
      [er; ew] :: rmwl
    ) rmwl ewl
  ) rmw []

let gen_sync evts (_, _, _, _, _, _, sync) = (* union find on map instead of array *)
  List.fold_left (fun sl sync ->
    let sl = ref sl in
    let sync = ref sync in
    while not (HSet.is_empty !sync) do
      let e1 = HSet.choose !sync in
      sync := HSet.remove e1 !sync;
      try
        let e2 = HSet.choose !sync in
        sl := [e1; e2] :: !sl
      with Not_found -> ()
    done;
    !sl
  ) [] sync

let gen_fr evts (_, _, rf, co, fr, rmw, _) =
  let frl = HMap.fold (fun er ewl frl ->
    List.fold_left (fun frl ew -> [er; ew] :: frl) frl ewl
  ) fr [] in
  HMap.fold (fun ew erl frl ->
    let post = H2Set.filter (fun (ewf, ewt) -> H.equal ewf ew) co in
    List.fold_left (fun frl er ->
      let edr = HMap.find er evts in
      H2Set.fold (fun (_, ewt) frl ->
        let edw = HMap.find ewt evts in
        if same_var edr edw
           && not (is_rmw er ewt rmw)
        then [er; ewt] :: frl else frl
      ) post frl
    ) frl erl
  ) rf frl
  
(*
let filter_writes evts =
  HMap.filter (fun e ed -> is_write ed) evts

let gen_co evts (po, _, _, _, _, _) =
  let writes = filter_writes evts in
  (* Initial writes *)
  let co = HMap.fold (fun et (pt, _, _, _) co ->
    if H.equal pt hP0 then co
    else [hE0; et] :: co
  ) writes [] in
  (* Writes from the same thread *)
  HMap.fold (fun p ppo co ->
    H2Set.fold (fun (ef, et) co ->
      try
        if same_var (HMap.find ef writes) (HMap.find et writes)
        then [ef; et] :: co else co
      with Not_found -> co
    ) ppo co
  ) po co

(* more refinements to do :
   if p1:RX reads from p2:WX, then
    - all p1:WX that are po-before p1:RX are co-before P2:WX
    - all p1:WX that are po-after p1:RX are co-after P2:WX
*)

let get_rf_from_write_to_proc evts rf pwr ewr p =
  HMap.fold (fun ew rl rfp ->
    let (pw, _, _, _) = HMap.find ew evts in
    if H.equal pwr pw && H.equal ewr ew then
      List.fold_left (fun rfp er ->
        let (pr, _, _, _) = HMap.find er evts in
        if H.equal p pr then HSet.add er rfp else rfp
      ) rfp rl
    else rfp
  ) rf HSet.empty

let gen_co_cands evts (po, _, rf, _, _, _) =
  let writes = HMap.fold (fun e ((p, _, _, _) as ed) evts ->
    let pevts = try HMap.find p evts with Not_found -> HMap.empty in
    HMap.add p (HMap.add e ed pevts) evts
  ) (filter_writes evts) HMap.empty in (* should avoid this conversion *)
  let rec aux writes cco = try
    let p1, p1writes = HMap.choose writes in (* can do with map e -> evt *)
    let writes = HMap.remove p1 writes in
    let cco = HMap.fold (fun e1 ed1 cco ->
      HMap.fold (fun p2 -> HMap.fold (fun e2 ed2 cco ->
        if same_var ed1 ed2 && not (H.equal p1 p2)
	(* then [[e1;e2];[e2;e1]] :: cco else cco *)
        then begin

            let po1 = HMap.find p1 po in
            let rf21 = get_rf_from_write_to_proc evts rf p2 e2 p1 in
            let co21a = HSet.exists (fun er1 ->
              H2Set.mem (er1, e1) po1) rf21 in
            let co12a = HSet.exists (fun er1 ->
              H2Set.mem (e1, er1) po1) rf21 in

            let po2 = HMap.find p2 po in
            let rf12 = get_rf_from_write_to_proc evts rf p1 e1 p2 in
            let co12b = HSet.exists (fun er2 ->
              H2Set.mem (er2, e2) po2) rf12 in
            let co21b = HSet.exists (fun er2 ->
              H2Set.mem (e2, er2) po2) rf12 in

            if (co12a || co12b) && (co21a || co21b) then
              [[e1;e2]] :: [[e2;e1]] :: cco
              (* failwith "Weakorder.gen_co_cands : contradictory co" *)
            else if (co12a || co12b) then [[e1;e2]] :: cco
            else if (co21a || co21b) then [[e2;e1]] :: cco
            else [[e1;e2];[e2;e1]] :: cco

        end else cco
      )) writes cco
    ) p1writes cco in
    aux writes cco
    with Not_found -> cco
  in
  aux writes []



let co_to_cofrfw evts (_, _, rf, _, rmw, _) = function
  | [ew1; ew2] as co ->
     let rl = try HMap.find ew1 rf with Not_found -> [] in
     let frfw = try [[ew1; HMap.find ew2 rmw]] with Not_found -> [] in
     [co], List.fold_left (fun frfw er -> [er; ew2] :: frfw) frfw rl
  | _ -> failwith "Co_to_cofrfw : anomaly"

let add_frfw_to_co evts rels =
  List.map (co_to_cofrfw evts rels)

let add_frfw_to_co_cands evts rels =
  List.map (List.map (co_to_cofrfw evts rels))
*)


let make_pred p pl b =
  let pl = List.map (fun p -> T.make_app p []) pl in
  let tb = if b then T.t_true else T.t_false in
  F.make_lit F.Eq [ T.make_app p pl ; tb ]

let make_predl p el f =
  List.fold_left (fun f e -> make_pred p e true :: f) f el

let make_predl_dl p ell f =
  List.fold_left (fun f el -> (F.make F.Or (make_predl p el [])) :: f) f ell



let make_rel ?(op=F.Lt) r pl1 pl2 =
  let pl1 = List.map (fun p -> T.make_app p []) pl1 in
  let pl2 = List.map (fun p -> T.make_app p []) pl2 in
  F.make_lit op [ T.make_app r pl1 ; T.make_app r pl2 ]

let make_rell ?(op=F.Lt) r el f =
  List.fold_left (fun f e ->
    let pl1, pl2 = match e with
    | [p11;p21] -> [p11], [p21]
    | _ -> failwith "Weakorder.make_rel : anomaly"
    in
    (make_rel ~op r pl1 pl2) :: f
  ) f el


(*
let make_cofrl ?(op=F.Lt) r (co, frl) f =
  let f = make_rell ~op r co f in
  let f = make_rell ~op r frl f in
  f

let make_cofr ?(op=F.Lt) r cofr f =
  List.fold_left (fun f cofrl -> make_cofrl ~op r cofrl f) f cofr

let make_cofrll ?(op=F.Lt) r cofrll f =
  List.fold_left (fun f cofrl ->
    (F.make F.And (make_cofrl ~op r cofrl [])) :: f
  ) f cofrll

let make_ccofr ?(op=F.Lt) r ccofr f =
  List.fold_left (fun f cofrll ->
    (F.make F.Or (make_cofrll ~op r cofrll [])) :: f
  ) f ccofr
 *)

                 
let make_orders ?(fp=false) evts rels =
  TimeRels.start ();
  let evts = HMap.add hE0 (hP0, hW, hNone, []) evts in (* dummy event for e0 *)
  let f = [] in
  let f = if fp then begin (*
    (* let f = make_predl hFence (gen_fence evts rels) f in *)
    (* let f = make_predl hRf (gen_rf evts rels) f in *)
    (* let f = make_predl hRmw (gen_rmw evts rels) f in *)
    (* let f = make_predl hSync (gen_sync evts rels) f in *)

    let f = make_rell ~op:F.Eq hSci (gen_sync evts rels) f in
    let f = make_rell hSci (gen_po_loc evts rels) f in
    let f = make_rell hSci (gen_rf evts rels) f in
    let f = make_rell hSci (gen_co evts rels) f in
    let f = make_rell hSci (gen_fr evts rels) f in
    let f = make_rell ~op:F.Eq hSci (gen_rmw evts rels) f in
    (* let f = make_rell hSci (gen_rmw evts rels) f in rmw in po *)

    let f = make_rell ~op:F.Eq hPropi (gen_sync evts rels) f in
    let f = make_rell hPropi (gen_ppo_tso evts rels) f in
    let f = make_rell hPropi (gen_fence evts rels) f in
    let f = make_rell hPropi (gen_rfe evts rels) f in
    let f = make_rell hPropi (gen_co evts rels) f in
    let f = make_rell hPropi (gen_fr evts rels) f in
    let f = make_rell ~op:F.Eq hPropi (gen_rmw evts rels) f in
    (* let f = make_rell hPropi (gen_rmw evts rels) f in *) (* rmw in po *)
(*
    let co = gen_co evts rels in
    let cco = gen_co_cands evts rels in

    let cofrfw = add_frfw_to_co evts rels co in
    let ccofrfw = add_frfw_to_co_cands evts rels cco in

    let f = make_cofr hSci cofrfw f in
    let f = make_ccofr hSci ccofrfw f in
    let f = make_cofr hPropi cofrfw f in
    let f = make_ccofr hPropi ccofrfw f in
*) *)
    f
  end else begin (*
    (* let f = make_predl hSync (gen_sync evts rels) f in *)
    (* let f = make_predl hPoLoc (gen_po_loc evts rels) f in *)
    (* let f = make_predl hRf (gen_rf evts rels) f in *)
    (* let f = make_predl hPpo (gen_ppo_tso evts rels) f in *)
    (* let f = make_predl hFence (gen_fence evts rels) f in *)
    (* let f = make_predl hCo (gen_co evts rels) f in *)
    (* let f = make_predl_dl hCo (gen_co_cands evts rels) f in *)

    let f = make_rell ~op:F.Eq hSci (gen_sync evts rels) f in
    let f = make_rell hSci (gen_po_loc evts rels) f in
    let f = make_rell hSci (gen_rf evts rels) f in
    let f = make_rell hSci (gen_co evts rels) f in
    let f = make_rell hSci (gen_fr evts rels) f in
    let f = make_rell ~op:F.Eq hSci (gen_rmw evts rels) f in
    (* let f = make_rell hSci (gen_rmw evts rels) f in *) (* rmw in po *)

    let f = make_rell ~op:F.Eq hPropi (gen_sync evts rels) f in
    let f = make_rell hPropi (gen_ppo_tso evts rels) f in
    let f = make_rell hPropi (gen_fence evts rels) f in
    let f = make_rell hPropi (gen_rfe evts rels) f in
    let f = make_rell hPropi (gen_co evts rels) f in
    let f = make_rell hPropi (gen_fr evts rels) f in
    let f = make_rell ~op:F.Eq hPropi (gen_rmw evts rels) f in
    (* let f = make_rell hPropi (gen_rmw evts rels) f in *) (* rmw in po *)

(*  let f = make_predl hRf (gen_rf evts rels) f in
    let f = make_predl hCo (gen_co evts rels) f in
    let f = make_predl_dl hCo (gen_co_cands evts rels) f in *)
(*
    let co = gen_co evts rels in
    let cco = gen_co_cands evts rels in

    let cofrfw = add_frfw_to_co evts rels co in
    let ccofrfw = add_frfw_to_co_cands evts rels cco in

    let f = make_cofr hSci cofrfw f in
    let f = make_ccofr hSci ccofrfw f in
    let f = make_cofr hPropi cofrfw f in
    let f = make_ccofr hPropi ccofrfw f in
*) *)
    f
  end in
  TimeRels.pause ();
  if f = [] then None else
  Some (F.make F.And f)







(* ppo U fence U co U rfe U fr *)
let make_prop evts (po, f, rf, co, fr, rmw, s) =
  TimeProp.start ();
  
  let prop = H2Set.empty in

  let is_rmw ef et =
    try
      let ewl = HMap.find ef rmw in
      List.exists (fun ew -> H.equal ew et) ewl
    with Not_found -> false
  in

  (* ppo *)
  let prop = HMap.fold (fun p ppo prop ->
    H2Set.fold (fun (ef, et) prop ->
      let edf = HMap.find ef evts in
      let edt = HMap.find et evts in
      if is_write edf && is_read edt || is_rmw ef et then prop
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
    let (pf, _, _, _) = HMap.find wef evts in
    let retl = List.filter (fun ret ->
      let (pt, _, _, _) = HMap.find ret evts in
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

  (* add rmw to sync *)
  let sync = HMap.fold (fun ef etl sync ->
    let eq_ef = H2Set.fold (fun (pef, pet) eq_ef ->
      if H.equal pef ef then HSet.add pet eq_ef
      else if H.equal pet ef then HSet.add pef eq_ef
      else eq_ef
    ) sync (HSet.of_list etl) in
    List.fold_left (fun sync et ->
      let eq_et = H2Set.fold (fun (pef, pet) eq_et ->
        if H.equal pef et then HSet.add pet eq_et
        else if H.equal pet et then HSet.add pef eq_et
        else eq_et
      ) sync (HSet.singleton ef) in
      HSet.fold (fun eef sync ->
        HSet.fold (fun eet sync ->
          H2Set.add (eef, eet) sync
        ) eq_et sync
      ) eq_ef sync
    ) sync etl
  ) rmw sync in

  (* H2Set.iter (fun (e1, e2) -> *)
  (*   Format.fprintf Format.std_formatter "%a < %a  " H.print e1 H.print e2 *)
  (* ) prop; *)
  (* Format.fprintf Format.std_formatter "\n"; *)
  (* H2Set.iter (fun (e1, e2) -> *)
  (*   Format.fprintf Format.std_formatter "%a = %a  " H.print e1 H.print e2 *)
  (* ) sync; *)
  (* Format.fprintf Format.std_formatter "\n"; *)

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






let make_scloc evts (po, f, rf, co, fr, rmw, s) =
  TimeProp.start ();
  
  let scloc = H2Set.empty in

  let is_rmw ef et =
    try
      let ewl = HMap.find ef rmw in
      List.exists (fun ew -> H.equal ew et) ewl
    with Not_found -> false
  in

  (* po_loc *)
  let scloc = HMap.fold (fun p ppo scloc ->
    H2Set.fold (fun (ef, et) scloc ->
      let edf = HMap.find ef evts in
      let edt = HMap.find et evts in
      if not (same_var edf edt) || is_rmw ef et then scloc
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

  (* add rmw to sync *)
  let sync = HMap.fold (fun ef etl sync ->
    let eq_ef = H2Set.fold (fun (pef, pet) eq_ef ->
      if H.equal pef ef then HSet.add pet eq_ef
      else if H.equal pet ef then HSet.add pef eq_ef
      else eq_ef
    ) sync (HSet.of_list etl) in
    List.fold_left (fun sync et ->
      let eq_et = H2Set.fold (fun (pef, pet) eq_et ->
        if H.equal pef et then HSet.add pet eq_et
        else if H.equal pet et then HSet.add pef eq_et
        else eq_et
      ) sync (HSet.singleton ef) in
      HSet.fold (fun eef sync ->
        HSet.fold (fun eet sync ->
          H2Set.add (eef, eet) sync
        ) eq_et sync
      ) eq_ef sync
    ) sync etl
  ) rmw sync in

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

       


         
  (* SC_LOC : po_loc U co U rf U fr *)
  (* PROP :   ppo U fence U co U rfe U fr *)

    (* let f = make_rell hSci po_loc f in *)
    (* let f = make_rell hPropi ppo f in *)
    (* let f = make_rell hPropi fence f in *)
     (* let f = make_rell hCoi co f in *)
    (* let f = make_rell hSci co f in *)
    (* let f = make_rell hPropi co f in *)
    (* let f = make_rell_dl hCoi go_cands f in *)


(*let make_rel r pl1 pl2 =
  let pl1 = List.map (fun p -> T.make_app p []) pl1 in
  let pl2 = List.map (fun p -> T.make_app p []) pl2 in
  F.make_lit F.Lt [ T.make_app r pl1 ; T.make_app r pl2 ]

let make_rell r el f =
  List.fold_left (fun f e ->
    let pl1, pl2 = match e with
    | [p11;p12;p13;p21;p22;p23] -> [p11;p12(*;p13*)], [p21;p22(*;p23*)]
    | [p11;p12;p21;p22] -> [p11;p12], [p21;p22]
    | [p11;p21] -> [p11], [p21]
    | _ -> failwith "Weakorder.make_rel : anomaly"
    in
    (make_rel r pl1 pl2) :: f
  ) f el

let make_rell_dl r ell f =
  List.fold_left (fun f el -> (F.make F.Or (make_rell r el [])) :: f) f ell*)
