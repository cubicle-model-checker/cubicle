
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



(* Extract events, event ids, rf, fences and sync from sa (fences/sync removed)
   Used when making formula for safety / fixpoint check *)
let extract_events (sa, evts, eids, rf, fce, sync) at =
  let update_eids eids p hE =
    let peids = try HMap.find p eids with Not_found -> RIntMap.empty in
    let e = int_of_e hE in
    HMap.add p (RIntMap.add e hE peids) eids
  in
  match at with
  | Atom.Comp (Access (a, [pw; ew; pr; er]), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a, [pw; ew; pr; er])) when H.equal a hRf ->
     (SAtom.add at sa, evts, eids, H2Map.add (pw, ew) (pr, er) rf, fce, sync)
  | Atom.Comp (Access (a, sl), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a, sl)) when H.equal a hSync ->
     (sa, evts, eids, rf, fce, sl :: sync)
  | Atom.Comp (Access (a, [p; e]), Eq, Elem _)(*warning,several procs possible*)
  | Atom.Comp (Elem _, Eq, Access (a, [p; e])) when H.equal a hFence ->
     let pfce = try HMap.find p fce with Not_found -> HSet.empty in
     let fce = HMap.add p (HSet.add e pfce) fce in (*or use a better predicate*)
     (sa, evts, eids, rf, fce, sync)
  | Atom.Comp (Field (Access (a, [p; e]), f), Eq, Elem (c, t))
  | Atom.Comp (Elem (c,t), Eq, Field (Access (a, [p; e]),f)) when H.equal a hE->
     let pevts = try HMap.find p evts with Not_found -> HMap.empty in
     let (d, v, vi) as evt = try HMap.find e pevts
		             with Not_found -> (hNone, hNone, []) in
     let evt = if H.equal f hDir then (c, v, vi)
          else if H.equal f hVar then (d, c, vi)
          else if is_param f then (d, v, (f, c) :: vi)
          else evt in
     (SAtom.add at sa,
      HMap.add p (HMap.add e evt pevts) evts,
      update_eids eids p e, rf, fce, sync)
  | Atom.Comp (Read _, _, _) | Atom.Comp (_, _, Read _) ->
     failwith "Weakorder.extract_events : Read should not be there"
  | Atom.Comp (Write _, _, _) | Atom.Comp (_, _, Write _) ->
     failwith "Weakorder.extract_events : Write should not be there"
  | Atom.Comp (Fence _, _, _) | Atom.Comp (_, _, Fence _) ->
     failwith "Weakorder.extract_events : Fence should not be there"
  | Atom.Ite _ ->
     failwith "Weakorder.extract_events : Ite should not be there"
  | _ -> (SAtom.add at sa, evts, eids, rf, fce, sync)



let make_sync sync =
  let rec aux sm = function
    | [] -> sm
    | [_] -> failwith "Weakorder.make_sync : internal error"
    | p :: e :: sl -> aux (H2Set.add (p, e) sm) sl
  in
  List.map (aux H2Set.empty) sync

let are_sync sync p1 e1 p2 e2 =
  List.exists (fun ss ->
    H2Set.mem (p1, e1) ss && H2Set.mem (p2, e2) ss
  ) sync

let make_po eids sync = (* sync used *)
  HMap.fold (fun p peids po ->
    let peids = ref peids in
    let ppo = ref H2Set.empty in
    while not (RIntMap.is_empty !peids) do
      let ef, hEf = RIntMap.min_binding !peids in
      peids := RIntMap.remove ef !peids;
      ppo := RIntMap.fold (fun et hEt ppo ->
        if are_sync sync p hEf p hEt then ppo
        else H2Set.add (hEf, hEt) ppo
      ) !peids !ppo
    done;
    HMap.add p !ppo po
  ) eids HMap.empty

let make_fence eids fce evts = (* no need to use sync *)
  HMap.fold (fun p peids fence ->
    let pevts = HMap.find p evts in
    let pfce = try HMap.find p fce with Not_found -> HSet.empty in
    let peids = ref peids in
    let pfence = ref H2Set.empty in
    while not (RIntMap.is_empty !peids) do
      let ef, hEf = RIntMap.min_binding !peids in
      peids := RIntMap.remove ef !peids;
      let (df, _, _) = HMap.find hEf pevts in
      if H.equal df hW then
        let f = ref false in
        pfence := RIntMap.fold (fun et hEt pfence ->
          if HSet.mem hEt pfce then f := true;
          if !f = false then pfence else
          let (dt, _, _) = HMap.find hEt pevts in
          if H.equal dt hR then H2Set.add (hEf, hEt) pfence else pfence
        ) !peids !pfence;
    done;
    HMap.add p !pfence fence
  ) eids HMap.empty



let init_acc =
  (SAtom.empty, HMap.empty, HMap.empty, H2Map.empty, HMap.empty, [])

let post_process (sa, evts, eids, rf, fce, sync) =
  let evts = HMap.map (HMap.map sort_params) evts in
  let sync = make_sync sync in
  sa, evts, (make_po eids sync, rf, make_fence eids fce evts, sync)

(* Used when making formula for safety / fixpoint check *)
let extract_events_array ar =
  post_process (Array.fold_left (fun acc a -> extract_events acc a) init_acc ar)

(* Used when making formula for safety / fixpoint check *)
let extract_events_set sa =
  post_process (SAtom.fold (fun a acc -> extract_events acc a) sa init_acc)



let filter_writes evts =
  HMap.fold (fun p pevts writes ->
    let pw = HMap.filter (fun e ed -> is_write ed) pevts in
    HMap.add p pw writes) evts HMap.empty

let gen_po_pred pred evts po fence =
  HMap.fold (fun p ppo pol ->
    let pevts = HMap.find p evts in
    H2Set.fold (fun (ef, et) pol ->
      if pred (HMap.find ef pevts) (HMap.find et pevts)
      then [p; ef; p; et] :: pol else pol
    ) ppo pol
  ) po []

let gen_po_loc = gen_po_pred (fun ed1 ed2 -> same_var ed1 ed2)

let gen_ppo_tso = gen_po_pred (fun ed1 ed2 -> not (is_write ed1 && is_read ed2))

let gen_fence evts fence =
  HMap.fold (fun p pfence fl ->
    H2Set.fold (fun (ef, et) fl -> [p; ef; p; et] :: fl) pfence fl
  ) fence []

let gen_sync evts sync = (* union find on map instead of array *)
  List.fold_left (fun sl sync ->
    let sl = ref sl in
    let sync = ref sync in
    while not (H2Set.is_empty !sync) do
      let p1, e1 = H2Set.choose !sync in
      sync := H2Set.remove (p1, e1) !sync;
      try
        let p2, e2 = H2Set.choose !sync in
        sync := H2Set.remove (p1, e1) !sync;
        sl := [p1; e1; p2; e2] :: !sl
      with Not_found -> ()
    done;
    !sl
  ) [] sync

let gen_co evts po =
  let writes = filter_writes evts in
  (* Initial writes *)
  let co = HMap.fold (fun pt -> HMap.fold (fun et edt co ->
    [hP0; hE0; pt; et] :: co)) writes [] in
  (* Writes from the same thread *)
  HMap.fold (fun p ppo co ->
    let pwrites = HMap.find p writes in
    H2Set.fold (fun (ef, et) co ->
      try
        if same_var (HMap.find ef pwrites) (HMap.find et pwrites)
        then [p; ef; p; et] :: co else co
      with Not_found -> co
    ) ppo co
  ) po co

(* more refinements to do :
   if p1:RX reads from p2:WX, then
    - all p1:WX that are po-before p1:RX are co-before P2:WX
    - all p1:WX that are po-after p1:RX are co-after P2:WX

gen_co_cands could do both co and co_cands
evaluate condition inside loop
must extract rf
*)

let get_rf_from_write_to_proc rf pwr ewr p =
  H2Map.fold (fun (pw, ew) (pr, er) rfp ->
    if H.equal pwr pw && H.equal ewr ew && H.equal p pr then
      H2Set.add (pr, er) rfp else rfp
  ) rf H2Set.empty

let gen_co_cands evts po rf =
  let rec aux writes cco = try
    let p1, p1writes = HMap.choose writes in
    let writes = HMap.remove p1 writes in
    let cco = HMap.fold (fun e1 ed1 cco ->
      HMap.fold (fun p2 -> HMap.fold (fun e2 ed2 cco ->
        if same_var ed1 ed2 && not (H.equal p1 p2)
	(* then [[p1;e1;p2;e2];[p2;e2;p1;e1]] :: cco else cco *)
        then begin

            let po1 = HMap.find p1 po in
            let rf21 = get_rf_from_write_to_proc rf p2 e2 p1 in
            let co21a = H2Set.exists (fun (_, er1) ->
              H2Set.mem (er1, e1) po1) rf21 in
            let co12a = H2Set.exists (fun (_, er1) ->
              H2Set.mem (e1, er1) po1) rf21 in

            let po2 = HMap.find p2 po in
            let rf12 = get_rf_from_write_to_proc rf p1 e1 p2 in
            let co12b = H2Set.exists (fun (_, er2) ->
              H2Set.mem (er2, e2) po2) rf12 in
            let co21b = H2Set.exists (fun (_, er2) ->
              H2Set.mem (e2, er2) po2) rf12 in

            if (co12a || co12b) && (co21a || co21b) then
              [[p1;e1;p2;e2]] :: [[p2;e2;p1;e1]] :: cco
              (* failwith "Weakorder.gen_co_cands : contradictory co" *)
            else if (co12a || co12b) then [[p1;e1;p2;e2]] :: cco
            else if (co21a || co21b) then [[p2;e2;p1;e1]] :: cco
            else [[p1;e1;p2;e2];[p2;e2;p1;e1]] :: cco

        end else cco
      )) writes cco
    ) p1writes cco in
    aux writes cco
    with Not_found -> cco
  in
  aux (filter_writes evts) []



let make_pred p pl b =
  let pl = List.map (fun p -> T.make_app p []) pl in
  let tb = if b then T.t_true else T.t_false in
  F.make_lit F.Eq [ T.make_app p pl ; tb ]

let make_predl p el f =
  List.fold_left (fun f e -> make_pred p e true :: f) f el

let make_predl_dl p ell f =
  List.fold_left (fun f el -> (F.make F.Or (make_predl p el [])) :: f) f ell

let make_orders ?(fp=false) evts (po, rf, fence, sync) =
  TimeRels.start ();
  let f = [] in
  let f = make_predl hFence (gen_fence evts fence) f in
  let f = make_predl hSync (gen_sync evts sync) f in
  let f = if fp then f else begin
    let f = make_predl hPoLoc (gen_po_loc evts po fence) f in
    let f = make_predl hPpo (gen_ppo_tso evts po fence) f in
    let f = make_predl hCo (gen_co evts po) f in
    let f = make_predl_dl hCo (gen_co_cands evts po rf) f in
    f
  end in
  TimeRels.pause ();
  if f = [] then None else
  Some (F.make F.And f)





         
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
