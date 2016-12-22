
open Weakmem
open Types

module STerm = Term.Set

module WH = Hashtbl.Make(struct
  type t = (H.t * Variable.t list)
  let equal (v1, vi1) (v2, vi2) =
    H.equal v1 v2 && H.list_equal vi1 vi2
  let hash = Hashtbl.hash
end)



(* Build an event *)
let build_event p e s d v vi = (* v is already in the _Vx form *)
  let tevt = Access (hE, [p;e;s]) in
  let adir = Atom.Comp (Field (tevt, hDir), Eq, Elem (d, Constr)) in
  let avar = Atom.Comp (Field (tevt, hVar), Eq, Elem (v, Constr)) in
  let sa, _ = List.fold_left (fun (sa, i) v ->
    SAtom.add (Atom.Comp (Field (tevt, mk_hP i), Eq, Elem (v, Var))) sa, i + 1
  ) (SAtom.add avar (SAtom.singleton adir), 1) vi in
  sa, tevt



(* Build a write event for the specified initial write *)
let make_init_write =
  let events = WH.create 16 in
  let nbe = ref 0 in
  fun (v, vi) ->
    try WH.find events (v, vi) with Not_found ->
      let hSi = nbe := !nbe + 1; mk_hS !nbe in      
      let sa, _ = build_event hP0 hE1 hSi hW v vi in
      let vv = H.make (var_of_v v) in
      let vt = if vi = [] then Elem (vv, Glob) else Access (vv, vi) in
      WH.add events (v, vi) ((hP0, hE1, hSi), vt, sa);
      ((hP0, hE1, hSi), vt, sa)



(* Make an event for specified parameters, returns the new atoms and event counts *)
let make_event (cnt, na) d p v vi = 
  let (_, ret) = Smt.Symbol.type_of v in
  let eid, seid = try HMap.find p cnt with Not_found -> (1, 1) in
  let e, s, v = mk_hE eid, mk_hS seid, mk_hV v in
  let sa, tevt = build_event p e s d v vi in
  let cnt = HMap.add p (eid, seid + 1) cnt in
  (cnt, SAtom.union na sa), Field (Field (tevt, hVal), mk_hT ret)



(* Actually splits an sa into pure sa and events/writes/fences
   and determines the next event id to attribute
   Is meant to be called on an atom set that has events, reads, processed writes, fences
   Used internally by events_of_satom only *)
let split_events_orders sa =
  let rec has_read = function
    | Arith (t, _) -> has_read t
    | Read _ -> true
    | Write _ -> assert false (* writes are processed before *)
    | _ -> false
  in  
  let rec update_cnt_t cnt = function
    | Arith (t, _) -> update_cnt_t cnt t
    | Field (Access (a, [p;e;_]), _) when H.equal a hE ->
       let (c, _) = try HMap.find p cnt with Not_found -> (1, 1) in
       let e = int_of_e e in
       if e >= c then HMap.add p (e+1, 1) cnt else cnt
    | _ -> cnt
  in
  let rec update_cnt cnt = function
    | Atom.Comp (t1, _, t2) -> update_cnt_t (update_cnt_t cnt t1) t2
    | Atom.Ite (sa, a1, a2) -> update_cnt (update_cnt cnt a1) a2 (* are Ites allowed here ? *)
    | _ -> cnt
  in
  SAtom.fold (fun a (sa_pure, sa_evts, sa_wts, fce, cnt) -> match a with
    | Atom.Comp (Fence p, _, _) | Atom.Comp (_, _, Fence p) ->
       (sa_pure, sa_evts, sa_wts, p :: fce, cnt)
    | Atom.Comp (Write _, _, _) | Atom.Comp (_, _, Write _) ->
       (sa_pure, sa_evts, SAtom.add a sa_wts, fce, cnt)
        (* other side of equality is meaningless : it has already been processed *)
    | Atom.Comp (t1, _, t2) when has_read t1 || has_read t2 ->
       (sa_pure, SAtom.add a sa_evts, sa_wts, fce, update_cnt cnt a)
    | _ -> (SAtom.add a sa_pure, sa_evts, sa_wts, fce, update_cnt cnt a)
) sa (SAtom.empty, SAtom.empty, SAtom.empty, [], HMap.empty)



(* Used internally by events_of_satom only *)
let all_reads sa =
  let rec reads_of srt td = match td with
    | Arith (td, _) -> reads_of srt td
    | Read _ -> STerm.add td srt
    | Write _ -> assert false (* sa was filtered before, can only contain reads*)
    | _ -> srt
  in
  SAtom.fold (fun a srt -> match a with
    | Atom.Comp (t1, _, t2) -> reads_of (reads_of srt t1) t2
    (* Ites ? *)
    | _ -> srt
  ) sa STerm.empty

(* Used internally by events_of_satom only *)
let event_subst t te sa =
  let rec subst td =
    if Term.compare td t = 0 then te else match td with
    | Arith (td, c) -> Arith (subst td, c)
    | _ -> td
  in
  SAtom.fold (fun a sa -> match a with
    | Atom.Comp (t1, op, t2) ->
       SAtom.add (Atom.Comp (subst t1, op, subst t2)) sa
    | _ -> SAtom.add a sa
  ) sa SAtom.empty

(* Used internally by events_of_satom only *)
let update_cnt cnt =
  HMap.fold (fun p (eid, seid) cnt ->
    if seid <= 1 then HMap.add p (eid, seid) cnt
    else HMap.add p (eid + 1, 1) cnt
  ) cnt HMap.empty



(* Replace plain read/writes by actual events + add rf pairs
   Used by pre-image, and when generating events for unsafe / invariants *)
let events_of_satom sa =

  let eTrue = Elem (Term.htrue, Constr) in

  let sa_pure, sa_evts, sa_wts, fce, cnt = split_events_orders sa in
  let srt = all_reads sa_evts in
  
  (* First, generate Write events *)
  let (cnt, sa_new) = SAtom.fold (fun a acc -> match a with
    | Atom.Comp (Write (p, v, vi, srl), _, _)
    | Atom.Comp (_, _, Write (p, v, vi, srl)) ->
       let (cnt, sa), te = make_event acc hW p v vi in
       let (wp, we, ws) = match te with
         | Field (Field (Access (_, [p; e; s]), _), _) -> (p, e, s)
	 | _ -> assert false in
       let sa = List.fold_left (fun sa (rp, re, rs) ->
	 let rfa = Atom.Comp (Access (hRf, [wp;we;ws;rp;re;rs]), Eq, eTrue) in
	 SAtom.add rfa sa
       ) sa srl in
       (cnt, sa)
    | _ -> assert false (* sa_wts was filtered before, it can only contain writes *)
  ) sa_wts (cnt, SAtom.empty) in

  (* Update event count *)
  let cnt = update_cnt cnt in

  (* Then, generate Read events *)
  let ((cnt, sa_new), sa_evts) = STerm.fold (fun t (acc, sa) -> match t with
    | Read (p, v, vi) ->
       let acc, te = make_event acc hR p v vi in
       let sa = event_subst t te sa in
       (acc, sa)
    | _ -> assert false (* srt was filtered before, it can only contain reads *)
  ) srt ((cnt, sa_new), sa_evts) in

  (* Update event count *)
  let cnt = update_cnt cnt in

  (* Generate proper event order *)
  let sa_fence = List.fold_left (fun sa p ->
    let (eid, _) = try HMap.find p cnt with Not_found -> (1, 1) in
    if eid <= 1 then sa else (* no fence if no event after *)
      let e = mk_hE (eid - 1) in
      let fa = Atom.Comp (Access (hFence, [p; e]), Eq, eTrue) in
      SAtom.add fa sa
  ) SAtom.empty fce in

  (* Merge all atom sets *)
  SAtom.union sa_pure (SAtom.union sa_fence (SAtom.union sa_evts sa_new))
