
open Weakmem
open Types
open Util

(*
module RInt = struct
  type t = int
  let compare x y = - (Pervasives.compare x y)
end

module RIntMap = Map.Make (RInt)

module UF = struct
  type t = H2.t H2Map.t

  let empty = H2Map.empty

  let rec find m i =
    try find m (H2Map.find i m) with Not_found -> i
                                              
  let union m i j =
    let ri = find m i in
    let rj = find m j in
    if (H2.compare ri rj) <> 0 then H2Map.add ri rj m else m
end
                        
let rec split_event_t = function
  | Field (Field (Access (a, [p; e]), f), _)
       when H.equal a hE && H.equal f hVal ->
     Some (p, int_of_e e), None
  | Arith (t, c) ->
     fst (split_event_t t), Some c
  | _ -> None, None

let subs_const_from_term cs =
  let cs = Types.mult_const (-1) cs in
  function
  | Const c -> Const (Types.add_constants c cs)
  | Arith (t, c) -> Arith (t, Types.add_constants c cs)
  | t -> Arith (t, cs)

let find_event_safe (p, e) evts =
  let pevts = try HMap.find p evts with Not_found -> RIntMap.empty in
  try RIntMap.find e pevts with Not_found -> (hNone, (hNone, hNone, []), [])

let add_event (p, e) evt evts =
  let pevts = try HMap.find p evts with Not_found -> RIntMap.empty in
  RIntMap.add e evt pevts

let process_event eid c rev op tv evts = match eid with
  | Some eid ->
     let (e, ed, vals) = find_event_safe eid evts in
     let tv = match c with Some c -> subs_const_from_term c tv | _ -> tv in
     add_event eid (e, ed, (rev, op, tv) :: vals) evts
  | None -> evts

let extract_po_sync (evts, sync) at =
  let rec make_sync sm = function
    | [] | [_;_] -> sm
    | [_] | [_;_;_] -> assert false
    | p1 :: e1 :: ((p2 :: e2 :: _) as sl) ->
       make_sync (UF.union sm (p1, e1) (p2, e2)) sl
  in
  match at with
  | Atom.Comp (Access (a, sl), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a, sl)) when H.equal a hSync ->
     (evts, make_sync sync sl)
  | Atom.Comp (Field (Access (a, [p; e]), f), Eq, Elem (c, t))
  | Atom.Comp (Elem (c,t), Eq, Field (Access (a, [p;e]),f)) when H.equal a hE ->
     let ie = int_of_e e in
     let pevts = try HMap.find p evts with Not_found -> RIntMap.empty in
     let (_, ((d, v, vi) as ed), vals) =
       try RIntMap.find ie pevts
       with Not_found -> (hNone, (hNone, hNone, []), []) in
     let ed = if H.equal f hDir then (c, v, vi)
         else if H.equal f hVar then (d, c, vi)
         else if is_param f then (d, v, (f, c) :: vi)
         else ed in
     (HMap.add p (RIntMap.add ie (e, ed, vals) pevts) evts, sync)
  | Atom.Comp (t1, op, t2) ->
     let eid1, c1 = split_event_t t1 in
     let eid2, c2 = split_event_t t2 in
     let evts = process_event eid1 c1 false op t2 evts in
     process_event eid2 c2 true op t1 evts
  | _ -> (evts, sync)
 *)

(* Retrive all events in a map of map (procs -> events *)
let get_evts ar =
  let evts = Array.fold_left (fun evts a ->
    Weakwrite.split_event a evts) H2Map.empty ar in
  H2Map.fold (fun (p, e) (ed, vals) evts ->
    let pevts = try HMap.find p evts with Not_found -> HMap.empty in
    let evt = (sort_params ed, vals) in
    HMap.add p (HMap.add e evt pevts) evts
  ) evts HMap.empty

(* Checks whether (r1, op1, t1) can subsume (r2, op2, t2) *)
let compatible_values r1 op1 t1 r2 op2 t2 = match t1, t2 with
  | Const c1, Const c2 ->
     begin match r1, op1 with
     | false, Eq | true, Neq -> (* = *)
        begin match r2, op2 with
	| false, Eq | true, Neq -> Types.compare_constants c1 c2 = 0
	| _ -> false
	end
     | false, Neq | true, Eq -> (* <> *)
        begin match r2, op2 with
	| false, Eq | true, Neq -> Types.compare_constants c1 c2 <> 0
	| false, Neq | true, Eq -> Types.compare_constants c1 c2 = 0
	| false, Lt -> Types.compare_constants c1 c2 >= 0
	| false, Le -> Types.compare_constants c1 c2 > 0
	| true, Le -> Types.compare_constants c1 c2 <= 0
	| true, Lt -> Types.compare_constants c1 c2 < 0
	end
     | false, Lt -> (* < *)
        begin match r2, op2 with
	| false, Eq | true, Neq -> Types.compare_constants c1 c2 > 0
	| false, Lt -> Types.compare_constants c1 c2 >= 0
	| false, Le -> Types.compare_constants c1 c2 > 0
	| _ -> false
	end
     | false, Le -> (* <= *)
        begin match r2, op2 with
	| false, Eq | true, Neq -> Types.compare_constants c1 c2 >= 0
	| false, Lt -> Types.compare_constants c1 c2 >= 0 (* +1 *)
	| false, Le -> Types.compare_constants c1 c2 >= 0
	| _ -> false
	end
     | true, Le -> (* > *)
        begin match r2, op2 with
	| false, Eq | true, Neq -> Types.compare_constants c1 c2 < 0
	| true, Le -> Types.compare_constants c1 c2 <= 0
	| true, Lt -> Types.compare_constants c1 c2 < 0
	| _ -> false
	end
     | true, Lt -> (* >= *)
        begin match r2, op2 with
	| false, Eq | true, Neq -> Types.compare_constants c1 c2 <= 0
	| true, Le -> Types.compare_constants c1 c2 <= 0 (* +1 *)
	| true, Lt -> Types.compare_constants c1 c2 <= 0
	| _ -> false
	end
     end
  | _ -> true

(* Checks whether (ed1, vals) can subsume (ed2, vals2) *)
let compat_evts (ed1, vals1) (ed2, vals2) =
  same_dir ed1 ed2 && same_var ed1 ed2 &&
    (vals1 = [] (*&& vals2 = []*) ||
     vals1 <> [] && vals2 <> [] &&
    (* (vals1 = [] || vals2 = [] || *)
     List.for_all (fun (r1, op1, t1) ->
       List.for_all (fun (r2, op2, t2) ->
         compatible_values r1 op1 t1 r2 op2 t2
       ) vals2
     ) vals1)

let cartesian_product op l1 l2 =
  if l1 = [] then l2 else if l2 = [] then l1 else
  List.fold_left (fun rl e1 ->
    List.fold_left (fun rl e2 ->
      (op e1 e2) :: rl
    ) rl l2
  ) [] l1

let cartesian_product_h2m =
  cartesian_product (H2Map.union (fun k v1 v2 ->
    failwith "Weaksubst.cartesian_product : duplicate"))

(* SHOULD TAKE CARE OF SYNC ! *)
(* [Empty] -> the source was empty, this is a valid substitution
                (though it should not happen here)
   [] -> no combination (not enough compatible events in dest) *)
let rec make_e_combs p esf est = (* order between e matters *)
  let rec aux cc rcl esf est =
    try
      let ef, evtf = HMap.min_binding esf in
      let esf = HMap.remove ef esf in
      let rcl, _ = HMap.fold (fun et evtt (rcl, est) ->
	let est = HMap.remove et est in
        if compat_evts evtf evtt then
	  let cc = H2Map.add (p, ef) et cc in
	  aux cc rcl esf est, est
	else rcl, est
      ) est (rcl, est) (* To Set is finished -> combinations done for this ef *)
      in rcl
    with Not_found -> cc :: rcl (*From Set is empty -> the combinations are OK*)
  in
  aux H2Map.empty [] esf est

(* [Empty] -> the source was empty, this is a valid substitution
   [] -> no combination (not enough compatible events in dest)  *)
let rec make_p_combs psf pst = (* only map events from same procs *)
  let rec aux ccl psf pst =
    try
      let p, esf = HMap.choose psf in
      let psf = HMap.remove p psf in
      try
        let est = HMap.find p pst in
        let pst = HMap.remove p pst in
	let ncl = make_e_combs p esf est in (* might be [] or [Empty] *)
	if ncl = [] then []
	else
          let ccl = cartesian_product_h2m ncl ccl in
          aux ccl psf pst (* Next process *)
      with Not_found -> []
    with Not_found -> ccl (* From Set is empty -> we're done *)
  in
  aux [H2Map.empty] psf pst

(* from : visited node, more general / to : node to test, less general *)
let build_event_substs from_evts to_evts =
  TimeCSubst.start ();
  let es = make_p_combs from_evts to_evts in
  TimeCSubst.pause ();
  es


let remap_events_ar ar sub =
  let subst p e =
    try H2Map.find (p, e) sub with Not_found ->
      failwith "Weaksubst.remap_events : no substitution !"
  in
  let remap_sl sl =
    let rec aux rsl = function
      | [] -> rsl
      | [_] -> failwith "Weaksubst.remap_events : internal error"
      | p :: e :: sl -> aux ((subst p e) :: p :: rsl) sl
    in
    List.rev (aux [] sl)
  in
  let rec remap_t = function
    | Arith (t, c) -> Arith (remap_t t, c)
    | Field (t, f) -> Field (remap_t t, f)
    | Access (a, [p; e]) when H.equal a hE || H.equal a hFence ->
        let e = subst p e in Access (a, [p; e])
    | Access (a, [p1; e1; p2; e2]) when H.equal a hRf ->
        let e1 = subst p1 e1 in
        let e2 = subst p2 e2 in
        Access (a, [p1; e1; p2; e2])
    | Access (a, sl) when H.equal a hSync ->
       Access (a, remap_sl sl)
    (* Read / Write / Fence -> KO *)
    | t -> t
  in
  let rec remap_a = function
    | Atom.Comp (t1, op, t2) -> Atom.Comp (remap_t t1, op, remap_t t2)
    | Atom.Ite (sa, a1, a2) -> Atom.Ite (sa, remap_a a1, remap_a a2) (* KO ? *)
    | a -> a
  in
  let ar = Array.map remap_a ar in
  Array.fast_sort Atom.compare ar;
  ar

let remap_events ar substs =
  TimeASubst.start ();
  let nl = List.fold_left (fun nodes s ->
    if H2Map.is_empty s then ar :: nodes
    else (remap_events_ar ar s) :: nodes
  ) [] substs in
  TimeASubst.pause ();
  nl






(*= v1  = !<> v2      v1 = v2
  = v1  <> != v2      false
  = v1      < v2      false
  = v1     <= v2      false
  = v1    !<= v2      false
  = v1     !< v2      false

 <> v1  = !<> v2      v1 <> v2         eg : x <> 4 / x = 4 // x <> 4 / x = 5 
 <> v1  <> != v2      v1 = v2
 <> v1      < v2      v1 >= v2         eg : x <> 4 / x = 3 // x <> 4 / x = 4
 <> v1     <= v2      v1 > v2
 <> v1    !<= v2      v1 <= v2
 <> v1     !< v2      v1 < v2          eg : x <> 4 / x = 4 // x <> 4 / x = 5

  < v1  = !<> v2      v1 > v2          eg : x < 4 / x = 3 // x < 4 / x = 4 
  < v1  <> != v2      false
  < v1      < v2      v1 >= v2         eg : x < 4 / x <= 3 // x < 4 / x <= 4
  < v1     <= v2      v1 > v2
  < v1    !<= v2      false
  < v1     !< v2      false

 <= v1  = !<> v2      v1 >= v2         eg : x < 4 / x = 4 // x < 4 / x = 5 
 <= v1  <> != v2      false
 <= v1      < v2      v1+1 >= v2       eg : x <= 4 / x < 5 // x <= 4 / x < 6
 <= v1     <= v2      v1 >= v2
 <= v1    !<= v2      false
 <= v1     !< v2      false

  > v1  = !<> v2      v1 < v2          eg : x > 4 / x = 4 // x > 4 / x = 5 
  > v1  <> != v2      false
  > v1      < v2      false
  > v1     <= v2      false
  > v1    !<= v2      v1 <= v2
  > v1     !< v2      v1 < v2          eg : x > 4 / x >= 4 // x > 4 / x >= 5

 >= v1  = !<> v2      v1 <= v2         eg : x >= 4 / x = 3 // x >= 4 / x = 4 
 >= v1  <> != v2      false
 >= v1      < v2      false
 >= v1     <= v2      false
 >= v1    !<= v2      v1 <= v2+1
 >= v1     !< v2      v1 <= v2         eg : x >= 4 / x >= 3 // x <= 4 / x >= 4

x >= 4    x > 2   x > 3   x > 4   x > 5   x > 6    *)


