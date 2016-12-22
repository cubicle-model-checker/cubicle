
open Weakmem
open Types

(* Retrive all events in a map of map of map (procs -> events -> subevents *)
let get_evts ar =
  let evts = Array.fold_left (fun evts a ->
    Weakwrite.split_event a evts) H3Map.empty ar in
  H3Map.fold (fun (p, e, s) (d, v, vi, vals) evts ->
    let pevts = try HMap.find p evts with Not_found -> HMap.empty in
    let sevts = try HMap.find e pevts with Not_found -> HMap.empty in
    let vi = List.map (fun (_, i) -> i) (Weakutil.sort_hplist vi) in
    let evt = (d, v, vi, vals) in
    HMap.add p (HMap.add e (HMap.add s evt sevts) pevts) evts
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

(* Checks whether (d1, v1, vi1, vals) can subsume (d2, v2, vi2, vals2) *)
let compat_evts (d1, v1, vi1, vals1) (d2, v2, vi2, vals2) =
  H.equal d1 d2 && same_var (d1, v1, vi1) (d2, v2, vi2) &&
    (vals1 = [] && vals2 = [] ||
     vals1 <> [] && vals2 <> [] &&
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

let cartesian_product_h3m =
  cartesian_product (H3Map.union (fun k v1 v2 ->
    failwith "Weaksubst.cartesian_product : duplicate"))

(* [Empty] -> the source was empty, this is a valid substitution
                (though it should not happen here)
   [] -> no combination (not enough compatible events in dest) *)
let rec make_s_combs p ef et ssf sst = (* order between s' doesn't matter *)
  let rec aux cc rcl ssf sst =
    try
      let sf, evtf = HMap.choose ssf in
      let ssf = HMap.remove sf ssf in
      HMap.fold (fun st evtt rcl ->
        let sst = HMap.remove st sst in
	if compat_evts evtf evtt then
	  let cc = H3Map.add (p, ef, sf) (et, st) cc in
	  aux cc rcl ssf sst
	else rcl
      ) sst rcl (* To Set is finished -> combinations done for this sf *)
    with Not_found -> cc :: rcl (* From Set is empty -> the combination is OK *)
  in
  aux H3Map.empty [] ssf sst

(* [Empty] -> the source was empty, this is a valid substitution
                (though it should not happen here)
   [] -> no combination (not enough compatible events in dest) *)
let rec make_e_combs p esf est = (* order between e matters *)
  let rec aux ccl rcl esf est =
    try
      let ef, ssf = HMap.min_binding esf in
      let esf = HMap.remove ef esf in
      let rcl, _ = HMap.fold (fun et sst (rcl, est) ->
	let est = HMap.remove et est in
	let ncl = make_s_combs p ef et ssf sst in
	if ncl = [] then rcl, est
	else
          let ccl = cartesian_product_h3m ncl ccl in
          aux ccl rcl esf est, est
      ) est (rcl, est) (* To Set is finished -> combinations done for this ef *)
      in rcl
    with Not_found -> ccl @ rcl (*From Set is empty -> the combinations are OK*)
  in
  aux [H3Map.empty] [] esf est

(* Alternative to the next make_p_combs *)
(*exception Exit
let rec make_e_combs p esf est = (* order between e matters *)
  let rec aux ccl rcl esf est =
    try
      let ef, ssf = HMap.min_binding esf in
      let esf = HMap.remove ef esf in
      let rcl, _ = HMap.fold (fun et sst (rcl, est) ->
	let est = HMap.remove et est in
	let ncl = make_s_combs p ef et ssf sst in
	if ncl = [] then raise Exit
	else aux (cartesian_product_h3m ncl ccl) rcl esf est, est
      ) est (rcl, est) (* To Set is finished -> combinations done for this ef *)
      in rcl
    with Not_found -> ccl @ rcl (* From Set is empty -> the combinations are good *)
  in
  try
    let ef, ssf = HMap.min_binding esf in
    let esf = HMap.remove ef esf in
    let rcl, _ = HMap.fold (fun et sst (rcl, est) ->
      let est = HMap.remove et est in
      let ccl = make_s_combs p ef et ssf sst in
      if ccl = [] then rcl, est (* should exit if not enough et in est *)
      else try aux ccl rcl esf est, est with Exit -> rcl, est
    ) est ([], est) (* To Set is finished -> combinations done *)
    in
    rcl
  with Not_found -> [H3Map.empty]*)

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
          let ccl = cartesian_product_h3m ncl ccl in
          aux ccl psf pst (* Next process *)
      with Not_found -> []
    with Not_found -> ccl (* From Set is empty -> we're done *)
  in
  aux [H3Map.empty] psf pst

let build_event_substs from_evts to_evts = make_p_combs from_evts to_evts



let remap_events_ar ar sub =
  let subst p e s =
    try H3Map.find (p, e, s) sub with Not_found ->
      failwith "Weaksubst.remap_events : no substitution !"
  in
  let rec remap_t = function
    | Arith (t, c) -> Arith (remap_t t, c)
    | Field (t, f) -> Field (remap_t t, f)
    | Access (a, [p;e;s]) when H.equal a hE ->
        let e, s = subst p e s in Access (a, [p;e;s])
    | Access (a, [p;e]) when H.equal a hFence ->
        let e, _ = subst p e hS1 in Access (a, [p;e])
    | Access (a, [p1;e1;s1;p2;e2;s2]) when H.equal a hRf ->
        let e1, s1 = subst p1 e1 s1 in
        let e2, s2 = subst p2 e2 s2 in
        Access (a, [p1;e1;s1;p2;e2;s2])
    | t -> t
  in
  let rec remap_a = function
    | Atom.Comp (t1, op, t2) -> Atom.Comp (remap_t t1, op, remap_t t2)
    | Atom.Ite (sa, a1, a2) -> Atom.Ite (sa, remap_a a1, remap_a a2)
    | a -> a
  in
  let ar = Array.map remap_a ar in
  Array.fast_sort Atom.compare ar;
  ar

let remap_events ar substs =
  List.fold_left (fun nodes s ->
    if H3Map.is_empty s then nodes
    else (remap_events_ar ar s) :: nodes
  ) [] substs







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


