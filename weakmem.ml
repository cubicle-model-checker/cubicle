
open Types

module H = Hstring
module HMap = Hstring.HMap
module HSet = Hstring.HSet
module T = Smt.Term
module S = Smt.Symbol
module F = Smt.Formula
module STerm = Term.Set

module HS3 = struct
  type t = (H.t * H.t * H.t)
  let compare (s1a, s1b, s1c) (s2a, s2b, s2c) =
    let c = H.compare s1a s2a in if c <> 0 then c else
    let c = H.compare s1b s2b in if c <> 0 then c else
    H.compare s1c s2c
end

module H3Map = Map.Make(HS3)



let hNone = H.make ""
let hP0 = H.make "#0"
let hR = H.make "_R"
let hW = H.make "_W"
let hDirection = H.make "_direction"
let hWeakVar = H.make "_weak_var"
let hV = H.make "_v"
let hParam = H.make "_param"
let hVarParam = H.make "_varparam"
let hValType = H.make "_val_type"
let hDir = H.make "_dir"
let hVar = H.make "_var"
let hPar = H.make "_par"
let hVal = H.make "_val"
let hEvent = H.make "_event"
let hInt = H.make "int"
let hProp = H.make "prop"
let hO = H.make "_o"
let hF = H.make "_f"
let hE = H.make "_e"
let hE1 = H.make "_e1"
let hS1 = H.make "_s1"
let hPo = H.make "_po"
let hRf = H.make "_rf"
let hCo = H.make "_co"
let hFence = H.make "_fence"
let hCoUProp = H.make "_co_U_prop"
let hPoLocUCom = H.make "_po_loc_U_com"
let hPoLoc = H.make "_po_loc"
let hPpo = H.make "_ppo"
let hSci = H.make "_sci"
let hPropi = H.make "_propi"
let mk_hE e = H.make ("_e" ^ (string_of_int e))
let mk_hS s = H.make ("_s" ^ (string_of_int s))
let mk_hV hv = H.make ("_V" ^ (H.view hv))
let mk_hP p = H.make ("_p" ^ (string_of_int p))
let mk_hT ht = H.make ("_t" ^ (H.view ht))
let eTrue = Elem (Term.htrue, Constr)



let max_params = ref 0
let pl = ref []



let int_of_e e =
  let e = H.view e in
  let e = String.sub e 2 (String.length e - 2) in
  int_of_string e

let var_of_v v =
  let v = H.view v in
  let v = String.sub v 2 (String.length v - 2) in
  v



let init_weak_env wvl =

  Smt.Type.declare hDirection [hR; hW];
  Smt.Type.declare hWeakVar (List.map (fun (v, _, _) -> mk_hV v) wvl);

  (* wts : set of all types of weak variables / maxp : max. number of params *)
  let wts, maxp = List.fold_left (fun (wts, maxp) (wv, args, ret) ->
    let nbp = List.length args in
    HSet.add ret wts, if nbp > maxp then nbp else maxp
  ) (HSet.empty, 0) wvl in

  (* wtl : list of all types of weak variable + corresponding field name *)
  let wtl = HSet.fold (fun wt wtl -> (mk_hT wt, wt) :: wtl) wts [] in
  Smt.Type.declare_record hValType wtl;

  max_params := maxp;

  (* Var and Params in single record *) (* a lot slower *)
  (* for i = 1 to maxp do pl := (mk_hP i, hInt) :: !pl done; *)
  (* let pl = (hV, hWeakVar) :: (List.rev !pl) in *)
  (* Smt.Type.declare_record hVarParam pl; *)
  (* Smt.Type.declare_record hEvent [(hDir, hDirection); (hVar, hVarParam); *)
  (* 				  (hVal, hValType)]; *)

  (* Var inlined in event, Params in record *) (* slightly slower *)
  (* for i = 1 to maxp do pl := (mk_hP i, hInt) :: !pl done; *)
  (* Smt.Type.declare_record hParam (List.rev !pl); *)
  (* Smt.Type.declare_record hEvent [(hDir, hDirection); (hVar, hWeakVar); *)
  (* 				  (hPar, hParam); (hVal, hValType)]; *)

  (* Var and Params inlined in event *)
  for i = 1 to maxp do pl := (mk_hP i, hInt) :: !pl done;
  let pl = (hDir, hDirection) :: (hVar, hWeakVar) ::
  	     (hVal, hValType) :: (List.rev !pl) in
  Smt.Type.declare_record hEvent pl;

  Smt.Symbol.declare hE
    [Smt.Type.type_proc; Smt.Type.type_int; Smt.Type.type_int] hEvent;

  for i = 1 to 50 do Smt.Symbol.declare (mk_hE i) [] Smt.Type.type_int done;
  for i = 1 to 10 do Smt.Symbol.declare (mk_hS i) [] Smt.Type.type_int done;

  let int2 = [Smt.Type.type_int; Smt.Type.type_int] in
  let int4 = [Smt.Type.type_int; Smt.Type.type_int;
	      Smt.Type.type_int; Smt.Type.type_int] in
  let int6 = [Smt.Type.type_int; Smt.Type.type_int;
	      Smt.Type.type_int; Smt.Type.type_int;
	      Smt.Type.type_int; Smt.Type.type_int] in

  Smt.Symbol.declare hPo int4 Smt.Type.type_prop;
  Smt.Symbol.declare hRf int6 Smt.Type.type_prop;
  Smt.Symbol.declare hCo int6 Smt.Type.type_prop;
  Smt.Symbol.declare hFence int4 Smt.Type.type_prop;
  Smt.Symbol.declare hPoLoc int6 Smt.Type.type_prop;
  Smt.Symbol.declare hPpo int6 Smt.Type.type_prop;
  (* Smt.Symbol.declare hCoUProp int4 Smt.Type.type_prop; *)
  (* Smt.Symbol.declare hPoLocUCom int4 Smt.Type.type_prop; *)
  Smt.Symbol.declare hSci int2 Smt.Type.type_int;
  Smt.Symbol.declare hPropi int2 Smt.Type.type_int



module WH = Hashtbl.Make(struct
  type t = (H.t * Variable.t list)
  let equal (v1, vi1) (v2, vi2) =
    H.equal v1 v2 && H.list_equal vi1 vi2
  let hash = Hashtbl.hash
end)

let make_init_write =
  let events = WH.create 16 in
  let nbe = ref 0 in
  fun (v, vi) ->
    try WH.find events (v, vi) with Not_found ->
      let hSi = nbe := !nbe + 1; mk_hS !nbe in
      let tevt = Access (hE, [hP0;hE1;hSi]) in
      let adir = Atom.Comp (Field (tevt, hDir), Eq, Elem (hW, Constr)) in
      let avar = Atom.Comp (Field (tevt, hVar), Eq, Elem (v, Constr)) in
      let sa, _ = List.fold_left (fun (sa, i) v ->
        let apar = Atom.Comp (Field (tevt, mk_hP i), Eq, Elem (v, Var)) in
        (SAtom.add apar sa, i + 1)
      ) (SAtom.add avar (SAtom.singleton adir), 1) vi in
      let vv = H.make (var_of_v v) in
      let vt = if vi = [] then Elem (vv, Glob) else Access (vv, vi) in
      WH.add events (v, vi) ((hP0, hE1, hSi), vt, sa);
      ((hP0, hE1, hSi), vt, sa)



(* Make an event for specified parameters, returns the new atoms and event counts *)
let make_event (cnt, na) d p v vi = 
  let (_, ret) = Smt.Symbol.type_of v in
  let eid, seid = try HMap.find p cnt with Not_found -> (1, 1) in
  let e, s = mk_hE eid, mk_hS seid in
  let tevt = Access (hE, [p;e;s]) in
  let adir = Atom.Comp (Field (tevt, hDir), Eq, Elem (d, Constr)) in

  (* Var and Params in single record *)
  (* let tvar = Field (tevt, hVar) in *)
  (* let avar = Atom.Comp (Field (tvar, hV), Eq, Elem (mk_hV v, Constr)) in *)
  (* let na, i = List.fold_left (fun (na, i) v -> *)
  (*   let apar = Atom.Comp (Field (tvar, mk_hP i), Eq, Elem (v, Var)) in *)
  (*   SAtom.add apar na, i + 1 *)
  (* ) (SAtom.add avar (SAtom.add adir na), 1) vi in *)

  (* Var inlined in event, Params in record *)
  (* let tpar = Field (tevt, hPar) in *)
  (* let avar = Atom.Comp (Field (tevt, hVar), Eq, Elem (mk_hV v, Constr)) in *)
  (* let na, i = List.fold_left (fun (na, i) v -> *)
  (*   let apar = Atom.Comp (Field (tpar, mk_hP i), Eq, Elem (v, Var)) in *)
  (*   SAtom.add apar na, i + 1 *)
  (* ) (SAtom.add avar (SAtom.add adir na), 1) vi in *)

  (* Var and Params inlined in event *)
  let avar = Atom.Comp (Field (tevt, hVar), Eq, Elem (mk_hV v, Constr)) in
  let na, i = List.fold_left (fun (na, i) v ->
    let apar = Atom.Comp (Field (tevt, mk_hP i), Eq, Elem (v, Var)) in
    SAtom.add apar na, i + 1
  ) (SAtom.add avar (SAtom.add adir na), 1) vi in

  (* let rna = ref na in (\* add dummy procs for unsued params *\) *)
  (* for i = i to !max_params do *)
  (*   let apar = Atom.Comp (Field (tevt, mk_hP i), Eq, Elem (hP0, Glob)) in *)
  (*   rna := SAtom.add apar !rna *)
  (* done; *)
  (* let na = !rna in *)

  let cnt = HMap.add p (eid, seid + 1) cnt in
  (cnt, na), Field (Field (tevt, hVal), mk_hT ret)



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




(* Extract events, event counts and fences from sa
   Used when making formula for safety / fixpoint check
   Used in split_events_orders_xxx only *)
let split_event_order (sa, evts, cnt, fce) at =
  let rec update_cnt_t cnt = function
    | Arith (t, _) -> update_cnt_t cnt t
    | Field (Access (a, [p;e;_]), _) when H.equal a hE ->
       let cmin, cmax = try HMap.find p cnt with Not_found -> (max_int, 0) in
       let e = int_of_e e in
       if e > cmax && e < cmin then HMap.add p (e, e) cnt
       else if e > cmax then HMap.add p (cmin, e) cnt
       else if e < cmin then HMap.add p (e, cmax) cnt
       else cnt
    | _ -> cnt
  in
  let rec update_cnt cnt = function
    | Atom.Comp (t1, _, t2) -> update_cnt_t (update_cnt_t cnt t1) t2
    | Atom.Ite (sa, a1, a2) -> update_cnt (update_cnt cnt a1) a2
    | _ -> cnt
  in
  match at with
  | Atom.Comp (Access (a,[p;e]), Eq, Elem _)
  | Atom.Comp (Elem _, Eq, Access (a,[p;e])) when H.equal a hFence ->
     let pfce = try HMap.find p fce with Not_found -> [] in
     let fce = HMap.add p (e :: pfce) fce in (* ot could use a smarter predicate *)
     (sa, evts, cnt, fce) (* we remove the fences, as the predicate can't be used directly *)
  | Atom.Comp (Field (Access (a,[p;e;s]),f), Eq, Elem (c,t))
  | Atom.Comp (Elem (c,t), Eq, Field (Access (a,[p;e;s]),f)) when H.equal a hE->
     let pevts = try HMap.find p evts with Not_found -> HMap.empty in
     let spe = try HMap.find e pevts with Not_found -> HMap.empty in
     let (d, v, vi) = try HMap.find s spe
		      with Not_found -> (hNone, hNone, []) in
     let d = if f = hDir then c else d in
     let v = if f = hVar then c else v in
     let vi = if List.exists (fun (p, _) -> H.equal f p) !pl
	      then (f, c) :: vi else vi in 
     (SAtom.add at sa,
      HMap.add p (HMap.add e (HMap.add s (d, v, vi) spe) pevts) evts,
      update_cnt cnt at, fce)
  | _ -> (SAtom.add at sa, evts, cnt, fce)

(* Used in split_events_orders_xxx only *)
let sort_event_params =
  HMap.map (HMap.map (HMap.map (fun (d, v, vi) ->
    (d, v, List.sort (fun (p1, _) (p2, _) -> H.compare p1 p2) vi)
  )))

(* Used in split_events_orders_xxx only *)
let make_ord cnt fce =
  HMap.fold (fun p (cmin, cmax) ord ->
    let pfce = try HMap.find p fce with Not_found -> [] in
    let pord = ref [] in
    for i = cmin to cmax do
      let e = mk_hE i in
      if List.exists (fun f -> H.equal f e) pfce then pord := hF :: e :: !pord
      else pord := e :: !pord
    done;
    HMap.add p !pord ord
  ) cnt HMap.empty

(* Used when making formula for safety / fixpoint check *)
let split_events_orders_array ar =
  let sa, evts, cnt, fce = Array.fold_left (fun acc a ->
    split_event_order acc a
  ) (SAtom.empty, HMap.empty, HMap.empty, HMap.empty) ar in
  sa, sort_event_params evts, make_ord cnt fce

(* Used when making formula for safety / fixpoint check *)
let split_events_orders_set sa =
  let sa, evts, cnt, fce = SAtom.fold (fun a acc ->
    split_event_order acc a
  ) sa (SAtom.empty, HMap.empty, HMap.empty, HMap.empty) in
  sa, sort_event_params evts, make_ord cnt fce



(* Used internally by split_event *)
let find_event_safe eid evts =
  try H3Map.find eid evts
  (* with Not_found -> (hNone, hNone, [], false, Eq, Elem (hNone, Glob)) *)
  with Not_found -> (hNone, hNone, [], [])

(* Used internally by split_event *)
let is_param f =
  List.exists (fun (p, _) -> H.equal f p) !pl

(* Used internally by split_event *)
let rec split_event_t = function
  | Field (Field (Access (a, [p; e; s]), f), _)
       when H.equal a hE && H.equal f hVal ->
     Some (p, e, s), None
  | Arith (t, c) ->
     fst (split_event_t t), Some c
  | _ -> None, None

(* Used internally by split_event *)
let subs_const_from_term cs =
  let cs = Types.mult_const (-1) cs in
  function
  | Const c -> Const (Types.add_constants c cs)
  | Arith (t, c) -> Arith (t, Types.add_constants c cs)
  | t -> Arith (t, cs)

(* Used internally by split_event *)
let process_event eid c rev op tv evts = match eid with
  | Some eid -> (* SHOULD LINK WITH A VALUE LIST (several values possible) !!! *)
     (* let (d, v, vi, _, _, _) = find_event_safe eid evts in *)
     let (d, v, vi, vals) = find_event_safe eid evts in
     let tv = match c with Some c -> subs_const_from_term c tv | _ -> tv in
     (* H3Map.add eid (d, v, vi, rev, op, tv) evts *)
     H3Map.add eid (d, v, vi, (rev, op, tv) :: vals) evts
  | None -> evts

let split_event at evts = match at with
  (* Direction / Variable / Indices *)
  | Atom.Comp (Field (Access (a, [p; e; s]), f), Eq, Elem (c, t))
  | Atom.Comp (Elem (c, t), Eq, Field (Access (a, [p; e; s]), f))
       when H.equal a hE ->
     (* let (d, v, vi, r, op, tv) as evt = find_event_safe (p, e, s) evts in *)
     (* let evt = if H.equal f hDir then (c, v, vi, r, op, tv) *)
     (* 	  else if H.equal f hVar then (d, c, vi, r, op, tv) *)
     (* 	  else if is_param f then (d, v, (f, c) :: vi, r, op, tv) *)
     (* 	  else evt in *)
     let (d, v, vi, vals) as evt = find_event_safe (p, e, s) evts in
     let evt = if H.equal f hDir then (c, v, vi, vals)
	  else if H.equal f hVar then (d, c, vi, vals)
	  else if is_param f then (d, v, (f, c) :: vi, vals)
	  else evt in
     H3Map.add (p, e, s) evt evts
  (* Value *)
  | Atom.Comp (t1, op, t2) ->
     let eid1, c1 = split_event_t t1 in
     let eid2, c2 = split_event_t t2 in
     let evts = process_event eid1 c1 false op t2 evts in
     process_event eid2 c2 true op t1 evts
  (* Others *)
  | _ -> evts

(*let split_event at evts = match at, false, true with
  (* Value *)
  | Atom.Comp ((Field (Field (Access (a1, [p1; e1; s1]), f1), _) as tv2), op,
	       (Field (Field (Access (a2, [p2; e2; s2]), f2), _) as tv1)), _, _
       when H.equal a1 hE && H.equal f1 hVal &&
	    H.equal a2 hE && H.equal f2 hVal ->
     let (d1, v1, vi1, _, _, _) = find_event_safe (p1, e1, s1) evts in
     let evts = H3Map.add (p1, e1, s1) (d1, v1, vi1, false, op, tv1) evts in
     let (d2, v2, vi2, _, _, _) = find_event_safe (p2, e2, s2) evts in
     H3Map.add (p2, e2, s2) (d2, v2, vi2, true, op, tv2) evts
  | Atom.Comp (Field (Field (Access (a, [p; e; s]), f), _), op, tv), r, _
  | Atom.Comp (tv, op, Field (Field (Access (a, [p; e; s]), f), _)), _, r
       when H.equal a hE && H.equal f hVal ->
     let (d, v, vi, _, _, _) = find_event_safe (p, e, s) evts in
     H3Map.add (p, e, s) (d, v, vi, r, op, tv) evts
  (* Direction / Variable / Indices *)
  | Atom.Comp (Field (Access (a, [p; e; s]), f), Eq, Elem (c, t)), _, _
  | Atom.Comp (Elem (c, t), Eq, Field (Access (a, [p; e; s]), f)), _, _
       when H.equal a hE ->
     let (d, v, vi, r, op, tv) as evt = find_event_safe (p, e, s) evts in
     let evt = if H.equal f hDir then (c, v, vi, r, op, tv)
	  else if H.equal f hVar then (d, c, vi, r, op, tv)
	  else if is_param f then (d, v, (f, c) :: vi, r, op, tv)
	  else evt in
     H3Map.add (p, e, s) evt evts
  (* Others *)
  | _ -> evts*)


	   
let events_by_thread sa =
  let evts = SAtom.fold split_event sa H3Map.empty in
  let evts = H3Map.fold (fun (p, e, s) evt evts ->
    let pevts = try HMap.find p evts with Not_found -> [] in
    let pevts = ((p, e, s), evt) :: pevts in
    HMap.add p pevts evts
  ) evts HMap.empty in
(*
  Format.eprintf "Events by thread : \n";
  HMap.iter (fun p pevts ->
    Format.eprintf "%a :" H.print p;
    List.iter (fun ((p, e, s), (d, v, vi, r, op, t)) ->
      Format.eprintf " (%a,%a,%a:%a%a)" H.print p H.print e H.print s
		                        H.print d H.print v
    ) pevts;
    Format.eprintf "\n"
  ) evts;
 *)
  evts


let compatible_values wt op rt r =
  match wt, rt with
  | Const c1, Const c2 ->
      let c = Types.compare_constants c1 c2 in
      let c = if r then -c else c in
      if op = Eq && c <> 0 then false
      else if op = Neq && c = 0 then false
      else if op = Lt && c >= 0 then false
      else if op = Le && c > 0 then false
      else true
  (* | Elem (e1, s1), Elem (e2, s2) -> true *)
  (* | Access (a1, ai1), Access (a2, ai2) -> true *)
  (* | Arith (t1, c1), Arith (t2, c2) -> true *)
  | _ -> true

let split_read_chunk (_, wv, wvi, wt) pevts =
  let wv = H.make ("_V" ^ (H.view wv)) in
  let is_read (_, (d, _, _, _)) =
    let r = H.equal d hR in
    (* Format.eprintf "is_read : %b\n" r; r *) r
    in
  let same_var (_, (_, v, vi, _)) =
    let r = H.equal wv v && List.for_all2 (fun wi (_, i) -> H.equal wi i) wvi vi in
    (* Format.eprintf "same_var : %b\n" r; r *) r
    in
  (* let compat_val (_, (_, _, _, r, op, t)) = *)
  (*   let r = compatible_values wt op t r in *)
  (*   (\* Format.eprintf "compat_val : %b\n" r; r *\) r *)
  (*   in *)
  let compat_val (_, (_, _, _, vals)) =    
    let r = List.for_all (fun (r, op, t) -> compatible_values wt op t r) vals in
    (* Format.eprintf "compat_val : %b\n" r; r *) r
    in
  (* let is_satisfied (_, (_, _, _, _, _, t)) = let r = match t with *)
  (*   | Elem (h, Glob) when H.equal h hNone -> true *)
  (*   | _ -> false in *)
  (*   (\* Format.eprintf "is_sat : %b\n" r; r *\) r *)
  (*   in *)
  let is_satisfied (_, (_, _, _, (vals))) = let r = match vals with
    | [] -> true
    | _ -> false in
    (* Format.eprintf "is_sat : %b\n" r; r *) r
    in
  let rec aux chunk = function (* all reads should also be inter-compatible *)
    | [] -> List.rev chunk, []
    | e :: pevts ->
       (* let (p, (d, v, vi, _)) = e in *)
       (* Format.eprintf "split %a %a\n" H.print d H.print v; *)
       if not (same_var e) then aux chunk pevts
       else if not (is_read e) || is_satisfied e || not (compat_val e) then
	 List.rev chunk, pevts
       else aux (e :: chunk) pevts
  in
  aux [] pevts
	    
let read_chunks_for_write same_thread w pevts =
  let wp, wv, wvi, wt = w in
  (* Format.eprintf "rcfw %b %a %a\n" same_thread H.print wp H.print wv; *)
  let rec aux chunks = function
    | [] -> List.rev chunks
    | pevts ->
       let chunk, pevts = split_read_chunk w pevts in
       if same_thread then [chunk] else begin
        if chunk = [] then aux chunks pevts
        else aux (chunk :: chunks) pevts end
  in
  aux [] pevts

let read_chunks_by_thread_by_write writes evts = (* evts by thread *)
  List.fold_left (fun rctw ((wp, wv, wvi, wt) as w) ->
    let rct = HMap.fold (fun p pevts rct ->
      let rc = read_chunks_for_write (H.equal wp p) w pevts in
      (p, rc) :: rct
    ) evts [] in
    (w, rct) :: rctw
  ) [] writes

let read_combs same_thread rl =
  let rec aux = function
  | [] -> []
  | [r] -> [[r]]
  | r :: rl ->
     let combs = aux rl in
     List.fold_left (fun combs c -> [r] :: (r :: c) :: combs)
		    (if same_thread then [] else combs) combs
  in
  aux rl

let read_combs_by_thread_by_write rctw =
  List.fold_left (fun rctw (((wp, _, _, _) as w), rct) ->
    let rct = List.fold_left (fun rct (p, rc) ->
      let rc = List.fold_left (fun rc rl ->
        (read_combs (H.equal wp p) rl) @ rc
      ) [] rc in (* rc <- all read combinations for this thread *)
      (p, rc) :: rct (* source rc is a list of chunks *)
    ) [] rct in
    (w, rct) :: rctw
  ) [] rctw

let read_combs_by_write rctw =
  List.fold_left (fun rcw (((wp, wv, wi, wt) as w), rct) ->
    let lrc = List.fold_left (fun lrc (p, rcl) ->
      List.fold_left (fun lrc crc ->
        List.fold_left (fun lrc rc ->
	  (rc @ crc) :: lrc
        ) lrc rcl
      ) lrc lrc
    ) [[]] rct in
    (w, lrc) :: rcw
  ) [] rctw

let all_combinations rcw =
  let make_combs combs w lrc cc =
    List.fold_left (fun combs rc ->
      ((w, rc) :: cc) :: combs
    ) combs lrc
  in
  let combs, rcw = match rcw with
    | [] -> [[]], []
    | (w, lrc) :: rcw -> make_combs [] w lrc [], rcw
  in
  List.fold_left (fun combs (w, lrc) ->
    List.fold_left (fun combs cc ->
      make_combs combs w lrc cc			  
    ) [] combs
  ) combs rcw
  
let make_read_write_combinations writes sa =
  let evts = events_by_thread sa in
  let rctw = read_chunks_by_thread_by_write writes evts in
  let rctw2 = read_combs_by_thread_by_write rctw in
  let rcw = read_combs_by_write rctw2 in
  let combs = all_combinations rcw in
  combs



let is_value = function
  | Elem (h, Glob) when H.equal h hNone -> false
  | _ -> true

(* let unsatisfied_reads sa = *)
(*   let evts = SAtom.fold split_event sa H3Map.empty in *)
(*   let ur = H3Map.fold (fun eid (d, v, vi, r, op, tv) ur -> *)
(*     if d = hR && is_value tv then *)
(*       H3Map.add eid (v, List.map (fun (_, i) -> i) vi) ur *)
(*     else ur *)
(*   ) evts H3Map.empty in *)
(*   ur *)
let unsatisfied_reads sa =
  let evts = SAtom.fold split_event sa H3Map.empty in
  let ur = H3Map.fold (fun eid (d, v, vi, vals) ur ->
    if d = hR && vals <> [] then
      H3Map.add eid (v, List.map (fun (_, i) -> i) vi) ur
    else ur
  ) evts H3Map.empty in
  ur



		
let rec hpl_equal hpl1 hpl2 = match hpl1, hpl2 with
  | [], [] -> true
  | [], _ | _, [] -> false
  | (hl1, hr1) :: hpl1, (hl2, hr2) :: hpl2 ->
     if H.equal hl1 hl2 && H.equal hr1 hr2 then hpl_equal hpl1 hpl2
     else false



let same_var (_, v1, pl1) (_, v2, pl2) = H.equal v1 v2 && hpl_equal pl1 pl2
let is_read (d, _, _) = H.equal d hR
let is_write (d, _, _) = H.equal d hW
let is_fence hs = H.equal hs hF
let is_p0 hs = H.equal hs hP0

let pick_event evts =
  let p, pevts = HMap.choose evts in
  let evts = HMap.remove p evts in
  p, pevts, evts

let filter_writes evts =
  HMap.fold (fun p pe w ->
    let pw = HMap.fold (fun e spe pw ->
      let spw = HMap.filter (fun s ed -> is_write ed) spe in
      HMap.add e spw pw) pe HMap.empty in
    HMap.add p pw w) evts HMap.empty

let partition_rw evts =
  HMap.fold (fun p pe (r, w) ->
    let pr, pw = HMap.fold (fun e spe (pr, pw) ->
      let spr, spw = HMap.partition (fun s ed -> is_read ed) spe in
      (HMap.add e spr pr, HMap.add e spw pw)
    ) pe (HMap.empty, HMap.empty) in
    (HMap.add p pr r, HMap.add p pw w)
  ) evts (HMap.empty, HMap.empty)



let gen_po ord =
  let rec aux p po = function
    | [] | [_] -> po
    | f :: pord when is_fence f -> aux p po pord
    | e1 :: pord ->
       let po = List.fold_left (fun po e2 ->
         if is_fence e2 then po else [p;e1;p;e2] :: po
       ) po pord in
       aux p po pord
  in
  HMap.fold (fun p pord po -> aux p po pord) ord []

let rec gen_po_pred pred evts ord =
  let rec aux p po pevts = function
    | [] | [_] -> po
    | f :: pord when is_fence f -> aux p po pevts pord
    | e1 :: pord ->
       let spe1 = HMap.find e1 pevts in
       let po = List.fold_left (fun po e2 ->
         if is_fence e2 then po else
         let spe2 = HMap.find e2 pevts in
         HMap.fold (fun s1 ed1 -> HMap.fold (fun s2 ed2 po ->
           if pred ed1 ed2 then [p;e1;s1;p;e2;s2] :: po else po
         ) spe2) spe1 po
       ) po pord in
       aux p po pevts pord
  in
  HMap.fold (fun p pord po -> aux p po (HMap.find p evts) pord) ord []

let gen_po_loc =
  gen_po_pred (fun ed1 ed2 -> same_var ed1 ed2)

let gen_ppo_tso =
  gen_po_pred (fun ed1 ed2 -> not (is_write ed1 && is_read ed2))

let gen_fence evts ord =
(*  HMap.iter (fun p pevts -> HMap.iter (fun e sevts -> HMap.iter (fun s (d, vr, vl) ->
    Format.eprintf "%a%a%a:%a%a\n" H.print p H.print e H.print s H.print d H.print vr
  ) sevts) pevts) evts;
  HMap.iter (fun p evts ->
    Format.eprintf "%a : " H.print p;
    List.iter (fun e -> Format.eprintf "%a " H.print e) evts;
    Format.eprintf "\n"
  ) ord; *)
  let rec split_at_first_fence lpord = function
    | [] -> lpord, []
    | f :: rpord when is_fence f -> lpord, rpord
    | e :: rpord -> split_at_first_fence (e :: lpord) rpord
  in
  let rec first_event dir p = function
    | [] -> None
    | f :: pord when is_fence f -> first_event dir p pord
    | e :: pord ->
       let pevts = HMap.find p evts in
       begin try
	 let spe = HMap.find e pevts in
         if HMap.exists (fun _ (d, _, _) -> H.equal d dir) spe
         then Some e else first_event dir p pord
       with Not_found -> first_event dir p pord end
  in
  let rec aux p fence lpord rpord = match rpord with
    | [] -> fence
    | _ ->
       let lpord, rpord = split_at_first_fence lpord rpord in
       match first_event hW p lpord, first_event hR p rpord with
       | Some w, Some r -> aux p ([p; w; p; r] :: fence) lpord rpord
       | _, _ -> aux p fence lpord rpord
  in
  HMap.fold (fun p pord fence -> aux p fence [] pord) ord []

let gen_co evts ord =
  let iwrites, writes =
    HMap.partition (fun p _ -> is_p0 p) (filter_writes evts) in
  (* Initial writes *)
  let co = HMap.fold (fun p1 -> HMap.fold (fun e1 -> HMap.fold (fun s1 ed1 ->
    HMap.fold (fun p2 -> HMap.fold (fun e2 -> HMap.fold (fun s2 ed2 co ->
      if same_var ed1 ed2 then [p1;e1;s1;p2;e2;s2] :: co else co
    ))) writes
  ))) iwrites [] in
  (* Writes from same thread *)
  let rec aux p co pwrites = function
    | [] | [_] -> co
    | f :: pord when is_fence f -> aux p co pwrites pord
    | e1 :: pord ->
       let spe1 = HMap.find e1 pwrites in
       let co = List.fold_left (fun co e2 ->
	 if is_fence e2 then co else
	 let spe2 = HMap.find e2 pwrites in
	 HMap.fold (fun s1 ed1 -> HMap.fold (fun s2 ed2 co ->
	   if same_var ed1 ed2 then [p;e1;s1;p;e2;s2] :: co else co
	 ) spe2) spe1 co
       ) co pord in
       aux p co pwrites pord
  in
  HMap.fold (fun p pord co ->
    aux p co (HMap.find p writes) pord
  ) (HMap.remove hP0 ord) co

let gen_co_cands evts =
  let rec aux writes cco = try
    let p1, p1writes, writes = pick_event writes in
    let cco = HMap.fold (fun e1 -> HMap.fold (fun s1 ed1 cco ->
      HMap.fold (fun p2 -> HMap.fold (fun e2 -> HMap.fold (fun s2 ed2 cco ->
        if same_var ed1 ed2
	then [[p1;e1;s1;p2;e2;s2];[p2;e2;s2;p1;e1;s1]] :: cco else cco
      ))) writes cco
    )) p1writes cco in
    aux writes cco
    with Not_found -> cco
  in
  aux (filter_writes (HMap.remove hP0 evts)) []

(* should exclude trivially false rf (use value/const) *)
(* for inter-thread read, should only read from the most recent *)
(*let gen_rf_cands evts =
  let reads, writes = partition_rw evts in
  HMap.fold (fun p1 -> HMap.fold (fun e1 -> HMap.fold (fun s1 ed1 crf ->
    let ecrf = HMap.fold (fun p2 -> HMap.fold (fun e2 ->
      HMap.fold (fun s2 ed2 ecrf ->
	if same_var ed1 ed2 then [p2;e2;s2;p1;e1;s1] :: ecrf else ecrf
    ))) writes [] in
    if ecrf = [] then crf else ecrf :: crf
  ))) reads [] *)



let make_rel r pl1 pl2 =
  let pl1 = List.map (fun p -> T.make_app p []) pl1 in
  let pl2 = List.map (fun p -> T.make_app p []) pl2 in
  F.make_lit F.Le [ T.make_app r pl1 ; T.make_app r pl2 ]

let make_rell r el f =
  List.fold_left (fun f e -> make_rel r e :: f) f el

let make_pred p pl b =
  let pl = List.map (fun p -> T.make_app p []) pl in
  let tb = if b then T.t_true else T.t_false in
  F.make_lit F.Eq [ T.make_app p pl ; tb ]

let make_predl p el f =
  List.fold_left (fun f e -> make_pred p e true :: f) f el

let make_predl_dl p ell f =
  List.fold_left (fun f el -> (F.make F.Or (make_predl p el [])) :: f) f ell

(*
let make_predrfl_dl ell f =
  List.fold_left (fun f el ->
    (F.make F.Or (
      List.fold_left (fun f e ->
	(F.make F.And [ make_pred hRf e true ;
	  let (p1, e1, p2, e2) = e in
	  let p1, p2 = T.make_app p1 [], T.make_app p2 [] in
	  let e1, e2 = T.make_app e1 [], T.make_app e2 [] in
	  let a1 = T.make_app hE [ p1; e1 ] in
	  let a2 = T.make_app hE [ p2; e2 ] in
	  let t1 = T.make_app hVal [ a1 ] in
	  let t2 = T.make_app hVal [ a2 ] in
	  F.make_lit F.Eq [ t1 ; t2 ]
	]) :: f
      ) [] el
    )) :: f
  ) f ell
 *)
let make_orders_fp evts ord =
  let f = [] in
  (* let f = make_predl hPo (gen_po ord) f in *) (* not necessary for fixpoint *)
  let f = make_predl hFence (gen_fence evts ord) f in
  f

let make_orders_sat evts ord =
  let f = [] in

  (* let f = make_predl hPo (gen_po ord) f in *) (* not necessary here either *)
    (* let f = make_predl hPoLocUCom (gen_po_loc evts ord) f in *)
    (* let f = make_predl hCoUProp (gen_ppo_tso evts ord) f in *)
    let f = make_predl hPoLoc (gen_po_loc evts ord) f in
    let f = make_predl hPpo (gen_ppo_tso evts ord) f in
    (* let f = make_rell (Hstring.make "_sci") (gen_po_loc evts ord) f in *)
    (* let f = make_rell (Hstring.make "_propi") (gen_ppo_tso evts ord) f in *)

  let f = make_predl hFence (gen_fence evts ord) f in
    (* let f = make_predl hCoUProp (gen_fence evts ord) f in *)
    (* let f = make_rell (Hstring.make "_propi") (gen_fence evts ord) f in *)

  let f = make_predl hCo (gen_co evts ord) f in
  (* let f = make_predl hPoLocUCom (gen_co evts ord) f in *)
  (* let f = make_predl hCoUProp (gen_co evts ord) f in *)
  (* let f = make_rell (Hstring.make "_sci") (gen_co evts ord) f in *)
  (* let f = make_rell (Hstring.make "_propi") (gen_co evts ord) f in *)

(*  let f = make_predl_dl hRf (gen_rf_cands evts) f in (*no value test*)*)
    (* let f = make_predrfl_dl (gen_rf_cands evts) f in (\* with value test *\) *)

  let f = make_predl_dl hCo (gen_co_cands evts) f in

  (* let f = HMap.fold (fun p -> HMap.fold (fun e _ f -> *)
  (*   make_pred hPoLocUCom (p, e, p, e) false :: *)
  (*   make_pred hCoUProp (p, e, p, e) false :: f *)
  (* )) evts f in *)

  f

let make_orders ?(fp=false) evts ord =
  let f = if fp then make_orders_fp evts ord
	  else make_orders_sat evts ord in
  if f = [] then F.f_true else
  F.make F.And f
