
open Weakmem
open Types

module T = Smt.Term
module F = Smt.Formula



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
     let vi = if is_param f then (f, c) :: vi else vi in 
     (SAtom.add at sa,
      HMap.add p (HMap.add e (HMap.add s (d, v, vi) spe) pevts) evts,
      update_cnt cnt at, fce)
  | _ -> (SAtom.add at sa, evts, cnt, fce)

(* Used in split_events_orders_xxx only *)
let sort_event_params =
  HMap.map (HMap.map (HMap.map (fun (d, v, vi) ->
    let vi = List.sort_uniq (fun (p1, _) (p2, _) -> H.compare p1 p2) vi in
    (d, v, List.map (fun (_, i) -> i) vi)
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
  F.make_lit F.Lt [ T.make_app r pl1 ; T.make_app r pl2 ]

(* let make_rell r el f = *)
(*   List.fold_left (fun f e -> make_rel r e :: f) f el *)
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
  List.fold_left (fun f el -> (F.make F.Or (make_rell r el [])) :: f) f ell

let make_pred p pl b =
  let pl = List.map (fun p -> T.make_app p []) pl in
  let tb = if b then T.t_true else T.t_false in
  F.make_lit F.Eq [ T.make_app p pl ; tb ]

let make_predl p el f =
  List.fold_left (fun f e -> make_pred p e true :: f) f el

let make_predl_dl p ell f =
  List.fold_left (fun f el -> (F.make F.Or (make_predl p el [])) :: f) f ell

(*let make_predrfl_dl ell f =
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
  ) f ell*)

let make_orders_fp evts ord =
  let f = [] in
  (* let f = make_predl hPo (gen_po ord) f in *) (* not necessary for fixpoint *)
  let f = make_predl hFence (gen_fence evts ord) f in
  f

let make_orders_sat evts ord =
  let f = [] in

  (* po_loc U com / co U prop *)
  (* let f = make_predl hPo (gen_po ord) f in not necessary here either *)
    let f = make_predl hPoLoc (gen_po_loc evts ord) f in
    let f = make_predl hPpo (gen_ppo_tso evts ord) f in
    (* let f = make_rell (Hstring.make "_sci") (gen_po_loc evts ord) f in *)
    (* let f = make_rell (Hstring.make "_propi") (gen_ppo_tso evts ord) f in *)

  (* co U prop *)
  let f = make_predl hFence (gen_fence evts ord) f in
    (* let f = make_rell (Hstring.make "_propi") (gen_fence evts ord) f in *)

  (* po_loc U com / co U prop *)
  let f = make_predl hCo (gen_co evts ord) f in
  (* let f = make_rell (Hstring.make "_coi") (gen_co evts ord) f in *)
  (* let f = make_rell (Hstring.make "_sci") (gen_co evts ord) f in *)
  (* let f = make_rell (Hstring.make "_propi") (gen_co evts ord) f in *)

(*  let f = make_predl_dl hRf (gen_rf_cands evts) f in (*no value test*)*)
    (* let f = make_predrfl_dl (gen_rf_cands evts) f in (\* with value test *\) *)

  let f = make_predl_dl hCo (gen_co_cands evts) f in
  (* let f = make_rell_dl (Hstring.make "_coi") (gen_co_cands evts) f in *)

  f

let make_orders ?(fp=false) evts ord =
  let f = if fp then make_orders_fp evts ord
	  else make_orders_sat evts ord in
  if f = [] then F.f_true else
  F.make F.And f
