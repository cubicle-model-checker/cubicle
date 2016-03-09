
open Types

module H = Hstring
module HMap = Hstring.HMap
module HSet = Hstring.HSet
module T = Smt.Term
module S = Smt.Symbol
module F = Smt.Formula
module STerm = Term.Set



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
let hPo = H.make "_po"
let hRf = H.make "_rf"
let hCo = H.make "_co"
let hFence = H.make "_fence"
let hCoUProp = H.make "_co_U_prop"
let hPoLocUCom = H.make "_po_loc_U_com"
let mk_hE e = H.make ("_e" ^ (string_of_int e))
let mk_hV hv = H.make ("_V" ^ (H.view hv))
let mk_hP p = H.make ("_p" ^ (string_of_int p))
let mk_hT ht = H.make ("_t" ^ (H.view ht))



let max_params = ref 0
let pl = ref []



let init_weak_env wvl =

  Smt.Type.declare hDirection [hR; hW];
  Smt.Type.declare hWeakVar (List.map (fun (v, _, _) -> mk_hV v) wvl);

  let wts, maxp = List.fold_left (fun (wts, maxp) (wv, args, ret) ->
    (* let (args, ret) = Smt.Symbol.type_of wv in *)
    let nbp = List.length args in
    HSet.add ret wts, if nbp > maxp then nbp else maxp
  ) (HSet.empty, 1) wvl in

  max_params := maxp;
  
  let wtl = HSet.fold (fun wt wtl -> (mk_hT wt, wt) :: wtl) wts [] in
  Smt.Type.declare_record hValType wtl;


  (* Var and Params in single record *)
  (* for i = 1 to maxp do pl := (mk_hP i, hInt) :: !pl done; *)
  (* let pl = (hV, hWeakVar) :: (List.rev !pl) in *)
  (* Smt.Type.declare_record hVarParam pl; *)
  (* Smt.Type.declare_record hEvent [(hDir, hDirection); (hVar, hVarParam); *)
  (* 				  (hVal, hValType)]; *)


  (* Var inlined in event, Params in record *)
  (* for i = 1 to maxp do pl := (mk_hP i, hInt) :: !pl done; *)
  (* Smt.Type.declare_record hParam (List.rev !pl); *)
  (* Smt.Type.declare_record hEvent [(hDir, hDirection); (hVar, hWeakVar); *)
  (* 				  (hPar, hParam); (hVal, hValType)]; *)


  (* Var and Params inlined in event *)
  for i = 1 to maxp do pl := (mk_hP i, hInt) :: !pl done;
  let pl = (hDir, hDirection) :: (hVar, hWeakVar) ::
	     (hVal, (*hInt*)hValType) :: (List.rev !pl) in
  Smt.Type.declare_record hEvent pl;

  (* No Params *)
  (* Smt.Type.declare_record hEvent [(hDir, hDirection); (hVar, hWeakVar); *)
  (* 				  (hVal, (*hInt*)hValType)]; *)


  Smt.Symbol.declare hE [Smt.Type.type_proc; Smt.Type.type_int] hEvent;
  for i = 1 to 20 do Smt.Symbol.declare (mk_hE i) [] Smt.Type.type_int done;
  let int4 = [Smt.Type.type_int; Smt.Type.type_int;
	      Smt.Type.type_int; Smt.Type.type_int] in
  Smt.Symbol.declare hPo int4 Smt.Type.type_prop;
  Smt.Symbol.declare hRf int4 Smt.Type.type_prop;
  Smt.Symbol.declare hCo int4 Smt.Type.type_prop;
  Smt.Symbol.declare hFence int4 Smt.Type.type_prop;
  Smt.Symbol.declare hCoUProp int4 Smt.Type.type_prop;
  Smt.Symbol.declare hPoLocUCom int4 Smt.Type.type_prop;

  let int2 = [Smt.Type.type_int; Smt.Type.type_int] in
  Smt.Symbol.declare (Hstring.make "_sci") int2 Smt.Type.type_int;
  Smt.Symbol.declare (Hstring.make "_propi") int2 Smt.Type.type_int



let writes_of_init wvl init =
  let wvs = List.fold_left (fun wvs (v, vi, _) ->
			    HMap.add v vi wvs) HMap.empty wvl in
  let aux wvs = function
  | Elem (v, Glob) when Smt.Symbol.is_weak v ->
     Write (hP0, v, []), HMap.remove v wvs
  | Access (v, vi) when Smt.Symbol.is_weak v ->
     Write (hP0, v, vi), HMap.remove v wvs
  | t -> t, wvs in
  List.map (fun sa ->
    let sa, wvs = SAtom.fold (fun a (sa, wvs) ->
      let a, wvs = match a with
      | Atom.Comp (t1, op, t2) ->
         let t1, wvs = aux wvs t1 in
         let t2, wvs = aux wvs t2 in
         Atom.Comp (t1, op, t2), wvs
      | _ -> a, wvs in
      SAtom.add a sa, wvs
    ) sa (SAtom.empty, wvs) in
    HMap.fold (fun v vi sa ->
      let a = Atom.Comp (Write (hP0, v, vi), Eq, Elem (hNone, Glob)) in
      SAtom.add a sa
    ) wvs sa
  ) init



let split_events_orders sa =
  SAtom.fold (fun a (sa_pure, sa_evts, fce, ord, cnt) ->
    match a with
    | Atom.Comp (Access (a, [p]), Eq, List tl)
    | Atom.Comp (List tl, Eq, Access (a, [p])) when H.equal a hO ->
       let c = List.fold_left (fun c t -> match t with
         | Elem (e, Glob) -> if H.equal e hF then c else c + 1
	 | _ -> failwith "Weakmem.split_events_order error"
       ) 0 tl in
       (sa_pure, sa_evts, fce, HMap.add p tl ord, HMap.add p c cnt)
    | Atom.Comp (Write _, _, _) | Atom.Comp (_, _, Write _)
    | Atom.Comp (Read _, _, _) | Atom.Comp (_, _, Read _) ->
       (sa_pure, SAtom.add a sa_evts, fce, ord, cnt)
    | Atom.Comp (Fence p, Eq, _) | Atom.Comp (_, Eq, Fence p) ->
       (sa_pure, sa_evts, p :: fce, ord, cnt)
    | _ -> (SAtom.add a sa_pure, sa_evts, fce, ord, cnt)
) sa (SAtom.empty, SAtom.empty, [], HMap.empty, HMap.empty)



let make_event (cnt, ord, na) d p v vi = 
  let (_, ret) = Smt.Symbol.type_of v in
  let eid = (try HMap.find p cnt with Not_found -> 0) + 1 in
  let pord = try HMap.find p ord with Not_found -> [] in
  let e = mk_hE eid in
  let tevt = Access (hE, [p; e]) in
  let adir = Atom.Comp (Field (tevt, hDir), Eq, Elem (d, Constr)) in


  (* Var and Params in single record *) (* P : 12.8, PX : 5.4 / 34K-27K *)
  (* let tvar = Field (tevt, hVar) in *)
  (* let avar = Atom.Comp (Field (tvar, hV), Eq, Elem (mk_hV v, Constr)) in *)
  (* let na, i = List.fold_left (fun (na, i) v -> *)
  (*   let apar = Atom.Comp (Field (tvar, mk_hP i), Eq, Elem (v, Var)) in *)
  (*   SAtom.add apar na, i + 1 *)
  (* ) (SAtom.add avar (SAtom.add adir na), 1) vi in *)


  (* Var inlined in event, Params in record *) (* P : 3.3, PX : 4.0 / 2.9-2.8K*)
  (* let tpar = Field (tevt, hPar) in *)
  (* let avar = Atom.Comp (Field (tevt, hVar), Eq, Elem (mk_hV v, Constr)) in *)
  (* let na, i = List.fold_left (fun (na, i) v -> *)
  (*   let apar = Atom.Comp (Field (tpar, mk_hP i), Eq, Elem (v, Var)) in *)
  (*   SAtom.add apar na, i + 1 *)
  (* ) (SAtom.add avar (SAtom.add adir na), 1) vi in *)


  (* Var and Params inlined in event *) (* P : 3.3, PX : 3.7 2.9-2.8K *)
  let avar = Atom.Comp (Field (tevt, hVar), Eq, Elem (mk_hV v, Constr)) in
  let na, i = List.fold_left (fun (na, i) v ->
    let apar = Atom.Comp (Field (tevt, mk_hP i), Eq, Elem (v, Var)) in
    SAtom.add apar na, i + 1
  ) (SAtom.add avar (SAtom.add adir na), 1) vi in


  (* No Params *) (* P : 2.6, PX : 2.9* / 561-540 *)
  (* let avar = Atom.Comp (Field (tevt, hVar), Eq, Elem (mk_hV v, Constr)) in *)
  (* let na = SAtom.add avar (SAtom.add adir na) in *)

  
  (* let rna = ref na in (\* add dummy procs for unsued params *\) *)
  (* for i = i to !max_params do *)
  (*   let apar = Atom.Comp (Field (tevt, mk_hP i), Eq, Elem (hP0, Glob)) in *)
  (*   rna := SAtom.add apar !rna *)
  (* done; *)
  (* let na = !rna in *)


  let cnt = HMap.add p eid cnt in
  let ord = HMap.add p (Elem (e, Glob) :: pord) ord in
  (cnt, ord, na), Field (Field (tevt, hVal), mk_hT ret)

  (* & no Type P : 2.5, PX : 2.7* / 561-540 *)
  (* (cnt, ord, na), Field (tevt, hVal) *)



(*
let write_of_term acc = function
  | Write (p, v, vi) -> make_event acc hW p v vi
  | t -> acc, t

let read_of_term acc = function
  | Read (p, v, vi) -> make_event acc hR p v vi
  | t -> acc, t

let events_of_atom fct acc = function
  | Atom.Comp (t1, op, t2) ->
     let acc, t1 = fct acc t1 in
     let acc, t2 = fct acc t2 in
     acc, Atom.Comp (t1, op, t2)
  | a -> acc, a

let events_of_satom sa =
  let sa_pure, sa_evts, fce, ord, cnt = split_events_orders sa in

  let (acc, sa_evts) = SAtom.fold (fun a (acc, sa) ->
    let acc, a = events_of_atom write_of_term acc a in
    (acc, SAtom.add a sa)
  ) sa_evts ((cnt, ord, SAtom.empty), SAtom.empty) in

  let ((_, ord, sa_new), sa_evts) = SAtom.fold (fun a (acc, sa) ->
    let acc, a = events_of_atom read_of_term acc a in
    (acc, SAtom.add a sa)
  ) sa_evts (acc, SAtom.empty) in

  let sa = SAtom.union sa_pure (SAtom.union sa_evts sa_new) in
  
  let ord = List.fold_left (fun ord p ->
    let pord = try HMap.find p ord with Not_found -> [] in
    HMap.add p (Elem (hF, Glob) :: pord) ord
  ) ord fce in

  HMap.fold (fun p tl ->
    SAtom.add (Atom.Comp (Access (hO, [p]), Eq, List tl))) ord sa
 *)



let all_events sa =
  let is_write = function Write _ -> true | _ -> false in
  let is_read = function Read _ -> true | _ -> false in
  SAtom.fold (fun a (srt, swt) -> match a with
    | Atom.Comp (t1, _, t2) ->
       let srt = if is_read t1 then STerm.add t1 srt else srt in
       let srt = if is_read t2 then STerm.add t2 srt else srt in
       let swt = if is_write t1 then STerm.add t1 swt else swt in
       let swt = if is_write t2 then STerm.add t2 swt else swt in
       srt, swt
    | _ -> srt, swt
  ) sa (STerm.empty, STerm.empty)

let remove_none = SAtom.filter (function
  | Atom.Comp (Elem (n, Glob), _, _) | Atom.Comp (_, _, Elem (n, Glob))
       when Hstring.equal n hNone -> false
  | _ -> true)

let event_subst t te sa =
  SAtom.fold (fun a sa -> match a with
    | Atom.Comp (t1, op, t2) ->
       let t1 = if Term.compare t1 t = 0 then te else t1 in
       let t2 = if Term.compare t2 t = 0 then te else t2 in
       SAtom.add (Atom.Comp (t1, op, t2)) sa
    | _ -> SAtom.add a sa
  ) sa SAtom.empty

let events_of_satom sa =
  let sa_pure, sa_evts, fce, ord, cnt = split_events_orders sa in
  let srt, swt = all_events sa_evts in
  let sa_evts = remove_none sa_evts in
  
  let (acc, sa_evts) = STerm.fold (fun t (acc, sa) -> match t with
    | Write (p, v, vi) ->
       let acc, te = make_event acc hW p v vi in
       let sa = event_subst t te sa in
       (acc, sa)
    | _ -> assert false
  ) swt ((cnt, ord, SAtom.empty), sa_evts) in

  let ((_, ord, sa_new), sa_evts) = STerm.fold (fun t (acc, sa) -> match t with
    | Read (p, v, vi) ->
       let acc, te = make_event acc hR p v vi in
       let sa = event_subst t te sa in
       (acc, sa)
    | _ -> assert false
  ) srt (acc, sa_evts) in

  let sa = SAtom.union sa_pure (SAtom.union sa_evts sa_new) in

  let ord = List.fold_left (fun ord p ->
    let pord = try HMap.find p ord with Not_found -> [] in
    HMap.add p (Elem (hF, Glob) :: pord) ord
  ) ord fce in

  HMap.fold (fun p tl ->
    SAtom.add (Atom.Comp (Access (hO, [p]), Eq, List tl))) ord sa



let split_event_order (sa, evts, ord) at = match at with
  | Atom.Comp (Access (a, [p]), Eq, List tl)
  | Atom.Comp (List tl, Eq, Access (a, [p])) when H.equal a hO ->
     let pord = List.map (fun t -> match t with
       | Elem (e, Glob) -> e
       | _ -> failwith "Weakmem.split_event_order error"
     ) tl in
     (sa, evts, HMap.add p pord ord)
  | Atom.Comp (Field (Access (a,[p;e]),f), Eq, Elem (c,t))
  | Atom.Comp (Elem (c,t), Eq, Field (Access (a,[p;e]),f)) when H.equal a hE ->
     let pevts = try HMap.find p evts with Not_found -> HMap.empty in
     let (d, v, vi) = try HMap.find e pevts
		      with Not_found -> (hNone, hNone, []) in
     let d = if f = hDir then c else d in
     let v = if f = hVar then c else v in
     let vi = if List.exists (fun (p, _) -> H.equal f p) !pl
	      then (f, c) :: vi else vi in 
     (SAtom.add at sa, HMap.add p (HMap.add e (d, v, vi) pevts) evts, ord)
  | _ -> (SAtom.add at sa, evts, ord)

let sort_event_params =
  HMap.map (HMap.map (fun (d, v, vi) ->
    (d, v, List.sort (fun (p1, _) (p2, _) -> H.compare p1 p2) vi)
  ))

let split_events_orders_array ar =
  let sa, evts, ord = Array.fold_left (fun acc a ->
    split_event_order acc a) (SAtom.empty, HMap.empty, HMap.empty) ar in
  sa, sort_event_params evts, ord

let split_events_orders_set sa =
  let sa, evts, ord = SAtom.fold (fun a acc ->
    split_event_order acc a) sa (SAtom.empty, HMap.empty, HMap.empty) in
  sa, sort_event_params evts, ord



let merge_ord sord dord =
  HMap.fold (fun p spord dord ->
    let dpord = try HMap.find p dord with Not_found -> [] in
    HMap.add p (spord @ dpord) dord
  ) sord dord

let merge_evts sevts devts =
  HMap.fold (fun p spevts devts ->
    let dpevts = try HMap.find p devts with Not_found -> HMap.empty in
    HMap.add p (HMap.fold HMap.add spevts dpevts) devts
  ) sevts devts


		
let rec hpl_equal hpl1 hpl2 = match hpl1, hpl2 with
  | [], [] -> true
  | [], _ | _, [] -> false
  | (hl1, hr1) :: hpl1, (hl2, hr2) :: hpl2 ->
     if H.equal hl1 hl2 && H.equal hr1 hr2 then hpl_equal hpl1 hpl2
     else false


  
let gen_po ord =
  let rec aux p po = function
    | [] | [_] -> po
    | f :: pord when H.equal f hF -> aux p po pord
    | e :: f :: pord when H.equal f hF -> aux p po (e :: pord)
    | e1 :: pord ->
       let po = List.fold_left (fun po e2 ->
         if H.equal e2 hF then po else
	 (p, e1, p, e2) :: po
       ) po pord in
       aux p po pord
  in
  HMap.fold (fun p pord po -> aux p po pord) ord []

let gen_po_loc evts ord =
  let rec aux p po pevts = function
    | [] | [_] -> po
    | f :: pord when H.equal f hF -> aux p po pevts pord
    | e :: f :: pord when H.equal f hF -> aux p po pevts (e :: pord)
    | e1 :: pord ->
       let (_, v1, pl1) = HMap.find e1 pevts in
       let po = List.fold_left (fun po e2 ->
         if H.equal e2 hF then po else
       	   let (_, v2, pl2) = HMap.find e2 pevts in
       	   if not (H.equal v1 v2 && hpl_equal pl1 pl2) then po else
       	     (p, e1, p, e2) :: po
       ) po pord in
       (* let po = try let e2 = List.find (fun e2 -> *)
       (*     if H.equal e2 hF then false else *)
       (* 	     let (_, v2, pl2) = HMap.find e2 pevts in *)
       (* 	     H.equal v1 v2 && hpl_equal pl1 pl2 *)
       (* 	   ) pord in (p, e1, p, e2) :: po *)
       (*   with Not_found -> po in *)
       aux p po pevts pord
  in
  HMap.fold (fun p pord po -> aux p po (HMap.find p evts) pord) ord []

let gen_ppo_tso evts ord =
  let rec aux p po pevts = function
    | [] | [_] -> po
    | f :: pord when H.equal f hF -> aux p po pevts pord
    | e :: f :: pord when H.equal f hF -> aux p po pevts (e :: pord)
    | e1 :: pord ->
       let (d1, _, _) = HMap.find e1 pevts in
       let po = List.fold_left (fun po e2 ->
         if H.equal e2 hF then po else
       	   let (d2, _, _) = HMap.find e2 pevts in
       	   if H.equal d1 hW && H.equal d2 hR then po else
       	     (p, e1, p, e2) :: po
       ) po pord in
       (* let po = try let e2 = List.find (fun e2 -> *)
       (*     if H.equal e2 hF then false else *)
       (* 	     let (d2, _, _) = HMap.find e2 pevts in *)
       (* 	     not (H.equal d1 hW && H.equal d2 hR) *)
       (* 	   ) pord in (p, e1, p, e2) :: po *)
       (* 	 with Not_found -> po in *)
       aux p po pevts pord
  in
  HMap.fold (fun p pord po -> aux p po (HMap.find p evts) pord) ord []

let gen_fence evts ord =
  let rec split_at_first_fence lpord = function
    | [] -> lpord, []
    | f :: rpord when H.equal f hF -> lpord, rpord
    | e :: rpord -> split_at_first_fence (e :: lpord) rpord
  in
  let rec first_event dir p = function
    | [] -> None
    | e :: pord ->
       let pevts = HMap.find p evts in
       let (d, _, _) = HMap.find e pevts in
       if H.equal d dir then Some e else first_event dir p pord
  in
  let rec aux p fence lpord rpord = match rpord with
    | [] -> fence
    | _ ->
       let lpord, rpord = split_at_first_fence lpord rpord in
       match first_event hW p lpord, first_event hR p rpord with
       | Some w, Some r -> aux p ((p, w, p, r) :: fence) lpord rpord
       | _, _ -> aux p fence lpord rpord
  in
  HMap.fold (fun p pord fence -> aux p fence [] pord) ord []

let rec co_from_pord co p pwrites = function
  | [] -> co
  | e1 :: pord -> begin try
      let (_, v1, pl1) = HMap.find e1 pwrites in
      let co = List.fold_left (fun co e2 ->
	try let (_, v2, pl2) = HMap.find e2 pwrites in
	  if H.equal v1 v2 && hpl_equal pl1 pl2
	  then (p, e1, p, e2) :: co else co
	with Not_found -> co
      ) co pord in
      co_from_pord co p pwrites pord
    with Not_found -> co_from_pord co p pwrites pord end

let gen_co evts ord =
  let writes = HMap.map (HMap.filter (fun e (d, _, _) -> H.equal d hW)) evts in
  let iwrites, writes = HMap.partition (fun p _ -> H.equal p hP0) writes in
  (* Initial writes *)
  let co = HMap.fold (fun p1 -> HMap.fold (fun e1 (_, v1, pl1) co ->
    HMap.fold (fun p2 -> HMap.fold (fun e2 (_, v2, pl2) co ->
      if H.equal v1 v2 && hpl_equal pl1 pl2
      then (p1, e1, p2, e2) :: co else co
    )) writes co
  )) iwrites [] in
  (* Writes from same thread *)
  HMap.fold (fun p pord co ->
    try co_from_pord co p (HMap.find p writes) pord
    with Not_found -> co
  ) ord co

let gen_co_cands evts =
  let rec aux evts cco =
    try
      let (p1, p1evts) = HMap.choose evts in
      let evts = HMap.remove p1 evts in
      let cco = HMap.fold (fun e1 (d1, v1, pl1) cco ->
        HMap.fold (fun p2 p2evts cco ->
          HMap.fold (fun e2 (d2, v2, pl2) cco ->
	    if H.equal d1 hW && H.equal d2 hW &&
		 H.equal v1 v2 && hpl_equal pl1 pl2 then
	      [ (p1, e1, p2, e2) ; (p2, e2, p1, e1) ] :: cco     
	    else cco
	  ) p2evts cco
        ) evts cco
      ) p1evts cco in
      aux evts cco
    with Not_found -> cco
  in
  aux (HMap.remove hP0 evts) []
  
let gen_rf_cands evts = (* exclude trivially false rf (use value/const) *)
  let reads, writes = HMap.fold (fun p pe (r, w) ->
    let pr, pw = HMap.partition (fun e (d, v, pl) -> H.equal d hR) pe in
    (HMap.add p pr r, HMap.add p pw w)
  ) evts (HMap.empty, HMap.empty) in
  HMap.fold (fun p1 -> HMap.fold (fun e1 (d1, v1, pl1) crf ->
    let ecrf = HMap.fold (fun p2 -> HMap.fold (fun e2 (d2, v2, pl2) ecrf ->
      if not (H.equal v1 v2 && hpl_equal pl1 pl2) then ecrf
      else (p2, e2, p1, e1) :: ecrf
    )) writes [] in
    if ecrf = [] then crf else ecrf :: crf
  )) reads []



let make_rel r (p1, e1, p2, e2) =
  let p1, p2 = T.make_app p1 [], T.make_app p2 [] in
  let e1, e2 = T.make_app e1 [], T.make_app e2 [] in
  F.make_lit F.Le [ T.make_app r [p1; e1] ; T.make_app r [p2; e2] ]

let make_rell r el f =
  List.fold_left (fun f e -> make_rel r e :: f) f el

let make_pred p (p1, e1, p2, e2) b =
  let p1, p2 = T.make_app p1 [], T.make_app p2 [] in
  let e1, e2 = T.make_app e1 [], T.make_app e2 [] in
  let tb = if b then T.t_true else T.t_false in
  F.make_lit F.Eq [ T.make_app p [p1; e1; p2; e2] ; tb ]

let make_predl p el f =
  List.fold_left (fun f e -> make_pred p e true :: f) f el

let make_predl_dl p ell f =
  List.fold_left (fun f el -> (F.make F.Or (make_predl p el [])) :: f) f ell


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

let make_orders_fp evts ord =
  let f = [] in
  let f = make_predl hPo (gen_po ord) f in
  let f = make_predl hFence (gen_fence evts ord) f in
  f

let make_orders_sat evts ord =
  let f = [] in

  (* let f = make_predl hPo (gen_po ord) f in *)
    let f = make_predl hPoLocUCom (gen_po_loc evts ord) f in
    let f = make_predl hCoUProp (gen_ppo_tso evts ord) f in
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
  
  let f = make_predl_dl hRf (gen_rf_cands evts) f in (*no value test*)
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



(*
let print_var fmt (v, vi) =
  if vi = [] then fprintf fmt "\\texttt{%a}" H.print v
  else fprintf fmt "\\texttt{%a}[%a]"
 	       H.print v (H.print_list ", ") vi

let print fmt { uid; tid; dir; var } =
  let dir = if dir = ERead then "R" else "W" in
  fprintf fmt "event(%d, %a, %s, %a)" uid H.print tid dir print_var var

let print_rd fmt (p, v, vi) =
  fprintf fmt "read(%a, %a)" H.print p print_var (v, vi)

let rec perm_all sevents devents spof dpof cnt perms cp =
  if IntMap.is_empty spof then cp :: perms else begin
    let tid, stpof = IntMap.choose spof in
    let dtpof = try IntMap.find tid dpof with Not_found -> [] in
    let spof = IntMap.remove tid spof in
    let dpof = IntMap.remove tid dpof in
    perm_thread sevents devents spof dpof stpof dtpof cnt perms cp
  end  

and perm_thread sevents devents spof dpof stpof dtpof cnt perms cp =
  match stpof, dtpof with
  | 0 :: stpof, dtpof ->
     perm_thread sevents devents spof dpof stpof dtpof cnt perms cp
  | seid :: stpof, dtpof ->
     let se = IntMap.find seid sevents in
     let perms = perm_list sevents devents spof dpof stpof dtpof
			   seid se cnt perms cp in
     perms
     (* Allow extra event ids *)
     (*perm_thread sevents devents spof dpof stpof []
		 (cnt+1) perms ((seid, cnt) :: cp)*)
  | [], ((_ :: _) as dtpof) ->
     if List.exists (fun deid -> deid <> 0) dtpof then [] else perms
  | [], [] ->
     perm_all sevents devents spof dpof cnt perms cp

and perm_list sevents devents spof dpof stpof dtpof seid se cnt perms cp =
  match dtpof with
  | [] -> perms
  | deid :: dtpof ->
     let perms =
       if deid = 0 then perms else
       let de = IntMap.find deid devents in
       if se.dir = de.dir && se.var = de.var then
         perm_thread sevents devents spof dpof stpof dtpof
        	     cnt perms ((seid, deid) :: cp)
       else perms in
     perm_list sevents devents spof dpof stpof dtpof seid se cnt perms cp

                                 (* source will be subst *)
let es_permutations s_es d_es = (* source = visited, dest = current node *)
  let sc = IntMap.cardinal s_es.events in
  let dc = IntMap.cardinal d_es.events in
  if sc < dc then [] else begin
    perm_all s_es.events d_es.events s_es.po_f d_es.po_f (dc+1) [] []
  end
    
let es_apply_subst s es =
  let events = IntMap.fold (fun uid e events ->
    let uid = try List.assoc uid s with Not_found -> uid in
    IntMap.add uid { e with uid } events			    
  ) es.events IntMap.empty in
  let po_f = IntMap.fold (fun tid tpof pof ->
    let tpof = List.map (fun uid ->
      try List.assoc uid s with Not_found -> uid
    ) tpof in
    IntMap.add tid tpof pof		  
  ) es.po_f IntMap.empty in
  { events; po_f }

 *)
