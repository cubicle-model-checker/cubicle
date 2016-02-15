
open Types

module H = Hstring
module HMap = Hstring.HMap
module T = Smt.Term
module S = Smt.Symbol
module F = Smt.Formula



let hNone = Hstring.make ""
let hP0 = Hstring.make "#0"
let hDirection = Hstring.make "_direction"
let hR = Hstring.make "_R"
let hW = Hstring.make "_W"
let hEvent = Hstring.make "_event"
let hDir = Hstring.make "_dir"
let hVal = Hstring.make "_val"
let hVar = Hstring.make "_var"
let hWeakVar = Hstring.make "_weak_var"
let hO = Hstring.make "_o"
let hF = Hstring.make "_f"
let hE = Hstring.make "_e"
let hInt = Hstring.make "int"
let hProp = Hstring.make "prop"
let hPo = Hstring.make "_po"
let hRf = Hstring.make "_rf"
let hCo = Hstring.make "_co"
let hFence = Hstring.make "_fence"
let hCoUProp = Hstring.make "_co_U_prop"
let hPoLocUCom = Hstring.make "_po_loc_U_com"
let mk_hE i = Hstring.make ("_e" ^ (string_of_int i))
let mk_hV hv = Hstring.make ("_V" ^ (Hstring.view hv))



let init_weak_env wvl =
  Smt.Type.declare hDirection [ hR ; hW ];
  Smt.Type.declare hWeakVar (List.map (mk_hV) wvl);
  Smt.Type.declare_record hEvent [(hDir, hDirection); (hVar, hWeakVar); (hVal, hInt)];
  Smt.Symbol.declare hE [ Smt.Type.type_proc ; Smt.Type.type_int ] hEvent;
  for i = 1 to 20 do
    Smt.Symbol.declare (mk_hE i) [] Smt.Type.type_int
  done;
  let int4 = [ Smt.Type.type_int; Smt.Type.type_int;
	       Smt.Type.type_int; Smt.Type.type_int ] in
  Smt.Symbol.declare hPo int4 Smt.Type.type_prop;
  Smt.Symbol.declare hRf int4 Smt.Type.type_prop;
  Smt.Symbol.declare hCo int4 Smt.Type.type_prop;
  Smt.Symbol.declare hFence int4 Smt.Type.type_prop;
  Smt.Symbol.declare hCoUProp int4 Smt.Type.type_prop;
  Smt.Symbol.declare hPoLocUCom int4 Smt.Type.type_prop



let writes_of_init init =
  let aux = function
  | Elem (v, Glob) when Smt.Symbol.is_weak v -> Write (hP0, v, [])
  | Access (v, vi) when Smt.Symbol.is_weak v -> Write (hP0, v, vi)
  | t -> t in
  List.map (fun sa -> SAtom.fold (fun a sa ->
    let a = match a with
    | Atom.Comp (t1, op, t2) -> Atom.Comp (aux t1, op, aux t2)
    | _ -> a in
    SAtom.add a sa
  ) sa SAtom.empty) init



let split_events_orders sa =
  SAtom.fold (fun a (sa_pure, sa_evts, fce, ord, cnt) ->
    match a with
    | Atom.Comp (Access (a, [p]), Eq, List tl)
    | Atom.Comp (List tl, Eq, Access (a, [p])) when a = hO ->
       let c = List.fold_left (fun c t -> match t with
         | Elem (e, Glob) -> if e = hF then c else c + 1
	 | _ -> failwith "Weakmem.split_events_order error"
       ) 0 tl in
       (sa_pure, sa_evts, fce, HMap.add p tl ord, HMap.add p c cnt)
    | Atom.Comp (Write (p, v, vi), Eq, tv)
    | Atom.Comp (tv, Eq, Write (p, v, vi)) ->
       (sa_pure, SAtom.add a sa_evts, fce, ord, cnt)
    | Atom.Comp (Read (p, v, vi), Eq, tv)
    | Atom.Comp (tv, Eq, Read (p, v, vi)) ->
       (sa_pure, SAtom.add a sa_evts, fce, ord, cnt)
    | Atom.Comp (Fence p, Eq, tb)
    | Atom.Comp (tb, Eq, Fence p) ->
       (sa_pure, sa_evts, p :: fce, ord, cnt)
    | _ -> (SAtom.add a sa_pure, sa_evts, fce, ord, cnt)
) sa (SAtom.empty, SAtom.empty, [], HMap.empty, HMap.empty)



let make_event (cnt, ord, na) d p v vi = 
  let eid = (try HMap.find p cnt with Not_found -> 0) + 1 in
  let pord = try HMap.find p ord with Not_found -> [] in
  let e = mk_hE eid in
  let tevt = Access (hE, [p ; e]) in
  let adir = Atom.Comp (Field (tevt, hDir), Eq, Elem (d, Constr)) in
  let avar = Atom.Comp (Field (tevt, hVar), Eq, Elem (mk_hV v, Constr)) in
  let cnt = HMap.add p eid cnt in
  let ord = HMap.add p (Elem (e, Glob) :: pord) ord in
  let na = SAtom.add adir (SAtom.add avar na) in
  (cnt, ord, na), Field (tevt, hVal)

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



let split_event_order (sa, evts, ord) at = match at with
  | Atom.Comp (Access (a, [p]), Eq, List tl)
  | Atom.Comp (List tl, Eq, Access (a, [p])) when a = hO ->
     let pord = List.map (fun t -> match t with
       | Elem (e, Glob) -> e
       | _ -> failwith "Weakmem.split_event_order error"
     ) tl in
     (sa, evts, HMap.add p pord ord)
  | Atom.Comp (Field (Access (a, [p ; e]), f), Eq, Elem (c, t))
  | Atom.Comp (Elem (c, t), Eq, Field (Access (a, [p ; e]), f)) when a = hE ->
     let pevts = try HMap.find p evts with Not_found -> HMap.empty in
     let (d, v) = try HMap.find e pevts with Not_found -> (hNone, hNone) in
     let d = if f = hDir then c else d in
     let v = if f = hVar then c else v in
     (SAtom.add at sa, HMap.add p (HMap.add e (d, v) pevts) evts, ord)
  | _ -> (SAtom.add at sa, evts, ord)

let split_events_orders_array ar =
  Array.fold_left (fun acc a ->
    split_event_order acc a) (SAtom.empty, HMap.empty, HMap.empty) ar

let split_events_orders_set sa =
  SAtom.fold (fun a acc ->
    split_event_order acc a) sa (SAtom.empty, HMap.empty, HMap.empty)



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


		
let gen_po ord =
  let rec aux p po = function
    | [] | [_] -> po
    | f :: pord when f = hF -> aux p po pord
    | e :: f :: pord when f = hF -> aux p po (e :: pord)
    | e1 :: ((e2 :: _) as pord) -> aux p ((p, e1, p, e2) :: po) pord
  in
  HMap.fold (fun p pord po -> aux p po pord) ord []

let gen_fence evts ord =
  let rec split_at_first_fence lpord = function
    | [] -> lpord, []
    | f :: rpord when f = hF -> lpord, rpord
    | e :: rpord -> split_at_first_fence (e :: lpord) rpord
  in
  let rec first_event dir p = function
    | [] -> None
    | e :: pord ->
       let pevts = HMap.find p evts in
       let (d, _) = HMap.find e pevts in
       if d = dir then Some e else first_event dir p pord
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

let rec co_from_pord evts p pord co =
  let pevts = try HMap.find p evts with Not_found -> HMap.empty in
  let pwrites = HMap.filter (fun e (d, _) -> d = hW) pevts in
  let rec aux co = function
  | [] -> co
  | e1 :: pord -> begin try
      let (_, v1) = HMap.find e1 pwrites in
      let co = List.fold_left (fun co e2 ->
	try let (_, v2) = HMap.find e2 pwrites in
	  if v1 = v2 then (p, e1, p, e2) :: co else co		   
	with Not_found -> co
      ) co pord in
      aux co pord
    with Not_found -> aux co pord end
  in
  aux co pord

let gen_co evts ord =
  let writes = HMap.map (HMap.filter (fun e (d, _) -> d = hW)) evts in
  let iwrites, writes = HMap.partition (fun p _ -> p = hP0) writes in
  (* Initial writes *)
  let co = HMap.fold (fun p1 -> HMap.fold (fun e1 (_, v1) co ->
    HMap.fold (fun p2 -> HMap.fold (fun e2 (_, v2) co ->
      if v1 = v2 then (p1, e1, p2, e2) :: co else co
    )) writes co
  )) iwrites [] in
  (* Writes from same thread *)
  HMap.fold (fun p pord co ->
    co_from_pord evts p pord co
  ) ord co

let gen_co_cands evts =
  let rec aux evts cco =
    try
      let (p1, p1evts) = HMap.choose evts in
      let evts = HMap.remove p1 evts in
      let cco = HMap.fold (fun e1 (d1, v1) cco ->
        HMap.fold (fun p2 p2evts cco ->
          HMap.fold (fun e2 (d2, v2) cco ->
	    if d1 = hW && d2 = hW && v1 = v2 then
	      [ (p1, e1, p2, e2) ; (p2, e2, p1, e1) ] :: cco     
	    else cco
	  ) p2evts cco
        ) evts cco
      ) p1evts cco in
      aux evts cco
    with Not_found -> cco
  in
  aux (HMap.remove hP0 evts) []
  
let gen_rf_cands evts =
  let reads, writes = HMap.fold (fun p pe (r, w) ->
    let pr, pw = HMap.partition (fun e (d, v) -> d = hR) pe in
    (HMap.add p pr r, HMap.add p pw w)
  ) evts (HMap.empty, HMap.empty) in
  HMap.fold (fun p1 -> HMap.fold (fun e1 (d1, v1) crf ->
    let ecrf = HMap.fold (fun p2 -> HMap.fold (fun e2 (d2, v2) ecrf ->
      if v1 <> v2 then ecrf
      else (p2, e2, p1, e1) :: ecrf
    )) writes [] in
    if ecrf = [] then crf else ecrf :: crf
  )) reads []



let make_pred p (p1, e1, p2, e2) b =
  let p = Hstring.make p in
  let p1 = T.make_app p1 [] in
  let p2 = T.make_app p2 [] in
  let e1 = T.make_app e1 [] in
  let e2 = T.make_app e2 [] in
  let tb = if b then T.t_true else T.t_false in
  F.make_lit F.Eq [ T.make_app p [p1; e1; p2; e2] ; tb ]

let make_rel rel pl =
  List.fold_left (fun f p -> make_pred rel p true :: f) [] pl

let make_cands rel cands =
  List.fold_left (fun f pl -> (F.make F.Or (make_rel rel pl)) :: f) [] cands

let make_orders ?(fp=false) evts ord =
  let f = [ F.f_true ] in
  let f = (make_rel "_po" (gen_po ord)) @ f in
  let f = (make_rel "_fence" (gen_fence evts ord)) @ f in
  let f = (make_rel "_co" (gen_co evts ord)) @ f in
  let f = (make_cands "_rf" (gen_rf_cands evts)) @ f in
  let f = (make_cands "_co" (gen_co_cands evts)) @ f in
  if fp then F.make F.And f else
  let el = HMap.fold (fun p -> HMap.fold (fun e _ el -> (p, e) :: el)) evts [] in
  let f = List.fold_left (fun f (p, e) ->
    make_pred "_po_loc_U_com" (p, e, p, e) false ::
    make_pred "_co_U_prop" (p, e, p, e) false :: f
  ) f el in
  F.make F.And f



(*
let name e = "e" ^ (string_of_int e.uid)

let int_of_tid tid =
  let tid = Hstring.view tid in
  let tid = String.sub tid 1 ((String.length tid)-1) in
  int_of_string tid

let print_var fmt (v, vi) =
  if vi = [] then fprintf fmt "\\texttt{%a}" Hstring.print v
  else fprintf fmt "\\texttt{%a}[%a]"
 	       Hstring.print v (Hstring.print_list ", ") vi

let print fmt { uid; tid; dir; var } =
  let dir = if dir = ERead then "R" else "W" in
  fprintf fmt "event(%d, %a, %s, %a)" uid Hstring.print tid dir print_var var

let print_rd fmt (p, v, vi) =
  fprintf fmt "read(%a, %a)" Hstring.print p print_var (v, vi)

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

let es_add_events es el =
  let events = List.fold_left (fun events e ->
    IntMap.add e.uid e events
  ) es.events el in
  { es with events }

let es_add_events_full es el =
  let events, po_f = List.fold_left (fun (events, po_f) e ->
    let tid = int_of_tid e.tid in
    let tpo_f = try IntMap.find tid po_f with Not_found -> [] in
    let po_f = IntMap.add tid (e.uid :: tpo_f) po_f in
    let events = IntMap.add e.uid e events in
    (events, po_f)
  ) (es.events, es.po_f) el in
  { events; po_f }

let es_add_fences es tidl =
  let po_f = List.fold_left (fun po_f tid ->
    let tid = int_of_tid tid in
    let tpo_f = try IntMap.find tid po_f with Not_found -> [] in
    IntMap.add tid (0 :: tpo_f) po_f
  ) es.po_f tidl in
  { es with po_f }

let event_from_id es eid =
  try IntMap.find eid es.events
  with Not_found -> failwith "Event.event_from_id : unknown event id"

let write_from_id es eid =
  if eid = 0 then None
  else
    let e = event_from_id es eid in
    if e.dir = EWrite then Some e
    else None

let gen_po es =
  let rec aux po = function
    | [] | [_] -> po
    | 0 :: tpof -> aux po tpof
    | eid :: 0 :: tpof -> aux po (eid :: tpof)
    | eid1 :: ((eid2 :: _) as tpof) ->
       let e1 = event_from_id es eid1 in
       let e2 = event_from_id es eid2 in
       aux ((e1, e2) :: po) tpof
  in
  IntMap.fold (fun _ tpof po -> aux po tpof) es.po_f []

let gen_fence es =
  let rec split_at_first_fence ltpof = function
    | 0 :: rtpof | ([] as rtpof) -> ltpof, rtpof
    | eid :: rtpof -> split_at_first_fence (eid :: ltpof) rtpof
  in
  let rec first_event dir = function
    | [] -> None
    | eid :: tpof ->
       let e = event_from_id es eid in
       if e.dir = dir then Some eid else first_event dir tpof
  in
  let rec aux fence ltpof rtpof = match rtpof with
    | [] -> fence
    | _ ->
       let ltpof, rtpof = split_at_first_fence ltpof rtpof in
       match first_event EWrite ltpof, first_event ERead rtpof with
       | Some w, Some r ->
	  let we = event_from_id es w in
	  let re = event_from_id es r in
	  aux ((we, re) :: fence) ltpof rtpof (*should make lst*)
       | _, _ -> aux fence ltpof rtpof
  in
  IntMap.fold (fun _ tpof fence -> aux fence [] tpof) es.po_f []

let rec co_from_tpof es co = function
  | [] -> co
  | eid1 :: tpof ->
     match write_from_id es eid1 with
     | None -> co_from_tpof es co tpof
     | Some e1 ->
	let co = List.fold_left (fun co eid2 ->
	  match write_from_id es eid2 with
	  | None -> co
	  | Some e2 -> if e1.var = e2.var then (e1, e2) :: co else co
	) co tpof in
	co_from_tpof es co tpof

let gen_co es =
  let writes = IntMap.filter (fun _ e -> e.dir = EWrite) es.events in
  let iwrites, writes = IntMap.partition (fun _ e ->
    Hstring.view e.tid = "#0") writes in
  let co = IntMap.fold (fun eid1 e1 co -> (* Initial writes *)
    IntMap.fold (fun eid2 e2 co ->
      if e1.var = e2.var then (e1, e2) :: co else co
    ) writes co
  ) iwrites [] in
  IntMap.fold (fun tid tpof co -> (* Writes from same thread *)
    co_from_tpof es co tpof
  ) es.po_f co
			
let gen_co_cands es =
  let rec aux cco tpof1 pof =
    try
      let (tid2, tpof2) = IntMap.choose pof in
      let cco = List.fold_left (fun cco eid1 ->
        match write_from_id es eid1 with
        | None -> cco
        | Some e1 ->
           List.fold_left (fun cco eid2 ->
             match write_from_id es eid2 with
	     | None -> cco
	     | Some e2 ->
		if e1.var <> e2.var then cco
		else [ (e1, e2) ; (e2, e1) ] :: cco
	   ) cco tpof2
      ) cco tpof1 in
      aux cco tpof2 (IntMap.remove tid2 pof)
    with Not_found -> cco
  in
  try
    let (tid1, tpof1) = IntMap.choose es.po_f in
    aux [] tpof1 (IntMap.remove tid1 es.po_f)
  with Not_found -> []

let gen_rf_cands es =
  let reads, writes = IntMap.partition (fun _ e -> e.dir = ERead) es.events in
  IntMap.fold (fun eid1 e1 crf ->
    let ecrf = IntMap.fold (fun eid2 e2 ecrf ->
      if e1.var <> e2.var then ecrf
      else (e2, e1) :: ecrf
    ) writes [] in
    if ecrf = [] then crf else ecrf :: crf
  ) reads []
 *)
