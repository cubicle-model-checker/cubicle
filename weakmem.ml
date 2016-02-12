
open Types

module H = Hstring
module HMap = Hstring.HMap
module T = Smt.Term
module F = Smt.Formula



let init_weak_env wvl =
  if Options.model <> Options.SC then begin
    Smt.Type.declare (Hstring.make "_direction")
	[ Hstring.make "_R" ; Hstring.make "_W" ];
    Smt.Type.declare (Hstring.make "_weak_var")
        (List.map (fun wv -> Hstring.make ("_V" ^ (Hstring.view wv))) wvl);
    Smt.Type.declare_record (Hstring.make "_event")
        [ (Hstring.make "_dir", Hstring.make "_direction") ;
	  (Hstring.make "_var", Hstring.make "_weak_var") ;
	  (Hstring.make "_val", Hstring.make "int") ];
    Smt.Symbol.declare (Hstring.make ("_e"))
        [ Smt.Type.type_proc ; Smt.Type.type_int ] (Hstring.make "_event");
    for i = 1 to 20 do
      Smt.Symbol.declare (Hstring.make ("_e" ^ (string_of_int i)))
	[] Smt.Type.type_int
    done
  end



let make_event (ec, eo, na) d p v vi = 
  let eid = (try HMap.find p ec with Not_found -> 0) + 1 in
  let pord = try HMap.find p eo with Not_found -> [] in
  let e = Hstring.make ("_e" ^ (string_of_int eid)) in
  let tevt = Access (Hstring.make "_e", [p ; e]) in
  let tdir = Field (tevt, Hstring.make "_dir") in
  let tvar = Field (tevt, Hstring.make "_var") in
  let tval = Field (tevt, Hstring.make "_val") in
  let adir = Atom.Comp (tdir, Eq, Elem (Hstring.make d, Constr)) in
  let avar = Atom.Comp (tvar, Eq, Elem
			(Hstring.make ("_V" ^ (Hstring.view v)), Constr)) in
  let ec = HMap.add p eid ec in
  let eo = HMap.add p (Elem (e, Glob) :: pord) eo in
  let na = adir :: avar :: na in
  (ec, eo, na), tval

let event_of_term acc = function
  | Elem (v, Glob) when Smt.Symbol.is_weak v ->
      make_event acc "_W" (Hstring.make "#0") v []
  | Access (v, vi) when Smt.Symbol.is_weak v ->
      make_event acc "_W" (Hstring.make "#0") v vi
  | Read (p, v, vi) ->
     make_event acc "_R" p v vi
  | t -> acc, t

let events_of_a acc = function
  | Atom.Comp (t1, op, t2) ->
     let acc, t1 = event_of_term acc t1 in
     let acc, t2 = event_of_term acc t2 in
     acc, Atom.Comp (t1, op, t2)
  | a -> acc, a

let events_of_satom sa =
  let ((ec, eo, na), sa) = SAtom.fold (fun a (acc, sa) ->
    let acc, a = events_of_a acc a in
    (acc, SAtom.add a sa)
  ) sa ((HMap.empty, HMap.empty, []), SAtom.empty) in
  let sa = List.fold_left (fun sa a -> SAtom.add a sa) sa na in
  HMap.fold (fun p tl sa ->
    let a = Atom.Comp (Access ((Hstring.make "_o"), [p]), Eq, List tl) in
    SAtom.add a sa) eo sa



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



let split_order a =
  let ho = Hstring.make "_o" in
  match a with
  | Atom.Comp (List tl, Eq, Access (a, [p]))
  | Atom.Comp (Access (a, [p]), Eq, List tl) when a = ho ->
     let ord = List.map (fun t -> match t with
       | Elem (e, Glob) -> e
       | _ -> failwith "Prover.split_order error"
     ) tl in
     (None, Some (p, ord))
  | _ -> (Some a, None)

let split_order_array ar =
  Array.fold_left (fun (sa, ord) a -> match split_order a with
    | None, Some (p, o) -> (sa, HMap.add p o ord)
    | Some a, None -> (SAtom.add a sa, ord)
    | _, _ -> failwith "Prover.split_order_array error"
  ) (SAtom.empty, HMap.empty) ar

let split_order_set sa =
  SAtom.fold (fun a (sa, ord) -> match split_order a with
    | None, Some (p, o) -> (sa, HMap.add p o ord)
    | Some a, None -> (SAtom.add a sa, ord)
    | _, _ -> failwith "Prover.split_order_set error"
  ) sa (SAtom.empty, HMap.empty)



let get_events sa =
  let none = Hstring.make "" in
  let he = Hstring.make "_e" in
  let hdir = Hstring.make "_dir" in
  let hvar = Hstring.make "_var" in
  SAtom.fold (fun a evts -> match a with
    | Atom.Comp (Field (Access (a, [p ; e]), f), Eq, Elem (c, t))
    | Atom.Comp (Elem (c, t), Eq, Field (Access (a, [p ; e]), f)) when a = he ->
       let pevts = try HMap.find p evts with Not_found -> HMap.empty in
       let (d, v) = try HMap.find e pevts with Not_found -> (none, none) in
       let d = if f = hdir then c else d in
       let v = if f = hvar then c else v in
       HMap.add p (HMap.add e (d, v) pevts) evts
    | _ -> evts
  ) sa HMap.empty		      


		
let gen_po ord =
  let hf = Hstring.make "_f" in
  let rec aux p po = function
    | [] | [_] -> po
    | f :: pord when f = hf -> aux p po pord
    | e :: f :: pord when f = hf -> aux p po (e :: pord)
    | e1 :: ((e2 :: _) as pord) -> aux p ((p, e1, p, e2) :: po) pord
  in
  HMap.fold (fun p pord po -> aux p po pord) ord []

let gen_fence evts ord =
  let hf = Hstring.make "_f" in
  let hW = Hstring.make "_W" in
  let hR = Hstring.make "_R" in
  let rec split_at_first_fence lpord = function
    | [] -> lpord, []
    | f :: rpord when f = hf -> lpord, rpord
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
  let hW = Hstring.make "_W" in
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
  let p0 = Hstring.make "#0" in
  let hW = Hstring.make "_W" in
  let writes = HMap.map (HMap.filter (fun e (d, _) -> d = hW)) evts in
  let iwrites, writes = HMap.partition (fun p _ -> p = p0) writes in
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
  let p0 = Hstring.make "#0" in
  let hW = Hstring.make "_W" in
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
  aux (HMap.remove p0 evts) []
  
let gen_rf_cands evts =
  let hR = Hstring.make "_R" in
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
  let p1 = Hstring.view p1 in
  let p2 = Hstring.view p2 in
  let e1 = Hstring.view e1 in
  let e2 = Hstring.view e2 in
  let tb = if b then T.t_true else T.t_false in
  F.make_lit F.Eq [ T.mk_pred p [p1;e1;p2;e2] ; tb ]

let make_acyclic_rel (p, e) =
  [ make_pred "_po_loc_U_com" (p,e,p,e) false ;
    make_pred "_co_U_prop" (p,e,p,e) false ]

let make_rel rel pl =
  List.fold_left (fun f p -> make_pred rel p true :: f) [] pl

let make_cands rel cands =
  List.fold_left (fun ff pl -> (F.make F.Or (make_rel rel pl)) :: ff) [] cands

let make_orders ?(fp=false)evts ord =
  let f = [F.f_true] in
  let f = (make_rel "_po" (gen_po ord)) @ f in
  let f = (make_rel "_fence" (gen_fence evts ord)) @ f in
  let f = (make_rel "_co" (gen_co evts ord)) @ f in
  let f = (make_cands "_rf" (gen_rf_cands evts)) @ f in
  let f = (make_cands "_co" (gen_co_cands evts)) @ f in
  if fp then F.make F.And f else
  let el = HMap.fold (fun p -> HMap.fold (fun e _ el -> (p,e) :: el)) evts [] in
  let f = List.fold_left (fun f e -> (make_acyclic_rel e) @ f) f el in
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
