
open Format

type dir = ERead | EWrite

type t = {
    uid : int;
    tid : Variable.t;
    dir : dir;
    var : Hstring.t * Variable.t list; }

module IntMap = Map.Make(struct type t = int let compare = compare end)

type structure = {
    events : t IntMap.t;
    po_f : int list IntMap.t; }

let empty_struct = { events = IntMap.empty; po_f = IntMap.empty }

let make uid tid dir var =
  { uid; tid; dir; var }

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
