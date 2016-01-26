
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

let axiom_base = "
type direction = _R | _W
type event = { tid : int; dir : direction; loc : tso_var; val : int }
logic e : int -> event
logic po : int, int -> prop
logic rf : int, int -> prop
logic co : int, int -> prop
logic fence : int, int -> prop
"
let axiom_rels = "
axiom rf :
  forall e1, e2 : int [rf(e1,e2)].
  rf(e1, e2) -> e(e1).val = e(e2).val
logic po_loc : int, int -> prop
axiom po_loc :
  forall e1, e2 : int [po(e1,e2)].
  po(e1, e2) and e(e1).loc = e(e2).loc
  <-> po_loc(e1, e2)
logic rfe : int, int -> prop
axiom rfe :
  forall e1, e2 : int [rf(e1,e2)].
  rf(e1, e2) and e(e1).tid <> e(e2).tid
  <-> rfe(e1, e2)
logic fr : int, int -> prop
axiom fr :
  forall r, w1, w2 : int [rf(w1,r),co(w1,w2)].
  rf(w1, r) and co(w1, w2)
  -> fr(r, w2)
logic com : int, int -> prop
axiom com :
  forall e1, e2 : int [co(e1,e2)|rf(e1,e2)|fr(e1,e2)].
  co(e1, e2) or rf(e1, e2) or fr(e1, e2)
  <-> com(e1, e2)
logic ppo : int, int -> prop
axiom ppo_tso :
  forall e1, e2 : int [po(e1,e2)].
  po(e1, e2) and not (e(e1).dir = _W and e(e2).dir = _R)
  <-> ppo(e1, e2)
logic propg : int, int -> prop
axiom propg_tso :
  forall e1, e2 : int [ppo(e1,e2)|fence(e1,e2)|rfe(e1,e2)|fr(e1,e2)].
  ppo(e1, e2) or fence(e1, e2) or rfe(e1, e2) or fr(e1, e2)
  <-> propg(e1, e2)
logic po_loc_U_com : int, int -> prop
axiom po_loc_U_com :
  forall e1, e2 : int [(*po_loc(e1,e2)|com(e1,e2)|*)po_loc_U_com(e1,e2)].
  po_loc(e1, e2) or com(e1, e2) -> po_loc_U_com(e1, e2)
axiom po_loc_U_com_t :
  forall e1, e2, e3 : int [po_loc_U_com(e1,e2),po_loc_U_com(e2,e3)].
  po_loc_U_com(e1, e2) and po_loc_U_com(e2, e3) -> po_loc_U_com(e1, e3)
logic co_U_prop : int, int -> prop
axiom co_U_prop :
  forall e1, e2 : int [co(e1,e2)|propg(e1,e2)(*|co_U_prop(e1,e2)*)].
  co(e1, e2) or propg(e1, e2) -> co_U_prop(e1, e2)
axiom co_U_prop_t :
  forall e1, e2, e3 : int [co_U_prop(e1,e2),co_U_prop(e2,e3)].
  co_U_prop(e1, e2) and co_U_prop(e2, e3) -> co_U_prop(e1, e3)
"


let replace str s1 s2 =
  Str.global_replace (Str.regexp_string s1) s2 str

let print_var_name fmt v =
  fprintf fmt "_V%s" (replace (Hstring.view v) "#" "p")

let unique_events esl =
  let uel = ref [] in
  List.iter (fun es -> IntMap.iter (fun _ e ->
    if not (List.exists (fun ex -> ex.uid = e.uid) !uel) then uel := e :: !uel
  ) es.events) esl;
  !uel

let print_hset_sep sep pfun fmt set =
  let first = ref true in
  Hstring.H.iter (fun k v ->
    if !first then begin pfun fmt (k, v); first := false end
    else fprintf fmt " %s %a" sep pfun (k, v)) set

let print_decls fmt fp tso_vars esl =
  if Hstring.H.length tso_vars > 0 then begin

    (* Additional proc #0 for initial events *)
    fprintf fmt "\nlogic p0 : int\n";
    fprintf fmt "axiom p0 : p0 <> p1 <> p2 <> p3 <> p4 <> p5";
    fprintf fmt " <> p6 <> p7 <> p8 <> p9 <> p10\n\n";

    (* List of TSO variables *) (* could use their original names *)
    fprintf fmt "type tso_var = %a\n" (print_hset_sep "|"
      (fun fmt (f, (fx, args, ret)) -> print_var_name fmt f)) tso_vars;

    (* Axiomatization *)
    fprintf fmt "%s" axiom_base;
    if not fp then fprintf fmt "%s" axiom_rels;
    fprintf fmt "\n";

    (* Declaration of events *)
    List.iter (fun e ->
      fprintf fmt "logic %s : int\n" (name e)
    ) (List.rev (unique_events esl));
    fprintf fmt "\n";

  end

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
    | eid1 :: ((eid2 :: _) as tpof) -> aux ((eid1, eid2) :: po) tpof
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
       | Some w, Some r -> aux ((w, r) :: fence) ltpof rtpof (*should make lst*)
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
	  | Some e2 -> if e1.var = e2.var then (eid1, eid2) :: co else co
	) co tpof in
	co_from_tpof es co tpof

let gen_co es =
  let writes = IntMap.filter (fun _ e -> e.dir = EWrite) es.events in
  let iwrites, writes = IntMap.partition (fun _ e ->
    Hstring.view e.tid = "#0") writes in
  let co = IntMap.fold (fun eid1 e1 co -> (* Initial writes *)
    IntMap.fold (fun eid2 e2 co ->
      if e1.var = e2.var then (eid1, eid2) :: co else co
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
		else [ (eid1, eid2) ; (eid2, eid1) ] :: cco
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
      else (eid2, eid1) :: ecrf
    ) writes [] in
    if ecrf = [] then crf else ecrf :: crf
  ) reads []
