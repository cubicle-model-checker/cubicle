
open Channels
open Types


       
module Int = struct
  type t = int
  let compare = Pervasives.compare
  let equal = (=)
  let hash i = i
end

module IntSet = Set.Make (Int)



type cop = CEq | CNeq | CLt | CLe | CGt | CGe

let cop_of_r_op r op =
  let open Types in
  match r, op with
  | _, Eq -> CEq
  | _, Neq -> CNeq
  | false, Lt -> CLt
  | false, Le -> CLe
  | true, Lt -> CGt
  | true, Le -> CGe

let string_of_cop = function
  | CEq -> "="
  | CNeq -> "<>"
  | CLt -> "<"
  | CGt -> ">"
  | CLe -> "<="
  | CGe -> ">="



let subs_const_from_term cs =
  let cs = Types.mult_const (-1) cs in
  function
  | Const c -> Const (Types.add_constants c cs)
  | Arith (t, c) -> Arith (t, Types.add_constants c cs)
  | t -> Arith (t, cs)



let find_ievent evts e =
  try HMap.find e evts with Not_found -> ((hNone, hNone, hNone, hNone), [])

let add_ievent evts e nvals =
  let (ed, vals) = find_ievent evts e in
  HMap.add e (ed, nvals @ vals) evts

let rec split_event_val = function
  | Access (f, [e]) when is_value f -> Some e, None
  | Arith (t, c) -> fst (split_event_val t), Some c
  | _ -> None, None

let process_event evts te cop tv =
  let e, c = split_event_val te in
  match e with
  | Some e ->
     let tv = match c with Some c -> subs_const_from_term c tv | _ -> tv in
     add_ievent evts e [(cop, tv)]
  | None -> evts



let rec has_recv = function
  | Arith (t, _) -> has_recv t
  | Recv _ -> true
  | _ -> false

let find_uevent evts dpqch =
  try HEvtMap.find dpqch evts with Not_found -> []

let add_uevent evts dpqch nvals =
  let vals = find_uevent evts dpqch in
  HEvtMap.add dpqch (nvals @ vals) evts

let rec split_recv = function
  | Recv (p, q, ch) -> Some (p, q, ch), None
  | Arith (t, c) -> fst (split_recv t), Some c (* assert (snd... = None) *)
  | _ -> None, None

let process_read rds tr cop tv =
  let r, c = split_recv tr in
  match r with
  | Some (p, q, ch) ->
     let tv = match c with Some c -> subs_const_from_term c tv | _ -> tv in
     add_uevent rds (hR, p, q, mk_hC ch) [(cop, tv)]
  | _ -> rds

let process_read_noval rds tr =
  match fst (split_recv tr) with
  | Some (p, q, ch) -> add_uevent rds (hR, p, q, mk_hC ch) []
  | _ -> rds



(* let update_eids eids p e = *)
(*   let peids = try HMap.find p eids with Not_found -> IntSet.empty in *)
(*   HMap.add p (IntSet.add (int_of_e e) peids) eids *)

let extract_event (sa_pure, rcs, sds, eids, evts) at = match at with
  (* Send (may have Recvs as value) *)
  | Atom.Comp (Send _, _, Send _) ->
     failwith "Chanevent.extract_events : can't have Send on both sides !"
  | Atom.Comp (Send (p, q, ch, _), _, t)
  | Atom.Comp (t, _, Send (p, q, ch, [])) ->
     let sds = add_uevent sds (hS, p, q, mk_hC ch) [t] in
     let rcs = process_read_noval rcs t in
     (sa_pure, rcs, sds, eids, evts)
  (* Recv (both sides may be Recv + can have instantiated recv as value) *)
  | Atom.Comp (t1, op, t2) when has_recv t1 || has_recv t2 ->
     let rcs = process_read rcs t1 (cop_of_r_op false op) t2 in
     let rcs = process_read rcs t2 (cop_of_r_op true op) t1 in
     let evts = process_event evts t1 (cop_of_r_op false op) t2 in
     let evts = process_event evts t2 (cop_of_r_op true op) t1 in
     (sa_pure, rcs, sds, eids, evts)
  (* Direction / Thread / Peer / Channel *)
  | Atom.Comp (Access (f, [e]), Eq, Elem (c, t))
  | Atom.Comp (Elem (c, t), Eq, Access (f, [e]))
       when is_event f && not (is_value f) ->
     let ((d, p, q, ch), vals) as evt = find_ievent evts e in
     let evt = if H.equal f hDir then ((c, p, q, ch), vals)
          else if H.equal f hThr then ((d, c, q, ch), vals)
	  else if H.equal f hPeer then ((d, p, c, ch), vals)
	  else if H.equal f hChan then ((d, p, q, c), vals)
          else evt in
     (* let eids = if H.equal f hThr then update_eids eids c e else eids in *)
     (SAtom.add at sa_pure, rcs, sds, eids, HMap.add e evt evts)
  (* Value *)
  | Atom.Comp (t1, op, t2) ->
     let evts = process_event evts t1 (cop_of_r_op false op) t2 in
     let evts = process_event evts t2 (cop_of_r_op true op) t1 in
     (SAtom.add at sa_pure, rcs, sds, eids, evts)
  | Atom.Ite _ ->
     failwith "Chanevent.extract_events : Ite should not be there"
  | _ -> (SAtom.add at sa_pure, rcs, sds, eids, evts)


let init_acc =
  (SAtom.empty, HEvtMap.empty, HEvtMap.empty, HMap.empty, HMap.empty)

let post_process (sa_pure, rcs, sds, eids, evts) = (* eids always empty *)
  let eids = HMap.fold (fun e ((p, _, _, _), _) eids ->
    let peids = try HMap.find p eids with Not_found -> IntSet.empty in
    HMap.add p (IntSet.add (int_of_e e) peids) eids
  ) evts HMap.empty in
  sa_pure, rcs, sds, eids, evts (* should be sorted already *)

let extract_events_array ar =
  post_process (Array.fold_left (fun acc a -> extract_event acc a) init_acc ar)

let extract_events_set sa =
  post_process (SAtom.fold (fun a acc -> extract_event acc a) sa init_acc)

let extract_events_list la =
  post_process (List.fold_left (fun acc a -> extract_event acc a) init_acc la)

let send_events evts =
  HMap.filter (fun _ (ed, _) -> is_send ed) evts

let unsat_recv_events evts =
  HMap.filter (fun _ (ed, vals) -> is_recv ed && vals <> []) evts

let sat_events evts =
  HMap.filter (fun _ (_, vals) -> vals = []) evts

let events_by_thread evts = (* by chance, this sorts event in correct order *)
  HMap.fold (fun e ((_, p, _, _) as ed, vals) evts ->
    let pevts = try HMap.find p evts with Not_found -> [] in
    let pevts = (e, (ed, vals)) :: pevts in
    HMap.add p pevts evts
  ) evts HMap.empty


let subst sigma evts =
  HMap.map (fun ((d, p, q, ch), vals) ->
    let dpqch = d, Variable.subst sigma p, Variable.subst sigma q, ch in
    let vals = List.map (fun (cop, t) -> cop, Term.subst sigma t) vals in
    dpqch, vals
  ) evts

let filter_events_set sa =
  SAtom.filter (function
    | Atom.Comp (Access (a, [_]), _, _)
    | Atom.Comp (_, _, Access (a, [_])) -> not (is_event a)
    | _ -> true) sa
