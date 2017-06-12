
open Weakmem
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
  try HMap.find e evts with Not_found -> ((hNone, hNone, hNone, []), [])

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



let rec has_read = function
  | Arith (t, _) -> has_read t
  | Read _ -> true
  | _ -> false

let find_uevent evts pdvvi =
  try HEvtMap.find pdvvi evts with Not_found -> []

let add_uevent evts pdvvi nvals =
  let vals = find_uevent evts pdvvi in
  HEvtMap.add pdvvi (nvals @ vals) evts

let rec split_read = function
  | Read (p, v, vi) -> Some (p, v, vi), None
  | Arith (t, c) -> fst (split_read t), Some c (* assert (snd... = None) *)
  | _ -> None, None

let process_read rds tr cop tv =
  let r, c = split_read tr in
  match r with
  | Some (p, v, vi) ->
     let tv = match c with Some c -> subs_const_from_term c tv | _ -> tv in
     add_uevent rds (p, hR, mk_hV v, vi) [(cop, tv)]
  | _ -> rds

let process_read_noval rds tr =
  match fst (split_read tr) with
  | Some (p, v, vi) -> add_uevent rds (p, hR, mk_hV v, vi) []
  | _ -> rds



(* let update_eids eids p e = *)
(*   let peids = try HMap.find p eids with Not_found -> IntSet.empty in *)
(*   HMap.add p (IntSet.add (int_of_e e) peids) eids *)

let extract_event (sa_pure, rds, wts, fces, eids, evts) at = match at with
  (* Fence *)
  | Atom.Comp (Fence p, _, _) | Atom.Comp (_, _, Fence p) ->
     (sa_pure, rds, wts, p :: fces, eids, evts) (* single fence allowed *)
  (* Write (may have Reads as value) *)
  | Atom.Comp (Write _, _, Write _) ->
     failwith "Weakevent.extract_events : can't have Write on both sides !"
  | Atom.Comp (Write (p, v, vi, _), _, t)
  | Atom.Comp (t, _, Write (p, v, vi, [])) ->
     let wts = add_uevent wts (p, hW, mk_hV v, vi) [t] in
     let rds = process_read_noval rds t in
     (sa_pure, rds, wts, fces, eids, evts)
  (* Read (both sides may be Reads + can have instantiated read as value) *)
  | Atom.Comp (t1, op, t2) when has_read t1 || has_read t2 ->
     let rds = process_read rds t1 (cop_of_r_op false op) t2 in
     let rds = process_read rds t2 (cop_of_r_op true op) t1 in
     let evts = process_event evts t1 (cop_of_r_op false op) t2 in
     let evts = process_event evts t2 (cop_of_r_op true op) t1 in
     (sa_pure, rds, wts, fces, eids, evts)
  (* Thread / Direction / Variable / Indices *)
  | Atom.Comp (Access (f, [e]), Eq, Elem (c, t))
  | Atom.Comp (Elem (c, t), Eq, Access (f, [e]))
       when is_event f && not (is_value f) ->
     let ((p, d, v, vi), vals) as evt = find_ievent evts e in
     let evt = if H.equal f hThr then ((c, d, v, vi), vals)
          else if H.equal f hDir then ((p, c, v, vi), vals)
	  else if H.equal f hVar then ((p, d, c, vi), vals)
          else if is_param f then ((p, d, v, (f, c) :: vi), vals)
          else evt in
     (* let eids = if H.equal f hThr then update_eids eids c e else eids in *)
     (SAtom.add at sa_pure, rds, wts, fces, eids, HMap.add e evt evts)
  (* Value *)
  | Atom.Comp (t1, op, t2) ->
     let evts = process_event evts t1 (cop_of_r_op false op) t2 in
     let evts = process_event evts t2 (cop_of_r_op true op) t1 in
     (SAtom.add at sa_pure, rds, wts, fces, eids, evts)
  | Atom.Ite _ ->
     failwith "Weakpre.extract_events : Ite should not be there"
  | _ -> (SAtom.add at sa_pure, rds, wts, fces, eids, evts)


let init_acc =
  (SAtom.empty, HEvtMap.empty, HEvtMap.empty, [], HMap.empty, HMap.empty)

let post_process (sa_pure, rds, wts, fces, eids, evts) =
  let evts = HMap.map (fun (ed, vals) -> sort_params ed, vals) evts in
  let eids = HMap.fold (fun e ((p, _, _, _), _) eids ->
    let peids = try HMap.find p eids with Not_found -> IntSet.empty in
    HMap.add p (IntSet.add (int_of_e e) peids) eids
  ) evts HMap.empty in
  sa_pure, rds, wts, fces, eids, evts (* should be sorted already *)

let extract_events_array ar =
  post_process (Array.fold_left (fun acc a -> extract_event acc a) init_acc ar)

let extract_events_set sa =
  post_process (SAtom.fold (fun a acc -> extract_event acc a) sa init_acc)

let write_events evts =
  HMap.filter (fun _ (ed, _) -> is_write ed) evts

let unsat_read_events evts =
  HMap.filter (fun _ (ed, vals) -> is_read ed && vals <> []) evts

let sat_events evts =
  HMap.filter (fun _ (_, vals) -> vals = []) evts

let events_by_thread evts = (* by chance, this sorts event in correct order *)
  HMap.fold (fun e ((p, _, _, _) as ed, vals) evts ->
    let pevts = try HMap.find p evts with Not_found -> [] in
    let pevts = (e, (ed, vals)) :: pevts in
    HMap.add p pevts evts
  ) evts HMap.empty


let subst sigma evts =
  HMap.map (fun ((p, d, v, vi), vals) ->
    let pdvvi = Variable.subst sigma p, d, v,
                List.map (Variable.subst sigma) vi in
    let vals = List.map (fun (cop, t) -> cop, Term.subst sigma t) vals in
    pdvvi, vals
  ) evts
