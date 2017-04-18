
open Weakmem
open Types

module STerm = Term.Set



module Int = struct
  type t = int
  let compare = Pervasives.compare
end

module IntSet = Set.Make (Int)



(* Retrieve the maximum event id for this proc *)
let max_proc_eid eids p =
  try IntSet.max_elt (HMap.find p eids) with Not_found -> 0

(* Generate a fresh event id for this proc *)
let fresh_eid eids p =
  let eid = 1 + HMap.fold (fun _ peids maxeid ->
    max maxeid (IntSet.max_elt peids)) eids 0 in
  let peids = try HMap.find p eids with Not_found -> IntSet.empty in
  eid, HMap.add p (IntSet.add eid peids) eids

(* Compute the difference between event id sets by proc *)
let eid_diff eids_high eids_low =
  HMap.merge (fun _ h l ->
    match h, l with
    | Some h, Some l -> Some (IntSet.diff h l)
    | Some h, None -> Some h
    | _ -> failwith "Weakevent.eid_diff : internal error"
  ) eids_high eids_low



(* Given an atom set, separate pure atoms from reads/writes/fences
   and determine the next event id to attribute for each thread
   The atom set should have events, reads, pre-processed writes, fences *)
let extract_events sa =
  let rec has_read = function
    | Arith (t, _) -> has_read t
    | Read _ -> true
    | _ -> false
  in  
  let rec update_eids eids = function
    | Atom.Comp (Field (Access (a, [e]), f), Eq, Elem (p, _))
    | Atom.Comp (Elem (p, _), Eq, Field (Access (a, [e]), f))
         when H.equal a hE && H.equal f hThr ->
       let peids = try HMap.find p eids with Not_found -> IntSet.empty in
       HMap.add p (IntSet.add (int_of_e e) peids) eids
    | _ -> eids
  in
  let find_event_safe e evts =
    try HMap.find e evts with Not_found -> ((hNone, hNone, hNone, []), false)
  in
  SAtom.fold (fun a (sa_pure, sa_rds, sa_wts, fces, eids, evts) -> match a with
    | Atom.Comp (Field (Access (ar, [e]), f), Eq, Elem (c, t))
    | Atom.Comp (Elem (c, t), Eq, Field (Access (ar, [e]), f))
         when H.equal ar hE ->
       let ((p, d, v, vi), hv) as evt = find_event_safe e evts in
       let evt = if H.equal f hThr then ((c, d, v, vi), hv)
            else if H.equal f hDir then ((p, c, v, vi), hv)
	    else if H.equal f hVar then ((p, d, c, vi), hv)
            else if is_param f then ((p, d, v, (f, c) :: vi), hv)
            else evt in
       (SAtom.add a sa_pure, sa_rds, sa_wts, fces,
        update_eids eids a, HMap.add e evt evts)
    | Atom.Comp (Field (Field (Access (ar, [e]), f), _), _, _)
    | Atom.Comp (_, _, Field (Field (Access (ar, [e]), f), _))
         when H.equal ar hE && H.equal f hVal ->
       let ((p, d, v, vi), hv) as evt = find_event_safe e evts in
       let evt = ((p, d, v, vi), true) in
       (SAtom.add a sa_pure, sa_rds, sa_wts, fces,
        update_eids eids a, HMap.add e evt evts)
    | Atom.Comp (Fence p, _, _) | Atom.Comp (_, _, Fence p) ->
       (sa_pure, sa_rds, sa_wts, p :: fces, eids, evts)
    | Atom.Comp (Write _, _, _) | Atom.Comp (_, _, Write _) ->
       (sa_pure, sa_rds, SAtom.add a sa_wts, fces, eids, evts)
    | Atom.Comp (t1, _, t2) when has_read t1 || has_read t2 ->
       (sa_pure, SAtom.add a sa_rds, sa_wts, fces, update_eids eids a, evts)
    | Atom.Ite _ ->
       failwith "Weakevent.extract_events : Ite should not be there"
    | _ -> (SAtom.add a sa_pure, sa_rds, sa_wts, fces, update_eids eids a, evts)
  ) sa (SAtom.empty, SAtom.empty, SAtom.empty, [], HMap.empty, HMap.empty)



(* Extract unique read terms from the specified set of atoms *)
let read_terms sa =
  let rec reads_of srt td = match td with
    | Arith (td, _) -> reads_of srt td
    | Read _ -> STerm.add td srt
    | _ -> srt
  in
  SAtom.fold (fun a srt -> match a with
    | Atom.Comp (t1, _, t2) -> reads_of (reads_of srt t1) t2
    | _ -> srt
  ) sa STerm.empty

(* Extract unique write terms from the specified set of atoms *)
let write_terms sa =
  let rec writes_of swt td = match td with
    | Write _ -> STerm.add td swt
    | _ -> swt
  in
  SAtom.fold (fun a swt -> match a with
    | Atom.Comp (t1, _, t2) -> writes_of (writes_of swt t1) t2
    | _ -> swt
  ) sa STerm.empty

(* Extract events corresponding to writes *)
let write_events evts =
  HMap.fold (fun e (ed, hv) wevts ->
    if is_write ed then HMap.add e (sort_params ed) wevts else wevts
  ) evts HMap.empty

(* Extract unsatified reads *)
let unsat_rd_events evts =
  HMap.fold (fun e (ed, hv) urevts ->
    if is_read ed && hv then HMap.add e (sort_params ed) urevts else urevts
  ) evts HMap.empty



(* Build an event *)
let build_event e p d v vi = (* v in original form without _V *)
  let _, ret = Smt.Symbol.type_of v in
  let v = mk_hV v in
  let tevt = Access (hE, [e]) in
  let tval = Field (Field (tevt, hVal), mk_hT ret) in
  let athr = Atom.Comp (Field (tevt, hThr), Eq, Elem (p, Var)) in
  let adir = Atom.Comp (Field (tevt, hDir), Eq, Elem (d, Constr)) in
  let avar = Atom.Comp (Field (tevt, hVar), Eq, Elem (v, Constr)) in
  let sa, _ = List.fold_left (fun (sa, i) v ->
    SAtom.add (Atom.Comp (Field (tevt, mk_hP i), Eq, Elem (v, Var))) sa, i + 1
  ) (SAtom.add avar (SAtom.add adir (SAtom.singleton athr)), 1) vi in
  sa, tval


             
(* Substitute a term by another in the given atom set *)
let event_subst t te sa = (* more general than just event_subst *)
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



(* Replace plain read/writes by actual events + add rf pairs
   Used by pre-image, and when generating events for unsafe / invariants *)
let instantiate_events sa =

  (* Build a predicate atom *)
  let mk_pred pred pl =
    Atom.Comp (Access (pred, pl), Eq, Elem (Term.htrue, Constr)) in

  (* Extract the relevant events *)
  let sa_pure, sa_rds, sa_wts, fce, eids, evts = extract_events sa in
  let swt = write_terms sa_wts in
  let srt = read_terms sa_rds in
  let wevts = write_events evts in
  let urevts = unsat_rd_events evts in
  
  (* Remember eids before starting instanciation *)
  let eids_before = eids in

  (* First, generate Write events and their rf/co/fr *)
  let (eids, sa_new, writes) = STerm.fold (
    fun t (eids, sna, writes) -> match t with
    | Write (p, v, vi, srl) ->
       let eid, eids = fresh_eid eids p in
       let e = mk_hE eid in
       let evt = (p, hW, mk_hV v, vi) in
       let na, _ = build_event e p hW v vi in
       let sna = List.fold_left (fun sna re -> (* rf *)
	 SAtom.add (mk_pred hRf [e; re]) sna
       ) (SAtom.union na sna) srl in
       let sna = HMap.fold (fun we wevt sna -> (* co *)
         if not (same_var evt wevt) then sna
         else SAtom.add (mk_pred hCo [e; we]) sna
       ) wevts sna in
       let sna = HMap.fold (fun ure urevt sna -> (* fr *)
         if not (same_var evt urevt) then sna
         else SAtom.add (mk_pred hFr [ure; e]) sna
       ) urevts sna in
       (eids, sna, HMap.add e evt writes)
    | _ -> assert false
  ) swt (eids, SAtom.empty, HMap.empty) in

  (* Then, generate Read events *)
  let (eids, sa_new, sa_rds, reads) = STerm.fold (
    fun t (eids, sna, sra, reads) -> match t with
    | Read (p, v, vi) ->
       let eid, eids = fresh_eid eids p in
       let e = mk_hE eid in
       let evt = (p, hR, mk_hV v, vi) in
       let na, tval = build_event e p hR v vi in
       let sna = HMap.fold (fun we wevt sna -> (* fr *)
         if not (same_var evt wevt) then sna
         else SAtom.add (mk_pred hFr [e; we]) sna
       ) wevts (SAtom.union na sna) in
       (eids, sna, event_subst t tval sra, HMap.add e evt reads)
    | _ -> assert false
  ) srt (eids, sa_new, sa_rds, HMap.empty) in

  (* Generate proper fences *) (* what on different procs ? *)
  let sa_fence = List.fold_left (fun sfa p ->
    let eid = max_proc_eid eids p in
    if eid <= 0 then sfa else
    SAtom.add (mk_pred hFence [p; mk_hE eid]) sfa
  ) SAtom.empty fce in

  (* Generate sync for synchronous events (for reads : even on <> threads) *)
  let mk_sync eid_range = HMap.fold (fun _ peids sync ->
      IntSet.fold (fun eid sync -> (mk_hE eid) :: sync
    ) peids sync) eid_range [] in
  let mk_sync_sa sync = match sync with [] | [_] -> SAtom.empty | _ ->
    SAtom.singleton (mk_pred hSync (List.rev sync)) in
  let sa_sync = mk_sync_sa (mk_sync (eid_diff eids eids_before)) in

  (* Merge all atom sets *)
  SAtom.union sa_pure (SAtom.union sa_fence
    (SAtom.union sa_sync (SAtom.union sa_rds sa_new)))

(*
  in a transition, forbid writes by a thread that has no read
  forbid writes by different threads
  check if reads by different threads are ok (needed for unsafe/invariant)
  fences should only be before procs that have reads in the transition
*)
