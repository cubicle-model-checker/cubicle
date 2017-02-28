
open Weakmem
open Types

module STerm = Term.Set



(* Retrieve the current event id for this proc *)
let current_eid eids p =
  try HMap.find p eids with Not_found -> 0

(* Generate a fresh event id for this proc *)
let fresh_eid eids p =
  let eid = 1 + current_eid eids p in
  eid, HMap.add p eid eids

(* If e > current eid for this proc, then take e as next id *)
let maximize_eid eids p e =
  if e <= current_eid eids p then eids
  else HMap.add p e eids

(* Compute the range between event ids per proc ]low;high] *)
let eid_range eids_low eids_high =
  HMap.merge (fun p l h ->
    match l, h with
    | Some l, Some h -> Some (l + 1, h)
    | None, Some h -> Some (1, h)
    | _ -> failwith "Weakevent.eid_range : internal error"
  ) eids_low eids_high



(* Given an atom set, separate pure atoms from reads/writes/fences
   and determines the next event id to attribute for each thread
   The atom set should have events, reads, pre-processed writes, fences *)
let extract_events sa =
  let rec has_read = function
    | Arith (t, _) -> has_read t
    | Read _ -> true
    | _ -> false
  in  
  let rec update_eids_t eids = function
    | Arith (t, _) -> update_eids_t eids t
    | Field (Access (a, [p; e]), _) when H.equal a hE ->
       maximize_eid eids p (int_of_e e)
    | _ -> eids
  in
  let rec update_eids eids = function
    | Atom.Comp (t1, _, t2) -> update_eids_t (update_eids_t eids t1) t2
    | _ -> eids
  in
  SAtom.fold (fun a (sa_pure, sa_rds, sa_wts, fce, eids) -> match a with
    | Atom.Comp (Fence p, _, _) | Atom.Comp (_, _, Fence p) ->
       (sa_pure, sa_rds, sa_wts, p :: fce, eids)
    | Atom.Comp (Write _, _, _) | Atom.Comp (_, _, Write _) ->
       (sa_pure, sa_rds, SAtom.add a sa_wts, fce, eids)
    | Atom.Comp (t1, _, t2) when has_read t1 || has_read t2 ->
       (sa_pure, SAtom.add a sa_rds, sa_wts, fce, update_eids eids a)
    | Atom.Ite _ ->
       failwith "Weakevent.extract_event : Ite should not be there"
    | _ -> (SAtom.add a sa_pure, sa_rds, sa_wts, fce, update_eids eids a)
) sa (SAtom.empty, SAtom.empty, SAtom.empty, [], HMap.empty)



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



(* Build an event *)
let build_event p e d v vi = (* v in original form without _V *)
  let _, ret = Smt.Symbol.type_of v in
  let v = mk_hV v in
  let tevt = Access (hE, [p; e]) in
  let tval = Field (Field (tevt, hVal), mk_hT ret) in
  let adir = Atom.Comp (Field (tevt, hDir), Eq, Elem (d, Constr)) in
  let avar = Atom.Comp (Field (tevt, hVar), Eq, Elem (v, Constr)) in
  let sa, _ = List.fold_left (fun (sa, i) v ->
    SAtom.add (Atom.Comp (Field (tevt, mk_hP i), Eq, Elem (v, Var))) sa, i + 1
  ) (SAtom.add avar (SAtom.singleton adir), 1) vi in (* should memoize params *)
  sa, tval


             
(* Substitute a term by another in the given atom set *)
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



(* Build a predicate atom *)
let mk_pred pred pl =
  Atom.Comp (Access (pred, pl), Eq, Elem (Term.htrue, Constr))



(* Replace plain read/writes by actual events + add rf pairs
   Used by pre-image, and when generating events for unsafe / invariants *)
let instantiate_events sa =

  (* Extract the relevant events *)
  let sa_pure, sa_rds, sa_wts, fce, eids = extract_events sa in
  let swt = write_terms sa_wts in
  let srt = read_terms sa_rds in

  (* Remember eids before *)
  let eids_before = eids in

  (* First, generate Write events and their rf *)
  let (eids, sa_new) = STerm.fold (fun t (eids, sna) -> match t with
    | Write (p, v, vi, srl) ->
       let eid, eids = fresh_eid eids p in
       let e = mk_hE eid in
       let na, _ = build_event p e hW v vi in
       let sna = List.fold_left (fun sna (rp, re) ->
	 SAtom.add (mk_pred hRf [p; e; rp; re]) sna
       ) (SAtom.union na sna) srl in
       (eids, sna)
    | _ -> assert false
  ) swt (eids, SAtom.empty) in

  (* Then, generate Read events *)
  let (eids, sa_new, sa_rds) = STerm.fold (fun t (eids,sna,sra) -> match t with
    | Read (p, v, vi) ->
       let eid, eids = fresh_eid eids p in
       let na, tval = build_event p (mk_hE eid) hR v vi in
       (eids, SAtom.union na sna, event_subst t tval sra)
    | _ -> assert false
  ) srt (eids, sa_new, sa_rds) in

  (* Generate proper fences *) (* Should add fence with other procs *)
  let sa_fence = List.fold_left (fun sfa p ->
    let eid = current_eid eids p in
    if eid <= 0 then sfa else (* no fence if no event after *)
      SAtom.add (mk_pred hFence [p; mk_hE eid]) sfa
  ) SAtom.empty fce in

  (* Generate sync for synchronous events, even on different threads *)
  let sync = HMap.fold (fun p (cl, ch) sync ->
    let sync = ref sync in
    for i = cl to ch do sync := mk_hE i :: p :: !sync done;
    !sync
  ) (eid_range eids_before eids) [] in
  let sa_sync = match sync with [] | [_; _] -> SAtom.empty | _ ->
    SAtom.singleton (mk_pred hSync (List.rev sync)) in

  (* Merge all atom sets *)
  SAtom.union sa_pure (SAtom.union sa_fence
    (SAtom.union sa_sync (SAtom.union sa_rds sa_new)))








(*module WH = Hashtbl.Make (struct
  type t = (H.t * Variable.t list)
  let equal (v1, vi1) (v2, vi2) =
    H.equal v1 v2 && H.list_equal vi1 vi2
  let hash = Hashtbl.hash
end)*)

  (* let sa_sync = HMap.fold (fun p (cl, ch) ssa -> *)
    (* let pl = ref [] in *)
    (* for i = cl to ch do pl := mk_hE i :: p :: !pl done; *)
    (* match !pl with [] | [_;_] -> ssa | _ -> *)
    (*   SAtom.add (mk_pred hSync (List.rev !pl)) ssa *)
    (* let ssa = ref ssa in *)
    (* for i = cl to ch - 1 do *)
    (*   ssa := SAtom.add (mk_pred hSync [p; mk_hE i; p; mk_hE (i+1)]) !ssa *)
    (* done; *)
    (* !ssa *)
  (* ) (eid_range cnt_before cnt) SAtom.empty in *)



(* let make_init_write = *)
(*   let events = WH.create 16 in *)
(*   let nbe = ref 0 in *)
(*   fun (vv, vi) ->   (\* vv already in _Vx form (from Weakwrite) *\) *)
(*     try WH.find events (vv, vi) with Not_found -> *)
(*       let hEi = nbe := !nbe + 1; mk_hE !nbe in       *)
(*       let v = H.make (var_of_v vv) in (\* v in original form *\) *)
(*       let sa, _ = build_event hP0 hEi hW v vi in *)
(*       let vt = if vi = [] then Elem (v, Glob) else Access (v, vi) in *)
(*       WH.add events (vv, vi) ((hP0, hEi), vt, sa); *)
(*       ((hP0, hEi), vt, sa) *)
