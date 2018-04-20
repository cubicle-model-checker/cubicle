
open Channels
open Chanevent
open Types
open Util

(* exception UnsatisfiableRecv *)



let compatible_consts c1 cop c2 =
  let c = Types.compare_constants c1 c2 in
  match cop with
  | CEq -> c = 0
  | CNeq -> c <> 0
  | CLt -> c < 0
  | CLe -> c <= 0
  | CGt -> c > 0
  | CGe -> c >= 0

(* True means maybe, False means no *)
let compatible_terms st cop rt = match st, rt with
  | Const c1, Const c2 -> compatible_consts c1 cop c2
  | Elem (c1, Constr), Elem (c2, Constr) ->
     if cop = CEq then H.equal c1 c2
     else if cop = CNeq then not (H.equal c1 c2)
     else failwith "Chanpre.compatible_terms : invalid op on Constr"
  | Elem (p1, Var), Elem (p2, Var) ->
     if cop = CEq then H.equal p1 p2
     else if cop = CNeq || cop = CLt || cop = CGt then not (H.equal p1 p2)
     else true (* CLe, CGe -> anything is potentially compatible *)
  | Elem (v1, Glob), Elem (v2, Glob) ->
     if cop = CNeq || cop = CLt || cop = CGt then not (H.equal v1 v2)
     else true (* CEq, CLe, CGe -> anything is potentially compatible *)
  (* | Access (v1, vi1), Access (v2, vi2) -> TODO *)
  | Arith (t1, c1), Arith (t2, c2) ->
     if not (Term.equal t1 t2) then true
     else compatible_consts c1 cop c2
  | _ ->
     if cop = CNeq || cop = CLt || cop = CGt then not (Term.equal st rt)
     else true

let compat_val stl vals =
  List.for_all (fun st ->
    List.for_all (fun (cop, t) -> compatible_terms st cop t) vals
  ) stl

(* let is_satisfied = function [] -> true | _ -> false *)

(* let get_send_on sends ed =
 *   try Some (HEvtMap.findp (fun eds _ -> same_chan eds ed) sends)
 *   with Not_found -> None *)
(*
let remove_write_on writes ed =
  HEvtMap.filter (fun edw _ -> not (same_var edw ed)) writes
let unsat_reads edw pevts =
  List.exists (fun (_, (ed, vals)) -> same_var edw ed && vals <> []) pevts
 *)


let recv_by_sends sends evts =
  HEvtMap.fold (fun (sd, sp, sq, sc) (se, stl) rbs ->
    (((sd, sp, sq, sc), (se, stl)), HMap.bindings
      (HMap.filter (fun re ((rd, rp, rq, rc), rvals) ->
       H.equal rd hR && H.equal sc rc &&
       (H.equal sq hNone || H.equal rq hNone || H.equal sq rq) &&
       rvals <> [] && compat_val stl rvals) evts)
    ) :: rbs
  ) sends []
  
let all_combinations rbs =
  let rec aux cl cc = function
    | [] -> cc :: cl
    | (s, rl) :: rbs ->
       let cl = aux cl cc rbs in (* try without satisfying *)
       List.fold_left (fun cl r -> aux cl ((s, r) :: cc) rbs) cl rl
  in
  aux [] [] rbs (* if rbs empty, this should correctly return [] *)



let make_recv_send_combinations sends evts urevts ghb =

  TimeBuildRS.start ();

  let rbs = recv_by_sends sends evts in
  let srcl = all_combinations rbs in

  TimeBuildRS.pause ();

  TimeFilterRS.start ();

  (* Filter out combinations that lead to cyclic relations *)
  let srcl = List.fold_left (fun srcl src ->

    (* Remove satisfied recvs from unsatisfied set *)
    let urevts = List.fold_left (fun urevts (_, (re, _)) ->
        HMap.remove re urevts
    ) urevts src in

    (* Adjust ghb for this combination *)
    let ghb = List.fold_left (fun ghb (((_,_,_,sc), (se,_)), (re, _)) ->
      let ghb = Chanrel.Rel.add_lt se re ghb in (* rf *)
      
      HMap.fold (fun ure ((_,_,_,urc), _) ghb -> (* fr *)
          if H.equal sc urc then
            Chanrel.Rel.add_lt ure se ghb
          else ghb
        ) urevts ghb
    ) ghb src in
    if Chanrel.Rel.acyclic ghb then
      (src, ghb, urevts) :: srcl
    else srcl
  ) [] srcl in

  TimeFilterRS.pause ();

  srcl

(*

new recv (cc)
 -> csl : ghb + po/rs

new send (cc)
 -> csl : ghb + po/ss

new recv (ro) :
 -> async : nothing
 -> rsc / n-n / 1-n : ghb + sched/rr
 -> csl / n-1 / 1-1 : ghb + po/rr

new send (so):
 -> async : nothing
 -> rsc / n-n : ghb + sched/ss
 ->       n-1 : ghb + sched/ss/rpo
 ->       1-n : ghb + po/ss
 ->       1-1 : ghb + po/ss/rpo
 ->       csl : ghb + po/ss

recv + send :
 -> add ghb (recv, send)

when new send satisfy old recv
 -> new send if ghb-before (rf) old recv
 -> old recv is ghb-before (fr) old sends that are ghb-after (so) the new send

Heuristics :
n-n : a new send MUST satisfy the oldest recv in ro (or none if lossy)
n-1 : a new send MUST satisfy the oldest recv in ro / thread (non if lossy)
1-n : a new send CAN'T satisfy the oldest recv in ro if it is so-before
      an older send that satisfies old recv that are before the oldest
1-1 : a new send CAN'T satisfy the oldest recv in ro / thread if it is so-before
      an older send that satisfies old recv that are before the oldest
*)



let subst_event_val sfun sa =
  let rec process_t = function
    | Access (f, [e]) as t when is_value f -> sfun t e
    | Arith (t, c) ->
       let ntl = process_t t in
       begin match ntl with
       | [] -> failwith "Chanpre.subst_event_val : ntl can't be empty"
       | [nt] when nt == t -> [t]
       | _ -> List.map (fun nt -> Arith (nt, c)) ntl
       end
    | t -> [t]
  in
  SAtom.fold (fun at sa -> match at with
    | Atom.Comp (t1, op, t2) ->
       let ntl1 = process_t t1 in
       let ntl2 = process_t t2 in
       begin match ntl1, ntl2 with
       | [], _ | _, [] ->
          failwith "Chanpre.subst_event_val : ntl can't be empty"
       | [nt1], [nt2] when nt1 == t1 && nt2 == t2 -> SAtom.add at sa
       | _, _ ->
          List.fold_left (fun sa nt1 ->
            List.fold_left (fun sa nt2 ->
              SAtom.add (Atom.Comp (nt1, op, nt2)) sa
            ) sa ntl2
          ) sa ntl1 (* ntl probably haev a single element *)
       end
    | Atom.Ite _ ->
       failwith "Chanpre.subst_event_val : Ite should not be there"
    | _ -> SAtom.add at sa
  ) sa SAtom.empty

let rec subst_ievent ievts t = match t with
  | Recv (p, q, ch) ->
     let _, tval, _ = HEvtMap.find (hR, p, q, mk_hC ch) ievts in
     tval
  | Arith (t, c) -> Arith (subst_ievent ievts t, c)
  | _ -> t

let add_ievts_rels rel ievts f =
  HEvtMap.fold (fun ied (ie, _) rel ->
    match f ied ie with
    | None -> rel | Some el ->
      List.fold_left (fun rel e ->
        Chanrel.Rel.add_lt ie e rel) rel el
  ) ievts rel

let add_recvs_to_sa irds sa =
  (* That might generate duplicate (opposite direction) atoms *)
  HEvtMap.fold (fun dpqch (e, lt, vals) sa ->
    List.fold_left (fun sa (cop, rt) ->
      let rt = subst_ievent irds rt in
      let a = match cop with
        | CEq -> Atom.Comp (lt, Eq, rt)
        | CNeq -> Atom.Comp (lt, Neq, rt)
        | CLt -> Atom.Comp (lt, Lt, rt)
        | CLe -> Atom.Comp (lt, Le, rt)
        | CGt -> Atom.Comp (rt, Lt, lt)
        | CGe -> Atom.Comp (rt, Le, lt)
      in
      SAtom.add a sa
    ) sa vals
  ) irds sa

(* let ghb_before_urd ghb urd e =
 *   HMap.exists (fun re _ ->
 *     Chanrel.Rel.mem_lt e re ghb || Chanrel.Rel.mem_eq e re ghb) urd *)

let mk_pred pred pl =
  Atom.Comp (Access (pred, pl), Eq, Elem (Term.htrue, Constr))

let add_ghb_lt_atoms ghb sa =
  Chanrel.Rel.fold_lt (fun ef et sa ->
    SAtom.add (mk_pred hGhb [ef; et]) sa) ghb sa

(* let add_ghb_eq_atoms ghb sa =
 *   Chanrel.Rel.fold_eq (fun e1 e2 sa ->
 *     SAtom.add (mk_pred hSync [e1; e2]) sa) ghb sa *)

(* let mk_pairs l =
 *   let rec aux acc = function
 *     | [] | [_] -> acc
 *     | e1 :: el -> aux (List.fold_left (fun acc e2 -> (e1, e2) :: acc) acc el) el
 *   in
 *   aux [] l *)





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
(* let eid_diff eids_high eids_low =
 *   HMap.merge (fun _ h l ->
 *     match h, l with
 *     | Some h, Some l -> Some (IntSet.diff h l)
 *     | Some h, None -> Some h
 *     | _ -> failwith "Chanevent.eid_diff : internal error"
 *   ) eids_high eids_low *)

(* Build an event *)
let build_event e d p q ch = (* ch with _C prefix *)
  let _, vt = Channels.chan_type ch in
  let tval = Access (mk_hVal vt, [e]) in
  let adir = Atom.Comp (Access (hDir, [e]), Eq, Elem (d, Constr)) in
  let athr = Atom.Comp (Access (hThr, [e]), Eq, Elem (p, Var)) in
  let apeer = Atom.Comp (Access (hPeer, [e]), Eq, Elem (q, Var)) in
  let achan = Atom.Comp (Access (hChan, [e]), Eq, Elem (ch, Constr)) in
  let sa = SAtom.add achan (SAtom.add athr (SAtom.singleton adir)) in
  let sa = if H.equal q hNone then sa else SAtom.add apeer sa in
  sa, tval





let satisfy_recvs sa =

  TimeSatRecv.start ();

  let sa, rcs, sds, eids, evts = Chanevent.extract_events_set sa in
  let urevts = Chanevent.unsat_recv_events evts in (* to associate to sds *)
  let ghb = Chanrel.extract_rels_set sa in (* for acyclicity *)

  let eids' = eids in
  let ghb' = ghb in
  
  (* Generate an id for each new send event *)
  let isds, eids' = HEvtMap.fold (fun ((_,p,_,_) as dpqc) vals (isds, eids') ->
    let eid, eids' = fresh_eid eids' p in
    HEvtMap.add dpqc (mk_hE eid, vals) isds, eids'
  ) sds (HEvtMap.empty, eids') in

  (* Generate an id for each new recv event *)
  let ircs, eids' = HEvtMap.fold (fun ((_,p,_,_) as dpqc) vals (ircs, eids') ->
    let eid, eids' = fresh_eid eids' p in
    HEvtMap.add dpqc (mk_hE eid, vals) ircs, eids'
  ) rcs (HEvtMap.empty, eids') in

  (* Add so from new sends to old sends on same channel,
     depending on the channel type *)
  let ghb' = add_ievts_rels ghb' isds (
    fun (d, p, q, c) _ ->
      try None (*Some (HVarMap.find (v, vi) gfw)*) (* list of sends in so *)
      with Not_found -> None
  ) in

  (* Add ro from new recvs to old recvs on same channel,
     depending on the channel type *)
  let ghb' = add_ievts_rels ghb' ircs (
    fun (d, p, q, c) _ ->
      try None (*Some (HVarMap.find (v, vi) gfw)*) (* list of sends in so *)
      with Not_found -> None
  ) in

  (* Add fr from new recvs to first old sends on same channel *)
  let ghb' = add_ievts_rels ghb' ircs (
    fun (d, p, q, c) _ ->
      try None (*Some (HVarMap.find (v, vi) gfw)*)
      with Not_found -> None
  ) in

  

  (* Build the relevant recv-send combinations *)
  let srcl = make_recv_send_combinations isds evts urevts ghb' in

  let pres =
    if srcl = [] then failwith "Chanpre : empty combination list"
    else begin     (* maybe with lossless FIFO this makes sense *)

    (* Instantiate new send events *)
    let isds, sa = HEvtMap.fold (fun (d, p, q, ch) (e, vals) (isds, sa) ->
      let na, _ = build_event e d p q ch in
      (HEvtMap.add (d, p, q, ch) (e, vals) isds, SAtom.union na sa)
    ) isds (HEvtMap.empty, sa) in

    (* Instantiate new recv events *)
    let ircs, sa = HEvtMap.fold (fun (d, p, q, ch) (e, vals) (ircs, sa) ->
      let na, tval = build_event e d p q ch in
      (HEvtMap.add (d, p, q, ch) (e, tval, vals) ircs, SAtom.union na sa)
    ) ircs (HEvtMap.empty, sa) in

    (* Add recvs with their values (which may be recvs too) *)
    let sa = add_recvs_to_sa ircs sa in

    (* Update the set of atoms with relations computed so far *)
    let d = Chanrel.Rel.diff ghb' ghb in
    let sa = add_ghb_lt_atoms d sa in
    let ghb = ghb' in

    (* Generate the atom sets for each combination *)
    let pres = List.fold_left (fun pres (src, ghb', urevts') ->

      (* Substitute the satisfied recv value with the send value *)
      let sa = List.fold_left (fun sa ((_, (_, stl)), (re, _)) ->
        let stl = List.map (subst_ievent ircs) stl in
        subst_event_val (fun t e -> if H.equal e re then stl else [t]) sa
      ) sa src in

      (* Update the set of atoms with the remaining relations (rf / fr) *)
      let sa = add_ghb_lt_atoms (Chanrel.Rel.diff ghb' ghb) sa in

      (* Simplify here in case adding reads added duplicates *)
      try (Cube.simplify_atoms sa) :: pres (* Cube.create_normal ? *)
      with Exit -> pres

    ) [] srcl in pres

  end in

  TimeSatRecv.pause ();

  pres
