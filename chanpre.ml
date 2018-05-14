
open Channels
open Chanevent
open Types
open Util



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

(* True means maybe, False means no *)
let compat_val stl vals =
  List.for_all (fun st ->
    List.for_all (fun (cop, t) -> compatible_terms st cop t) vals
  ) stl

(* For each send, get its compatible recvs *)
let recv_by_sends sends evts =
  HEvtMap.fold (fun (sd, sp, sq, sc) (se, stl) rbs ->
    (((sd, sp, sq, sc), (se, stl)), HMap.bindings
      (HMap.filter (fun re ((rd, rp, rq, rc), rvals) ->
       H.equal rd hR && H.equal sc rc &&
       (* (H.equal sq hNone || H.equal rq hNone || H.equal sq rq) && *)
       (H.equal rq hNone || H.equal sp rq) &&
       (H.equal sq hNone || H.equal sq rp) &&
       rvals <> [] && compat_val stl rvals) evts)
    ) :: rbs
  ) sends []

(* Build all possible send/recv combinations (no relation check) *)
let all_combinations rbs =
  let rec aux cl cc = function
    | [] -> cc :: cl
    | (s, rl) :: rbs ->
       let cl = aux cl cc rbs in (* try without satisfying *)
       List.fold_left (fun cl r -> aux cl ((s, r) :: cc) rbs) cl rl
  in
  aux [] [] rbs (* if rbs empty, this should correctly return [] *)


(* Build all send/recv combinations that do not lead to a cyclic ghb *)
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
    let ghb = List.fold_left (fun ghb (((_, _, _, sc), (se, _)), (re, _)) ->
      let ghb = Chanrel.Rel.add_lt se re ghb in (* rf *)
      HMap.fold (fun se2 ((sd2, _, _, sc2), _) ghb  -> (* fr *)
        if H.equal sd2 hS && H.equal sc sc2 &&
          Chanrel.Rel.mem_lt se se2 ghb then
            Chanrel.Rel.add_lt re se2 ghb
        else ghb
      ) evts ghb
    ) ghb src in

    (* Validate or reject combination depending on acyclicity test *)
    if Chanrel.Rel.acyclic ghb then
      (src, ghb, urevts) :: srcl
    else srcl

  ) [] srcl in

  TimeFilterRS.pause ();

  srcl

(*
ghb = co U ro U so U rf U fr

asc : co = /         ro = /         so = /
n-n : co = /         ro = eo ^ RR   so = eo ^ SS
1-n : co = /         ro = eo ^ RR   so = po ^ SS
n-1 : co = /         ro = po ^ RR   so = eo ^ SS
1-1 : co = /         ro = po ^ RR   so = po ^ SS
csl : co = po ^ RS   ro = po ^ RR   so = po ^ SS   (= 1-1 + co)
rsc : n-n + single pending send

new recv :
 *-n : ghb + eo ^ RR (ro)
 *-1 : ghb + po ^ RR (ro)
 csl : ghb + po ^ R* (ro / co)

new send :
 n-* : ghb + eo ^ SS (so)
 1-* : ghb + po ^ SS (so)
 csl : ghb + po ^ SS (so)

recv + send :
 * : ghb + rf + fr

fr (when S sat R) :
 n-* : fr = rf + (eo ^ SS) (so)
 1-* : fr = rf + (po ^ SS) (so)

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
       | [nt] when nt == t -> [Arith (t, c)]
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
    List.fold_left (fun rel e ->
      Chanrel.Rel.add_lt ie e rel) rel (f ied ie)
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

let mk_pred pred pl =
  Atom.Comp (Access (pred, pl), Eq, Elem (Term.htrue, Constr))

let add_ghb_lt_atoms ghb sa =
  Chanrel.Rel.fold_lt (fun ef et sa ->
    SAtom.add (mk_pred hGhb [ef; et]) sa) ghb sa



(* Retrieve the maximum event id for this proc *)
(* let max_proc_eid eids p =
 *   try IntSet.max_elt (HMap.find p eids) with Not_found -> 0 *)

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
  let sevts = Chanevent.send_events evts in (* to compute ro *)
  let revts = Chanevent.recv_events evts in (* to compute so / co *)
  let urevts = Chanevent.unsat_recv_events evts in (* to build rf/fr *)
  let ghb = Chanrel.extract_rels_set sa in (* for acyclicity test *)

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

  (* Extend ghb according to the following rules :
       New recv event :
         *-n : ghb + (eo ^ RR) (ro)
         *-1 : ghb + (po ^ RR) (ro)
         csl : ghb + (po ^ R* ) (ro / co)   *)
  let ghb' = add_ievts_rels ghb' ircs (fun (_, p1, _, c1) _ ->
    let ct, _ = chan_type c1 in
    let el =
      if ct = CCAUSAL then
        HMap.fold (fun e2 ((_, p2, _, c2), _) el ->
          if H.equal c1 c2 && H.equal p1 p2 then e2 :: el
          else el
        ) sevts []
      else [] in
    HMap.fold (fun e2 ((_, p2, _, c2), _) el ->
      if H.equal c1 c2 then
        match ct with
        | CNN | C1N | CRSC -> e2 :: el
        | CN1 | C11 | CCAUSAL -> if H.equal p1 p2 then e2 :: el else el
        | CASYNC -> el
      else el
    ) revts el
  ) in

  (* Extend ghb according to the following rules :
       New send event :
         n-* : ghb + (eo ^ SS) (so)
         1-* : ghb + (po ^ SS) (so)
         csl : ghb + (po ^ SS) (so) *)
  let ghb' = add_ievts_rels ghb' isds (fun (_, p1, _, c1) _ ->
    let ct, _ = chan_type c1 in
    HMap.fold (fun e2 ((_, p2, _, c2), _) el ->
      if H.equal c1 c2 then
        match ct with
        | CNN | CN1 | CRSC -> e2 :: el
        | C1N | C11 | CCAUSAL -> if H.equal p1 p2 then e2 :: el else el
        | CASYNC -> el
      else el
    ) sevts []
  ) in
(*
  Format.fprintf Format.std_formatter "isds : \n";
  HEvtMap.iter (fun (d, p, q, c) (e, _) ->
      Format.fprintf Format.std_formatter "%a:(%a,%a,%a,%a)\n"
        H.print e H.print d H.print p H.print q H.print c;
      Format.fprintf Format.std_formatter "\n"
  ) isds;

  Format.fprintf Format.std_formatter "ircs : \n";
  HEvtMap.iter (fun (d, p, q, c) (e, _) ->
      Format.fprintf Format.std_formatter "%a:(%a,%a,%a,%a)\n"
        H.print e H.print d H.print p H.print q H.print c;
      Format.fprintf Format.std_formatter "\n"
  ) ircs;

  Format.fprintf Format.std_formatter "sevts : \n";
  HMap.iter (fun e ((d, p, q, c), _) ->
      Format.fprintf Format.std_formatter "%a:(%a,%a,%a,%a)\n"
        H.print e H.print d H.print p H.print q H.print c;
      Format.fprintf Format.std_formatter "\n"
  ) sevts;

  Format.fprintf Format.std_formatter "revts : \n";
  HMap.iter (fun e ((d, p, q, c), _) ->
      Format.fprintf Format.std_formatter "%a:(%a,%a,%a,%a)\n"
        H.print e H.print d H.print p H.print q H.print c;
      Format.fprintf Format.std_formatter "\n"
  ) revts;

  Format.fprintf Format.std_formatter "Ghb : ";
  Chanrel.Rel.print_lt Format.std_formatter ghb';
  Format.fprintf Format.std_formatter "\n";
 *)
  (* Add fr from new recvs to old sends, depending on channel type *)
  (* let ghb' = add_ievts_rels ghb' ircs (
   *   fun (d, p, q, c) _ ->
   *     try None (\*Some (HVarMap.find (v, vi) gfw)*\)
   *     with Not_found -> None
   * ) in *)

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
