
open Weakmem
open Weakevent
open Types
open Util

exception UnsatisfiableRead



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
let compatible_terms wt cop rt = match wt, rt with
  | Const c1, Const c2 -> compatible_consts c1 cop c2
  | Elem (c1, Constr), Elem (c2, Constr) ->
     if cop = CEq then H.equal c1 c2
     else if cop = CNeq then not (H.equal c1 c2)
     else failwith "Weakwrite.compatible_terms : invalid op on Constr"
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
     if cop = CNeq || cop = CLt || cop = CGt then not (Term.equal wt rt)
     else true

let compat_val wtl vals =
  List.for_all (fun wt ->
    List.for_all (fun (cop, t) -> compatible_terms wt cop t) vals
  ) wtl

let is_satisfied = function [] -> true | _ -> false

let get_write_on writes ed =
  try Some (HEvtMap.findp (fun edw _ -> same_var edw ed) writes)
  with Not_found -> None

let remove_write_on writes ed =
  HEvtMap.filter (fun edw _ -> not (same_var edw ed)) writes

let unsat_reads edw pevts =
  List.exists (fun (_, (ed, vals)) -> same_var edw ed && vals <> []) pevts
              
let skip_incompatible writes pevts = (* wtl should contain only 1 element *)
  let rec aux ((wr, ird, srd, urd) as reason) = function
    | [] -> reason, []
    | ((_, (ed, vals)) as e) :: pevts ->
       begin match get_write_on writes ed with
       | None -> aux reason pevts (* not same var : no problem *)
       | Some (edw, (_, _, wtl)) ->
          if is_write ed then
            aux (true, ird, srd, urd || unsat_reads edw pevts) pevts
          else if is_satisfied vals then
            aux (wr, ird, true, urd || unsat_reads edw pevts) pevts
          else if not (compat_val wtl vals) then
            aux (wr, true, srd, urd) pevts
          else
            (wr, ird, srd, urd), e :: pevts (* compatible = go on *)
       end
  in
  aux (false, false, false, false) pevts

let get_read_chunk writes pevts =
  let rec aux chunk writes cut = function
    | [] -> List.rev chunk, cut
    | ((_, (ed, vals)) as e) :: pevts ->
       begin match get_write_on writes ed with
       | None -> aux chunk writes cut pevts
       | Some (edw, (_, _, wtl)) ->
          if is_write ed || is_satisfied vals || not (compat_val wtl vals)
          then begin
            let cut = if cut = [] then e :: pevts else cut in
            let writes = remove_write_on writes ed in
            if HEvtMap.cardinal writes = 0 then List.rev chunk, cut
            else aux chunk writes cut pevts
          end
          else aux (e :: chunk) writes cut pevts
       end
  in
  aux [] writes [] pevts

let read_chunks_for_writes same_thread writes pevts =
  let rec aux chunks = function
    | [] -> List.rev chunks
    | pevts ->
       let chunk, pevts = get_read_chunk writes pevts in
       let (wr, ird, srd, urd), pevts = skip_incompatible writes pevts in
       let chunk = if ird then [] else chunk in
       if same_thread then begin
         if ird || urd then raise UnsatisfiableRead;
         if chunk = [] then [] else [chunk]
       end else if wr || srd then begin
         if urd then raise UnsatisfiableRead;
         if chunk = [] then List.rev chunks
         else List.rev (chunk :: chunks)
       end else (* ird or no more events *) begin assert (ird || pevts = []);
         if ird || chunk = [] then aux chunks pevts
         else aux (chunk :: chunks) pevts
       end
  in
  aux [] pevts

let read_chunks_by_thread_for_writes writes evts = (* evts by thread *)
  try
    let (wp, _, _, _), _ = HEvtMap.choose writes in
    if not (HEvtMap.for_all (fun (p, _, _, _) _ -> H.equal p wp) writes) then
      failwith "Invalid proc\n";
    let res = HMap.fold (fun p pevts rct ->
      let rc = read_chunks_for_writes (H.equal wp p) writes pevts in
      if rc = [] then rct else (p, rc) :: rct
    ) evts [] in
    res
  with Not_found -> []
      
let read_combs same_thread rl =
  let rec aux = function
  | [] -> failwith "Weakwrite.read_combs : internal error" (*[[]], []*)
  | [r] -> if same_thread then [[r]], [[r]] else [[r] ; []], [[r]]
  | r :: rl ->
     let combs, new_combs = aux rl in
     let combs, new_combs = List.fold_left (fun (combs, new_combs) nc ->
       let nc = (r :: nc) in
       nc :: combs, nc :: new_combs
     ) (if same_thread then [], [] else combs, []) new_combs in
     combs, new_combs
  in
  fst (aux rl)

let read_combs_by_thread_for_writes writes rct =
  try
    let (wp, _, _, _), _ = HEvtMap.choose writes in
    if not (HEvtMap.for_all (fun (p, _, _, _) _ -> H.equal p wp) writes) then
      failwith "Invalid proc\n";
    List.fold_left (fun rct (p, rc) ->
      let rc = List.fold_left (fun rc rl ->
        (read_combs (H.equal wp p) rl) @ rc
      ) [] rc in (* rc <- all read combinations for this thread *)
      (p, rc) :: rct (* source rc is a list of chunks *)
    ) [] rct
  with Not_found -> []

let read_combs_for_writes writes rct =
  List.fold_left (fun lrc (p, rcl) ->
    cartesian_product (fun rc1 rc2 -> rc1 @ rc2) lrc rcl
  ) [[]] rct (* if no combination, we want to keep the write *)
               (* we just say that it satisfies no reads *)

let all_combinations writes rcl =
  List.map (fun rc -> HEvtMap.fold (fun edw wtl wrc ->
    ((edw, wtl), List.filter (fun (_, (edr, _)) -> same_var edw edr) rc) :: wrc
  ) writes []) rcl





let mk_eq_true term =
  Atom.Comp (term, Eq, Elem (Term.htrue, Constr))

(* Build a predicate atom *)
let mk_pred pred pl =
  Atom.Comp (Access (pred, pl), Eq, Elem (Term.htrue, Constr))

let add_ghb_lt_atoms ghb sa =
  Weakrel.Rel.fold_lt (fun ef et sa ->
    SAtom.add (mk_pred hGhb [ef; et]) sa) ghb sa

let add_ghb_eq_atoms ghb sa =
  Weakrel.Rel.fold_eq (fun e1 e2 sa ->
    SAtom.add (mk_pred hSync [e1; e2]) sa) ghb sa




let make_read_write_combinations writes evts_bt urevts ghb =

  TimeBuildRW.start ();

  let wrcp = try
    let rct = read_chunks_by_thread_for_writes writes evts_bt in
    let rct = read_combs_by_thread_for_writes writes rct in
    let rcl = read_combs_for_writes writes rct in
    all_combinations writes rcl
  with UnsatisfiableRead -> [] in

  TimeBuildRW.pause ();

  TimeFilterRW.start ();

  (* let olen = List.length wrcp in *)
  (* Format.fprintf Format.std_formatter "Before : %d\n" (List.length wrcp); *)
  (* Format.print_flush (); *)

  (* Filter out combinations that lead to cyclic relations *)
  let wrcp = List.filter (fun wrcl ->

    (* Remove satisfied reads from unsatisfied set *)
    let urevts = List.fold_left (fun urevts ((wed, _), rcl) ->
      List.fold_left (fun urevts (re, ((p, d, v, vi), _)) ->
        HMap.remove re urevts) urevts rcl
    ) urevts wrcl in

    (* Adjust ghb for this combination *)
    let ghb = List.fold_left (fun ghb (((wp,_,_,_) as wed, (we,_,_)), rcl) ->
      let ghb = List.fold_left (fun ghb (re, (red, _)) -> (* rf *)
        if same_proc wed red then ghb
        else Weakrel.Rel.add_lt we re ghb
      ) ghb rcl in
      let ghb = HMap.fold (fun ure (ured, _) ghb -> (* fr *)
        if not (same_var wed ured) then ghb
        else Weakrel.Rel.add_lt ure we ghb
      ) urevts ghb in
      ghb
    ) ghb wrcl in (* should remember this ghb to avoid recomputing *)

    Weakrel.Rel.acyclic ghb
  ) wrcp in

  (* let nlen = List.length wrcp in *)
  (* if olen > 0 && nlen = 0 then *)
  (*   Format.fprintf Format.std_formatter "Reduced %d -> 0\n" olen; *)
  (* Format.fprintf Format.std_formatter "After : %d\n" (List.length wrcp); *)
  (* Format.print_flush (); *)

  TimeFilterRW.pause ();

  wrcp


    


let subst_event_val sfun sa =
  let rec process_t = function
    | Field (Field (Access (a, [e]), f), _) as t
         when H.equal a hE && H.equal f hVal -> sfun t e
    | Arith (t, c) ->
       let ntl = process_t t in
       begin match ntl with
       | [] -> failwith "Weakwrites.subst_event_val : ntl can't be empty"
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
          failwith "Weakwrites.subst_event_val : ntl can't be empty"
       | [nt1], [nt2] when nt1 == t1 && nt2 == t2 -> SAtom.add at sa
       | _, _ ->
          List.fold_left (fun sa nt1 ->
            List.fold_left (fun sa nt2 ->
              SAtom.add (Atom.Comp (nt1, op, nt2)) sa
            ) sa ntl2
          ) sa ntl1 (* ntl probably haev a single element *)
       end
    | Atom.Ite _ ->
       failwith "Weakwrite.subst_event_val : Ite should not be there"
    | _ -> SAtom.add at sa
  ) sa SAtom.empty



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

(* Build an event *)
let build_event e p d v vi = (* v in original form without _V *)
  let _, ret = Weakmem.weak_type v in
  (* let v = mk_hV v in *)
  let tevt = Access (hE, [e]) in
  let tval = Field (Field (tevt, hVal), mk_hT ret) in
  let athr = Atom.Comp (Field (tevt, hThr), Eq, Elem (p, Var)) in
  let adir = Atom.Comp (Field (tevt, hDir), Eq, Elem (d, Constr)) in
  let avar = Atom.Comp (Field (tevt, hVar), Eq, Elem (v, Constr)) in
  let sa, _ = List.fold_left (fun (sa, i) v ->
    SAtom.add (Atom.Comp (Field (tevt, mk_hP i), Eq, Elem (v, Var))) sa, i + 1
  ) (SAtom.add avar (SAtom.add adir (SAtom.singleton athr)), 1) vi in
  sa, tval





let satisfy_reads sa =

  TimeSatRead.start ();

  (* Format.eprintf "Node : %a\n" SAtom.print sa; *)

  let sa, rds, wts, fces, eids, evts = Weakevent.extract_events_set sa in
  let evts_bt = Weakevent.events_by_thread evts in
  let wevts = Weakevent.write_events evts in (* only for co/fr *)
  let urevts = Weakevent.unsat_read_events evts in (* to associate to wts *)
  let ffces, ghb = Weakrel.extract_rels_set sa in (* for acyclicity *)

    (* Format.eprintf "Evts :"; *)
    (* HMap.iter (fun e (ed, vals) -> *)
    (*   Format.eprintf " %a (%d)" H.print e (List.length vals); *)
    (* ) evts; *)
    (* Format.eprintf "\n"; *)
    (* Format.eprintf "Unsat rd :"; *)
    (* HMap.iter (fun e _ -> *)
    (*   Format.eprintf " %a" H.print e; *)
    (* ) urevts; *)
    (* Format.eprintf "\n"; *)





  let eids_before = eids in

  (* Instantiate write events, keep a map to values *)
  let iwts, sa, eids = HEvtMap.fold (fun (p, d, v, vi) vals (iwts, sa, eids) ->
    let eid, eids = fresh_eid eids p in
    let e = mk_hE eid in
    let na, tval = build_event e p d v vi in
    (HEvtMap.add (p, d, v, vi) (e, tval, vals) iwts, SAtom.union na sa, eids)
  ) wts (HEvtMap.empty, sa, eids) in

  (* Instantiate read events, keep a map to values *)
  let irds, sa, eids = HEvtMap.fold (fun (p, d, v, vi) vals (irds, sa, eids) ->
    let eid, eids = fresh_eid eids p in
    let e = mk_hE eid in
    let na, tval = build_event e p d v vi in
    (HEvtMap.add (p, d, v, vi) (e, tval, vals) irds, SAtom.union na sa, eids)
  ) rds (HEvtMap.empty, sa, eids) in

  (* Generate new fences (and remove older ones) *)
  let sa = List.fold_left (fun sa p ->
    let eid = max_proc_eid eids p in
    if eid <= 0 then sa else
      let sa = SAtom.filter (function
        | Atom.Comp (Access (a, [px; _]), Eq, Elem _)
        | Atom.Comp (Elem _, Eq, Access (a, [px; _]))
             when H.equal a hFence && H.equal p px -> false
        | _ -> true) sa in
      SAtom.add (mk_pred hFence [p; mk_hE eid]) sa
  ) sa fces in

  (* Generate sync for synchronous events (for reads : even on <> threads)*)
  let nsync_l = HMap.fold (fun _ peids sync ->
    IntSet.fold (fun eid sync -> (mk_hE eid) :: sync
  ) peids sync) (eid_diff eids eids_before) [] in
  let mk_sync l ghb = let rec aux ghb = function
    | [] | [_] -> ghb
    | e1 :: el ->
       let ghb = List.fold_left (fun ghb e2 ->
         Weakrel.Rel.add_eq e1 e2 ghb) ghb el in
       aux ghb el
  in aux ghb l in
  let nghb = mk_sync nsync_l ghb in





  (* Get first write on each var *) (* in weakevent *)
  let gfw = HMap.fold (fun we ((p, _, v, vi), _) gfw ->
    let vvi = v :: vi in
    let cwe = try HLMap.find vvi gfw with Not_found -> hE0 in
    if H.compare we cwe <= 0 then gfw
    else HLMap.add vvi we gfw
  ) wevts HLMap.empty in

  (* Get first read and first write of each thread *) (* in weakevent *)
  (* Writes and fences are grouped together for simplicity *)
  let freads, fwrites = HMap.fold (fun p pevts (freads, fwrites) ->
    let freads = try
        let (re, _) = List.find (fun (_, (ed, _)) -> is_read ed) pevts in
        HMap.add p re freads
      with Not_found -> freads in
    let fwrites = try
        let (we, _) = List.find (fun (_, (ed, _)) -> is_write ed) pevts in
        let cwe = try HMap.find p fwrites with Not_found -> hE0 in
        if H.compare we cwe >= 0 then HMap.add p we fwrites else fwrites
      with Not_found -> fwrites in
    freads, fwrites
  ) evts_bt (HMap.empty, ffces) in




  
  let add_ievts_rels rel ievts f =
    HEvtMap.fold (fun ied (ie, _, _) rel -> match f ied ie with
      | None -> rel | Some e -> Weakrel.Rel.add_lt ie e rel
    ) ievts rel in

  (* Add co from new writes to first old write on same variable *)
  let nghb = add_ievts_rels nghb iwts (fun (_, _, v, vi) _ ->
    try Some (HLMap.find (v :: vi) gfw) with Not_found -> None) in
  
  (* Add fr from new reads to first old write on same variable *)
  let nghb = add_ievts_rels nghb irds (fun (_, _, v, vi) _ ->
    try Some (HLMap.find (v :: vi) gfw) with Not_found -> None) in

  (* Add ppo from new reads to first old read of same thread *)
  let nghb = add_ievts_rels nghb irds (fun (p, _, _, _) _ ->
    try Some (HMap.find p freads) with Not_found -> None) in

  (* Add ppo from new reads to first old write of same thread *)
  let nghb = add_ievts_rels nghb irds (fun (p, _, _, _) _ ->
    try Some (HMap.find p fwrites) with Not_found -> None) in

  (* Add ppo/fence from new writes to first old write (or fence) *)
  (* However, if it's an atomic RMW, then consider first old read instead *)
  (* No need to split the RMW case if reads exists. But it might be useful
     in fact since we could add the lock prefix to the transition
     syntactically to avoir missing reads causing instr to be not locked *)
  let nghb = add_ievts_rels nghb iwts (fun (p, _, _, _) _ ->
    let fevts = if HEvtMap.is_empty irds then fwrites else freads in
    try Some (HMap.find p fevts) with Not_found -> None) in




  
  let rec subst_ievent ievts t = match t with
    | Read (p, v, vi) ->
       let _, tval, _ = HEvtMap.find (p, hR, mk_hV v, vi) ievts in
       tval
    | Arith (t, c) -> Arith (subst_ievent ievts t, c)
    | _ -> t in

  (* Substitute write values by instantiated read values *)
  let wts_iv = HEvtMap.map (fun (e, tval, vals) ->
    e, tval, List.map (fun t -> subst_ievent irds t) vals
  ) iwts in
 



  (* Build the relevant read-write combinations *)
  let wrcp = make_read_write_combinations wts_iv evts_bt urevts nghb in

let pres = if wrcp = [] then [] else begin



  (* Substitute read values by instantiated read values *)
  let rds_iv = HEvtMap.map (fun (e, tval, vals) ->
    e, tval, List.map (fun (cop, t) -> (cop, subst_ievent irds t)) vals
  ) irds in

  (* Add reads with their values (which may be reads too) *)
  let sa = HEvtMap.fold (fun pdvvi (e, lt, vals) sa ->
    List.fold_left (fun sa (cop, rt) ->
      let a = match cop with
        | CEq -> Atom.Comp (lt, Eq, rt)
        | CNeq -> Atom.Comp (lt, Neq, rt)
        | CLt -> Atom.Comp (lt, Lt, rt)
        | CLe -> Atom.Comp (lt, Le, rt)
        | CGt -> Atom.Comp (rt, Le, lt)
        | CGe -> Atom.Comp (rt, Lt, lt)
      in
      SAtom.add a sa
    ) sa vals
  ) rds_iv sa in

  (* Remove duplicate pairs of reads *)
  (* should find opposite affectations *)(*
  let reads = HEvtMap.filter (fun (p, d, v, vi) vals ->
    List.exists (fun (cop, t) ->
        match t with
        | Read (rp, rv, rvi) -> H.equal p rp H.equal v rv H.list_equal vi rvi
        | Arith (c, t) -> true
        | _ -> false
    ) vals
  ) rds in *)





  (* Update first write on each var *)
  let gfw' =  HEvtMap.fold (fun (p, _, v, vi) (we, _, _) gfw ->
    let vvi = v :: vi in
    let cwe = try HLMap.find vvi gfw with Not_found -> hE0 in
    if H.compare we cwe <= 0 then gfw
    else HLMap.add vvi we gfw
  ) iwts gfw in

  (* Update first reads by thread  *)
  let freads' = HEvtMap.fold (fun (p, _, _, _) (e, _, _) freads ->
    HMap.add p e freads
  ) irds freads in

  (* Update first fences by thread (considered as writes) *)
  let fwrites' = List.fold_left (fun ffces p ->
    let eid = max_proc_eid eids p in
    if eid <= 0 then ffces else
      HMap.add p (mk_hE eid) ffces
  ) fwrites fces in

  (* Update first writes by thread  *)
  let fwrites' = HEvtMap.fold (fun (p, _, _, _) (e, _, _) fwrites ->
    let cwe = try HMap.find p fwrites with Not_found -> hE0 in
    if H.compare e cwe >= 0 then HMap.add p e fwrites else fwrites
  ) iwts fwrites' in

  (* Make set of events to keep *)
  let keep = HSet.empty in
  let keep = HLMap.fold (fun _ e keep -> HSet.add e keep) gfw' keep in
  let keep = HMap.fold (fun _ e keep -> HSet.add e keep) freads' keep in
  let keep = HMap.fold (fun _ e keep -> HSet.add e keep) fwrites' keep in
  (* let keep = HEvtMap.fold (fun _ (e, _, _) keep -> HSet.add e keep) iwts keep in *)
  (* the last one should not be necessary *)
  (* We keep the following events, provided they are ghb-before an unsat read :
       1st W on each var          gfw'     (for other W on same var)
       1st R of each thread       freads'  (for R by same thread)
       1st W/F of each thread     fwrites' (for RW by same thread)
       all unsat R *)
  (* might have to keep writes sync with unsat reads for atomic RMW...
     otherwise it might give spurious unsafes *)




  (* Update the set of atoms *)
  let d = Weakrel.Rel.diff nghb ghb in
  let sa = add_ghb_lt_atoms d sa in
  let sa = add_ghb_eq_atoms d sa in
  let ghb = nghb in  




  
  (* Generate the atom sets for each combination *)
  let pres = List.fold_left (fun pres wrcl ->

    (* Substitute the satisfied read value with the write value *)
    let sa = List.fold_left (fun sa (((wp, _, wv, wvi), (_, _, wtl)), rcl) ->
      List.fold_left (fun sa (re, _) ->
        subst_event_val (fun t e -> if H.equal e re then wtl else [t]) sa
      ) sa rcl
    ) sa wrcl in

    (* Format.eprintf "Unsat rd :"; *)
    (* HMap.iter (fun e _ -> *)
    (*   Format.eprintf " %a" H.print e; *)
    (* ) urevts; *)
    (* Format.eprintf "\n"; *)

    (* Remove satisfied reads from unsatisfied reads *)
    let urevts = List.fold_left (fun urevts ((wed, _), rcl) ->
      List.fold_left (fun urevts (re, ((p, d, v, vi), _)) ->
        (* Format.eprintf "Sat rd : %a\n" H.print re; *)
        HMap.remove re urevts) urevts rcl
    ) urevts wrcl in
    
    (* Add rf/fr from new writes to old sat/unsat reads *)
    let nghb = List.fold_left (fun nghb ((wed, wtl), rcl) ->
      let e, _, _ = HEvtMap.find wed iwts in
      let nghb = List.fold_left (fun nghb (re, (red, _)) -> (* rf *)
        if same_proc wed red then nghb
        else Weakrel.Rel.add_lt e re nghb
      ) nghb rcl in
      let nghb = HMap.fold (fun re (red, _) ghb -> (* fr *) (* internal ? *)
        if not (same_var wed red) then ghb
        else Weakrel.Rel.add_lt re e ghb
      ) urevts nghb in
      nghb
    ) nghb wrcl in

    let d = Weakrel.Rel.diff nghb ghb in
    let sa = add_ghb_lt_atoms d sa in
    let ghb = nghb in

    (* Format.eprintf "Keep1 : "; *)
    (* HSet.iter (fun e -> Format.eprintf " %a " H.print e) keep; *)
    (* Format.eprintf "\n"; *)

    (* Add instantiated reads to unsatisfied reads *)
    let urevts = HEvtMap.fold (fun red (re, _, rvals) urevts ->
      HMap.add re (red, rvals) urevts
    ) irds urevts in

    (* Keep only events that are ghb-before or sync with an unsatisfied read *)
    let keep = HSet.filter (fun e ->
      HMap.exists (fun re (red, rvals) ->
        Weakrel.Rel.mem_lt e re ghb || Weakrel.Rel.mem_eq e re ghb) urevts
    ) keep in

    (* And add the unsatisfied reads *)
    let keep = HMap.fold (fun e _ keep ->
      HSet.add e keep) urevts keep in

    (* Here, remove events that do not satisfy criterion to stay *)
    (* Format.eprintf "Keep2 : "; *)
    (* HSet.iter (fun e -> Format.eprintf " %a " H.print e) keep; *)
    (* Format.eprintf "\n"; *)
    let sa = SAtom.filter (function
      | Atom.Comp (Access (a, [_; e]), _, _)
      | Atom.Comp (_, _, Access (a, [_; e]))
           when H.equal a hFence -> HSet.mem e keep
      | Atom.Comp (Access (a, [ef; et]), _, _)
      | Atom.Comp (_, _, Access (a, [ef; et]))
           when H.equal a hGhb || H.equal a hSync ->
             HSet.mem ef keep && HSet.mem et keep
      | Atom.Comp (Access (a, [ef; et]), _, _)
      | Atom.Comp (_, _, Access (a, [ef; et])) (* sync necessary for RMW *)
           when H.equal a hGhb (*|| H.equal a hSync *) ->
             not (HMap.mem et wevts ||
               HEvtMap.exists (fun _ (e, _, _) -> H.equal e et) iwts)
      | Atom.Comp (Field (Access (a, [e]), f), _, _)
      | Atom.Comp (_, _, Field (Access (a, [e]), f))
           when H.equal a hE && (H.equal f hVar || is_param f) ->
         HSet.mem e keep && (HLMap.exists (fun _ we -> H.equal e we) gfw' ||
           HMap.exists (fun re _ -> H.equal e re) urevts)
      | Atom.Comp (Field (Access (a, [e]), _), _, _)
      | Atom.Comp (_, _, Field (Access (a, [e]), _))
           when H.equal a hE -> HSet.mem e keep
      | Atom.Comp (t1, _, t2) ->
         let k1 = match t1 with
         | Field (Field (Access (a, [e]), _), _)
         | Arith (Field (Field (Access (a, [e]), _), _), _)
              when H.equal a hE -> HSet.mem e keep
         | _ -> true in
         let k2 = match t2 with
         | Field (Field (Access (a, [e]), _), _)
         | Arith (Field (Field (Access (a, [e]), _), _), _)
              when H.equal a hE -> HSet.mem e keep
         | _ -> true in
           k1 && k2
      | _ -> true
    ) sa in

    (* Simplify here in case adding reads added duplicates *)
    try (Cube.simplify_atoms sa) :: pres (* Cube.create_normal ? *)
    with Exit -> pres

  ) [] wrcp in pres

end in

  TimeSatRead.pause ();

  pres





let satisfy_unsatisfied_reads sa =
  
  let _, _, _, _, _, evts  = Weakevent.extract_events_set sa in
  let urevts = Weakevent.unsat_read_events evts in

  (* Satisfy unsat reads from init *)
  subst_event_val (fun _ e ->
    let (_, _, v, vi), _ = try HMap.find e urevts with Not_found -> (Format.fprintf Format.std_formatter "%a\n" H.print e; assert false) in
    let v = H.make (var_of_v v) in
    if vi = [] then [Elem (v, Glob)] else [Access (v, vi)]
  ) sa

(* should detect trivially unsatisfiable reads with const values from init *)
(* this requires the init state... *)
