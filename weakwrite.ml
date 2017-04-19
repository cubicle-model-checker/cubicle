
open Weakmem
open Weakevent
open Types
open Util

exception UnsatisfiableRead


(*
(* Used internally by split_event *)
let find_event_safe e evts =
  try HMap.find e evts with Not_found -> ((hNone, hNone, hNone, []), [])

(* Used internally by split_event *)
let rec split_event_val_t = function
  | Field (Field (Access (a, [e]), f), _)
     when H.equal a hE && H.equal f hVal -> Some e, None
  | Arith (t, c) -> fst (split_event_val_t t), Some c
  | _ -> None, None

(* Used internally by split_event *)
let subs_const_from_term cs =
  let cs = Types.mult_const (-1) cs in
  function
  | Const c -> Const (Types.add_constants c cs)
  | Arith (t, c) -> Arith (t, Types.add_constants c cs)
  | t -> Arith (t, cs)

(* Used internally by split_event *)
let process_event e c cop tv evts = match e with
  | Some e ->
     let (ed, vals) = find_event_safe e evts in
     let tv = match c with Some c -> subs_const_from_term c tv | _ -> tv in
     HMap.add e (ed, (cop, tv) :: vals) evts
  | None -> evts

let split_event at evts = match at with
  (* Direction / Variable / Indices *)
  | Atom.Comp (Field (Access (a, [e]), f), Eq, Elem (c, t))
  | Atom.Comp (Elem (c, t), Eq, Field (Access (a, [e]), f)) when H.equal a hE ->
     let ((p, d, v, vi), vals) as evt = find_event_safe e evts in
     let evt = if H.equal f hThr then ((c, d, v, vi), vals)
          else if H.equal f hDir then ((p, c, v, vi), vals)
	  else if H.equal f hVar then ((p, d, c, vi), vals)
	  else if is_param f then ((p, d, v, (f, c) :: vi), vals)
	  else evt in
     HMap.add e evt evts
  (* Value *)
  | Atom.Comp (t1, op, t2) ->
     let e1, c1 = split_event_val_t t1 in
     let e2, c2 = split_event_val_t t2 in
     let evts = process_event e1 c1 (cop_of_r_op false op) t2 evts in
     process_event e2 c2 (cop_of_r_op true op) t1 evts
  (* Others *)
  | Atom.Ite _ ->
     failwith "Weakwrite.split_event : Ite should not be there"
  | _ -> evts

let events_by_thread sa =
  let evts = SAtom.fold split_event sa HMap.empty in
  HMap.fold (fun e ((p, d, v, vi) as ed, vals) evts ->
    let pevts = try HMap.find p evts with Not_found -> [] in
    let pevts = (e, (sort_params ed, vals)) :: pevts in
    HMap.add p pevts evts
  ) evts HMap.empty
 *)



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
       | Some (edw, wtl) ->
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
       | Some (edw, wtl) ->
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

let events_by_thread evts = (* by chance, this sorts event in correct order *)
  HMap.fold (fun e ((p, _, _, _) as ed, vals) evts ->
    let pevts = try HMap.find p evts with Not_found -> [] in
    let pevts = (e, (ed, vals)) :: pevts in
    HMap.add p pevts evts
  ) evts HMap.empty

let make_read_write_combinations writes reads evts wevts urevts rels =
  try
    TimeBuildRW.start ();

    let evts_bt = events_by_thread evts in
    let rct = read_chunks_by_thread_for_writes writes evts_bt in
    let rct = read_combs_by_thread_for_writes writes rct in
    let rcl = read_combs_for_writes writes rct in
    let wrcp = all_combinations writes rcl in

    TimeBuildRW.pause ();

    (* Build the ghb relation *)
    let ghb = Weakrel.make_ghb evts rels in
    (* let scloc = Weakorder.make_scloc evts rels in *)

    (* Extract fences and sync from rels *)
    let (f, _, _, _, _, _, sync) = rels in

    (* Get first fence of each thread *)
    let ffces = HMap.map (fun pfences -> HSet.max_elt pfences) f in

    (* Get first event and first write of each thread *)
    let fevts, fwrites = HMap.fold (fun p pevts (fevts, fwrites) ->
      let fevts = match pevts with
        | [] -> fevts
        | (e, _) :: _ -> HMap.add p e fevts
      in
      let fwrites = try
        let (we, _) = List.find (fun (e, (ed, _)) -> is_write ed) pevts in
        HMap.add p we fwrites
      with Not_found -> fwrites in
      fevts, fwrites
    ) evts_bt (HMap.empty, HMap.empty) in

(*
    let manip = List.fold_left (fun manip (ed, _) ->
      ed :: manip) reads writes in
    
    let is_manip manip ed =
      List.exists (fun med -> same_var ed med) manip in
 *)
    (* TODO : restrict ghb & wevts/urevts to manipualated only *)
    

    let add_rel_aux rel nef net =
      let pre = H2Set.filter (fun (_, et) -> H.equal et nef) rel in
      let post = H2Set.filter (fun (ef, _) -> H.equal net ef) rel in
      let pre = H2Set.add (nef, net) pre in
      let post = H2Set.add (nef, net) post in
      H2Set.fold (fun (ef, _) rel ->
        H2Set.fold (fun (_, et) rel ->
          H2Set.add (ef, et) rel
        ) post rel
      ) pre rel
    in

    let add_rel rel nef net =
      let sef = try List.find (HSet.mem nef) sync
        with Not_found -> HSet.singleton nef in
      let set = try List.find (HSet.mem net) sync
        with Not_found -> HSet.singleton net in
      HSet.fold (fun nef rel ->
        HSet.fold (fun net rel ->
          add_rel_aux rel nef net
        ) set rel
      ) sef rel
    in

    let acyclic rel =
      not (H2Set.exists (fun (e1a, e2a) ->
        H2Set.exists (fun (e1b, e2b) ->
          H.equal e1a e2b && H.equal e2a e1b
        ) rel
      ) rel)
    in
    
    (* Add fr from new reads to old writes *)
    let ghb = HEvtMap.fold (fun red _ ghb -> (* fr *)
      let re = hE0 in
      let ghb = HMap.fold (fun we (wed, _) ghb ->
        if not (same_var red wed) then ghb
        else begin
          (* Format.fprintf Format.std_formatter "fr : %a -> %a\n" *)
          (*   H.print re H.print we; *)
          add_rel ghb re we
        end
      ) wevts ghb in
      ghb
    ) reads ghb in

    (* Add co from new writes to old writes *)
    let ghb = HEvtMap.fold (fun wed _ ghb -> (* co *)
      let we = hE0 in
      let ghb = HMap.fold (fun we2 (wed2, _) ghb ->
        if not (same_var wed wed2) then ghb
        else begin
          (* Format.fprintf Format.std_formatter "co : %a -> %a\n" *)
          (*   H.print we H.print we2; *)
          add_rel ghb we we2
        end
      ) wevts ghb in
      ghb
    ) writes ghb in

    (* Add fence from new writes to old reads separated by fence *)
    let ghb = HEvtMap.fold (fun (wp, _, _, _) _ ghb -> (* fence *)
      let we = hE0 in
      let ghb = try let fe = HMap.find wp ffces in
                     let ghb = add_rel ghb we fe in
                     (* Format.fprintf Format.std_formatter "f : %a -> %a\n" *)
                     (*   H.print we H.print fe; *)
                     ghb
                 with Not_found -> ghb in
      ghb
    ) writes ghb in

    (* Add ppo from new reads to first old event *)
    let ghb = HEvtMap.fold (fun (rp, _, _, _) _ ghb -> (* ppo *)
      let re = hE0 in
      let ghb = try let fe = HMap.find rp fevts in
                     let ghb = add_rel ghb re fe in
                     (*Format.fprintf Format.std_formatter "ppo : %a -> %a\n" *)
                     (*   H.print re H.print fe; *)
                     ghb
                 with Not_found -> ghb in
      ghb
    ) reads ghb in

    (* Add ppo from new writes to first old write *)
    let ghb = HEvtMap.fold (fun (wp, _, _, _) _ ghb -> (* ppo *)
      let we = hE0 in
      let ghb = try let fe = HMap.find wp fwrites in
                     let ghb = add_rel ghb we fe in
                     (*Format.fprintf Format.std_formatter "ppo : %a -> %a\n" *)
                     (*   H.print we H.print fe; *)
                     ghb
                 with Not_found -> ghb in
      ghb
    ) writes ghb in

    TimeFilterRW.start ();

    (* Format.fprintf Format.std_formatter "Before : %d\n" (List.length wrcp);*)

    (* Filter out combinations that lead to cyclic relations *)
    let wrcp = List.filter (fun wrcl ->

      let urevts = List.fold_left (fun urevts ((wed, _), rcl) ->
        List.fold_left (fun urevts (re, ((p, d, v, vi), _)) ->
          HMap.remove re urevts) urevts rcl
      ) urevts wrcl in

      let ghb = List.fold_left (fun ghb (((wp, _, _, _) as wed, _), rcl) ->
        let we = hE0 in
        let ghb = List.fold_left (fun ghb (re, _) -> (* rf *)
          (* Format.fprintf Format.std_formatter "rf : %a -> %a\n" *)
          (*                H.print we H.print re; *)
	  add_rel ghb we re
        ) ghb rcl in
        let ghb = HMap.fold (fun ure (ured, _) ghb -> (* fr *)
          if not (same_var wed ured) then ghb
          else begin
              (* Format.fprintf Format.std_formatter "fr : %a -> %a\n" *)
              (*                H.print ure H.print we; *)
              add_rel ghb ure we
            end
        ) urevts ghb in
        ghb
      ) ghb wrcl in

      (* if acyclic ghb then begin *)
      (*   Format.fprintf Format.std_formatter "Node : %a\n" SAtom.print sa; *)
      (*   Format.fprintf Format.std_formatter "Ghb : "; *)
      (*   H2Set.iter (fun (ef, et) -> *)
      (*     Format.fprintf Format.std_formatter "%a < %a  " H.print ef H.print et *)
      (*   ) ghb; *)
      (*   Format.fprintf Format.std_formatter "\n" *)
      (* end; *)

      acyclic ghb
    ) wrcp in

    (* Format.fprintf Format.std_formatter "After : %d\n" (List.length wrcp); *)

    TimeFilterRW.pause ();

    wrcp
  with UnsatisfiableRead -> []



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

let mk_eq_true term =
  Atom.Comp (term, Eq, Elem (Term.htrue, Constr))

(* Build a predicate atom *)
let mk_pred pred pl =
  Atom.Comp (Access (pred, pl), Eq, Elem (Term.htrue, Constr))

let satisfy_reads tri sa =

  TimeSatRead.start ();

  let saX, rds, wts, fces, eids, evts = Weakevent.extract_events_set sa in

  let wevts = Weakevent.write_events evts in
  let urevts = Weakevent.unsat_read_events evts in
  let _, rels = Weakrel.extract_rels_set evts sa in

  (* Remove writes with their values from unsafe *)
  let _, sa = SAtom.partition (fun a -> match a with
    | Atom.Comp (Write (_, _, _, []), Eq, _)
    | Atom.Comp (_, Eq, Write (_, _, _, [])) -> true
    | Atom.Comp (Write _, _, _) | Atom.Comp (_, _, Write _) ->
       failwith "Weakwrite.satisfy_reads : invalid Write"
    | _ -> false
  ) sa in

  (* Build the relevant read-write combinations *)
  let wrcp = make_read_write_combinations wts rds evts wevts urevts rels in
(*
  let eids_before = eids in

  (* Instantiate write events, keep a map to values *)
  let iwts, sa, eids = HEvtMap.fold (fun (p, d, v, vi) _ (iwts, sa, eids) ->
    let eid, eids = fresh_eid eids p in
    let e = mk_hE eid in
    let na, tval = build_event e p d v vi in
    (HEvtMap.add (p, d, v, vi) (e, tval) iwts, SAtom.union na sa, eids)
  ) wts (HEvtMap.empty, sa, eids) in

  (* Instantiate read events, keep a map to values *)
  let irds, sa, eids = HEvtMap.fold (fun (p, d, v, vi) _ (irds, sa, eids) ->
    let eid, eids = fresh_eid eids p in
    let e = mk_hE eid in
    let na, tval = build_event e p d v vi in
    (HEvtMap.add (p, d, v, vi) (e, tval) irds, SAtom.union na sa, eids)
  ) rds (HEvtMap.empty, sa, eids) in

  (* Generate fences *)
  let sa = List.fold_left (fun sfa p ->
    let eid = max_proc_eid eids p in
    if eid <= 0 then sfa else
    SAtom.add (mk_pred hFence [p; mk_hE eid]) sfa
  ) sa fces in

  (* Generate sync for synchronous events (for reads : even on <> threads)*)
  let mk_sync eid_range = HMap.fold (fun _ peids sync ->
    IntSet.fold (fun eid sync -> (mk_hE eid) :: sync
  ) peids sync) eid_range [] in
  let mk_sync_sa sync = match sync with [] | [_] -> SAtom.empty | _ ->
    SAtom.singleton (mk_pred hSync (List.rev sync)) in
  let sa = SAtom.union sa (mk_sync_sa (mk_sync (eid_diff eids eids_before))) in


  let rec subst_ievent ievts t = match t with
    | Read (p, v, vi) -> snd (HEvtMap.find (p, hR, mk_hV v, vi) ievts)
    | Arith (t, c) -> Arith (subst_ievent ievts t, c)
    | _ -> t
  in

  (* Substitute write values by instantiated read values *)
  let wts_iv = HEvtMap.map (fun vals ->
    List.map (fun t -> subst_ievent irds t) vals
  ) wts in
 
  (* Substitute read values by instantiated read values *)
  let rds_iv = HEvtMap.map (fun vals ->
    List.map (fun (cop, t) -> (cop, subst_ievent irds t)) vals              
  ) rds in

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
 *)

  (* Could add relations that are already known *)

  (* Generate the atom sets for each combination *)
  let res = List.fold_left (fun pres wrcl ->
    let sa = List.fold_left (fun sa (((wp, _, wv, wvi), wtl), rcl) ->
      let sa = List.fold_left (fun sa (re, _) ->
        subst_event_val (fun t e -> if H.equal e re then wtl else [t]) sa
      ) sa rcl in
      let srl = List.fold_left (fun srl (re, _) -> re :: srl) [] rcl in
      let wv = H.make (var_of_v wv) in
      SAtom.add (mk_eq_true (Write (wp, wv, wvi, srl))) sa (* remove *)
    ) sa wrcl in

    (* let sa = List.fold_left (fun sa (((wp, _, wv, wvi), wtl), rcl) -> *)
    (*   let wtl = List.map (subst_ievent irds) wtl in *)
    (*   List.fold_left (fun sa (re, _) -> *)
    (*     subst_event_val (fun t e -> if H.equal e re then wtl else [t]) sa *)
    (*   ) sa rcl *)
    (* ) sa wrcl in *)

    try
(*
      (* Add reads with their values (which may be reads too) *)
      let sa = HEvtMap.fold (fun pdvvi vals sa ->
        let (_, lt) = HEvtMap.find pdvvi irds in
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

      (* Remove satisfied reads from unsatisfied reads *)
      let urevts = List.fold_left (fun urevts ((wed, _), rcl) ->
        List.fold_left (fun urevts (re, ((p, d, v, vi), _)) ->
          HMap.remove re urevts) urevts rcl
      ) urevts wrcl in

      (* Add relations impling new writes (rf, fr, co) *)
      let sa = List.fold_left (fun sa ((ed, wtl), rcl) ->
        let e, _ = HEvtMap.find ed iwts in
        let sa = List.fold_left (fun sa (re, _) -> (* rf *)
	  SAtom.add (mk_pred hRf [e; re]) sa
        ) sa rcl in
        let sa = HMap.fold (fun we (wed, _) sa -> (* co *)
          if not (same_var ed wed) then sa
          else SAtom.add (mk_pred hCo [e; we]) sa
        ) wevts sa in
        let sa = HMap.fold (fun re (red, _) sa -> (* fr *)
          if not (same_var ed red) then sa
          else SAtom.add (mk_pred hFr [re; e]) sa
        ) urevts sa in
        sa
      ) sa wrcl in

      (* Add relations impling new reads (fr) *)
      let sa = HEvtMap.fold (fun ed (e, _) sa ->
        let sa = HMap.fold (fun we (wed, _) sa -> (* fr *)
          if not (same_var ed wed) then sa
          else SAtom.add (mk_pred hFr [e; we]) sa
        ) wevts sa in
        sa
      ) irds sa in
 *) 
      (* Simplify here in case adding reads added duplicates *)
      let sa = Cube.simplify_atoms sa in (* Cube.create_normal ? *)
      let sa = Weakpre.instantiate_events sa in

      sa  :: pres
    with Exit -> pres
  ) [] wrcp in

  TimeSatRead.pause ();

  res



let satisfy_unsatisfied_reads sa =
  
  let _, _, _, _, _, evts  = Weakevent.extract_events_set sa in
  let urevts = Weakevent.unsat_read_events evts in

  (* Satisfy unsat reads from init *)
  let sa = subst_event_val (fun _ e ->
    let (_, _, v, vi), _ = HMap.find e urevts in
    let v = H.make (var_of_v v) in
    if vi = [] then [Elem (v, Glob)] else [Access (v, vi)]
  ) sa in

  sa

(* no need to add rf / co anymore : fri is built during pre,
   so cycles are detected before, if any *)

(* should detect trivially unsatisfiable reads with const values from init *)
(* this requires the init state... *)
