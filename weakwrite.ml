
open Weakmem
open Weakevent
open Types
open Util

exception UnsatisfiableRead



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


open Weakpre
            
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

let mk_eq_true term =
  Atom.Comp (term, Eq, Elem (Term.htrue, Constr))

let satisfy_reads tri unsafe = (* unsafe without ites *)

  TimeSatRead.start ();

  let sa_pure, rds, wts, fces, eids, evts, wevts, urevts =
    Weakevent.extract_events_set unsafe in

  let _, rels = Weakrel.extract_rels_set evts unsafe in

  (* Remove writes with their values from unsafe *)
  let _, unsafe = SAtom.partition (fun a -> match a with
    | Atom.Comp (Write (_, _, _, []), Eq, _)
    | Atom.Comp (_, Eq, Write (_, _, _, [])) -> true
    | Atom.Comp (Write _, _, _) | Atom.Comp (_, _, Write _) ->
       failwith "Weakwrite.satisfy_reads : invalid Write"
    | _ -> false
  ) unsafe in

  (* Build the relevant read-write combinations *)
  let wrcp = make_read_write_combinations wts rds evts wevts urevts rels in

  (* Generate the atom sets for each combination *)
  let res = List.fold_left (fun pres wrcl ->
    let unsafe = List.fold_left (fun unsafe (((wp, _, wv, wvi), wtl), rcl) ->
      let unsafe = List.fold_left (fun unsafe (re, _) ->
        subst_event_val (fun t e ->
          if H.equal e re then wtl else [t]) unsafe
      ) unsafe rcl in
      let srl = List.fold_left (fun srl (re, _) -> re :: srl) [] rcl in
      let wv = H.make (var_of_v wv) in
      SAtom.add (mk_eq_true (Write (wp, wv, wvi, srl))) unsafe
    ) unsafe wrcl in
    try
      let np = Cube.simplify_atoms unsafe in
      let np = Weakpre.instantiate_events np in
      np  :: pres
    with Exit -> pres
  ) [] wrcp in

  (* Cube.create_normal ? *)

  TimeSatRead.pause ();

  res


    
let satisfy_unsatisfied_reads sa =
  
  (* Retrive all events *)
  let evts = SAtom.fold split_event sa HMap.empty in

  (* Retrieve unsatisfied reads *)
  let ur = HMap.fold (fun e ((p, d, v, vi) as ed, vals) ur ->
    if is_read ed && vals <> [] then
      HMap.add e (sort_params ed) ur
    else ur
  ) evts HMap.empty in

  (* Satisfy unsat reads from init *)
  let sa = subst_event_val (fun _ e ->
    let (_, _, v, vi) = HMap.find e ur in
    let v = H.make (var_of_v v) in
    if vi = [] then [Elem (v, Glob)] else [Access (v, vi)]
  ) sa in

  sa

(* no need to add rf / co anymore : fri is built during pre,
   so cycles are detected before, if any *)

(* should detect trivially unsatisfiable reads with const values from init *)
(* this requires the init state... *)
