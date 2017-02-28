
open Weakmem
open Types



(* Used internally by split_event *)
let find_event_safe eid evts =
  try H2Map.find eid evts with Not_found -> ((hNone, hNone, []), [])

(* Used internally by split_event *)
let rec split_event_t = function
  | Field (Field (Access (a, [p; e]), f), _)
       when H.equal a hE && H.equal f hVal ->
     Some (p, e), None
  | Arith (t, c) ->
     fst (split_event_t t), Some c
  | _ -> None, None

(* Used internally by split_event *)
let subs_const_from_term cs =
  let cs = Types.mult_const (-1) cs in
  function
  | Const c -> Const (Types.add_constants c cs)
  | Arith (t, c) -> Arith (t, Types.add_constants c cs)
  | t -> Arith (t, cs)

(* Used internally by split_event *)
let process_event eid c rev op tv evts = match eid with
  | Some eid ->
     let (ed, vals) = find_event_safe eid evts in
     let tv = match c with Some c -> subs_const_from_term c tv | _ -> tv in
     H2Map.add eid (ed, (rev, op, tv) :: vals) evts
  | None -> evts

let split_event at evts = match at with
  (* Direction / Variable / Indices *)
  | Atom.Comp (Field (Access (a, [p; e]), f), Eq, Elem (c, t))
  | Atom.Comp (Elem (c,t), Eq, Field (Access (a, [p; e]),f)) when H.equal a hE->
     let ((d, v, vi), vals) as evt = find_event_safe (p, e) evts in
     let evt = if H.equal f hDir then ((c, v, vi), vals)
	  else if H.equal f hVar then ((d, c, vi), vals)
	  else if is_param f then ((d, v, (f, c) :: vi), vals)
	  else evt in
     H2Map.add (p, e) evt evts
  (* Value *)
  | Atom.Comp (t1, op, t2) ->
     let eid1, c1 = split_event_t t1 in
     let eid2, c2 = split_event_t t2 in
     let evts = process_event eid1 c1 false op t2 evts in
     process_event eid2 c2 true op t1 evts
  (* Others *)
  | Atom.Ite _ ->
     failwith "Weakwrite.split_event : Ite should not be there"
  | _ -> evts



let events_by_thread sa =
  let evts = SAtom.fold split_event sa H2Map.empty in
  H2Map.fold (fun (p, e) (ed, vals) evts ->
    let pevts = try HMap.find p evts with Not_found -> [] in
    let pevts = ((p, e), (sort_params ed, vals)) :: pevts in
    HMap.add p pevts evts
  ) evts HMap.empty

let compatible_values wt op rt r = match wt, rt with
  | Const c1, Const c2 ->
      let c = Types.compare_constants c1 c2 in
      let c = if r then -c else c in
      if op = Eq && c <> 0 then false
      else if op = Neq && c = 0 then false
      else if op = Lt && c >= 0 then false
      else if op = Le && c > 0 then false
      else true
  | _ -> true

let split_read_chunk edw wtl pevts =
  let compat_val vals =
    List.for_all (fun wt ->
      List.for_all (fun (r, op, t) -> compatible_values wt op t r) vals
    ) wtl in
  let is_satisfied = function [] -> true | _ -> false in
  let rec aux chunk = function (* all reads should also be inter-compatible *)
    | [] -> List.rev chunk, []
    | ((_, (ed, vals)) as e) :: pevts ->
       if not (same_var edw ed) then aux chunk pevts
       else if not (is_read ed) || is_satisfied vals || not (compat_val vals)
         then List.rev chunk, pevts
       else aux (e :: chunk) pevts
  in
  aux [] pevts
	    
let read_chunks_for_write same_thread edw wtl pevts =
  let rec aux chunks = function
    | [] -> List.rev chunks
    | pevts ->
       let chunk, pevts = split_read_chunk edw wtl pevts in
       if same_thread then [chunk] else begin
        if chunk = [] then aux chunks pevts
        else aux (chunk :: chunks) pevts end
  in
  aux [] pevts

let read_chunks_by_thread_by_write writes evts = (* evts by thread *)
  List.fold_left (fun rctw ((wp, edw, wtl) as w) ->
    let rct = HMap.fold (fun p pevts rct ->
      let rc = read_chunks_for_write (H.equal wp p) edw wtl pevts in
      (p, rc) :: rct
    ) evts [] in
    (w, rct) :: rctw
  ) [] writes

let read_combs same_thread rl =
  let rec aux = function
  | [] -> []
  | [r] -> [[r]]
  | r :: rl ->
     let combs = aux rl in
     List.fold_left (fun combs c -> [r] :: (r :: c) :: combs)
		    (if same_thread then [] else combs) combs
  in
  aux rl

let read_combs_by_thread_by_write rctw =
  List.fold_left (fun rctw (((wp, _, _) as w), rct) ->
    let rct = List.fold_left (fun rct (p, rc) ->
      let rc = List.fold_left (fun rc rl ->
        (read_combs (H.equal wp p) rl) @ rc
      ) [] rc in (* rc <- all read combinations for this thread *)
      (p, rc) :: rct (* source rc is a list of chunks *)
    ) [] rct in
    (w, rct) :: rctw
  ) [] rctw

let read_combs_by_write rctw =
  List.fold_left (fun rcw (((wp, _, wt) as w), rct) ->
    let lrc = List.fold_left (fun lrc (p, rcl) ->
      List.fold_left (fun lrc crc ->
        List.fold_left (fun lrc rc ->
	  (rc @ crc) :: lrc
        ) lrc rcl
      ) lrc lrc
    ) [[]] rct in
    (w, lrc) :: rcw
  ) [] rctw

let all_combinations rcw =
  let make_combs combs w lrc cc =
    List.fold_left (fun combs rc ->
      ((w, rc) :: cc) :: combs
    ) combs lrc
  in
  let combs, rcw = match rcw with
    | [] -> [[]], []
    | (w, lrc) :: rcw -> make_combs [] w lrc [], rcw
  in
  List.fold_left (fun combs (w, lrc) ->
    List.fold_left (fun combs cc ->
      make_combs combs w lrc cc			  
    ) [] combs
  ) combs rcw
  
let make_read_write_combinations writes sa =
  let evts = events_by_thread sa in
  let rctw = read_chunks_by_thread_by_write writes evts in
  let rctw2 = read_combs_by_thread_by_write rctw in
  let rcw = read_combs_by_write rctw2 in
  let combs = all_combinations rcw in
  combs



let mk_eq_true term =
  Atom.Comp (term, Eq, Elem (Term.htrue, Constr))



let subst_event_val sfun sa =
  let rec process_t = function
    | Field (Field (Access (a, [p; e]), f), _) as t
         when H.equal a hE && H.equal f hVal ->
       sfun t (p, e)
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
       | [nt1], [nt2] when nt1 = t1 && nt2 = t2 -> SAtom.add at sa
       | _, _ ->
          List.fold_left (fun sa nt1 ->
            List.fold_left (fun sa nt2 ->
              SAtom.add (Atom.Comp (nt1, op, nt2)) sa
            ) sa ntl2
          ) sa ntl1
       end
    | Atom.Ite _ ->
       failwith "Weakwrite.subst_event_val : Ite should not be there"
    | _ -> SAtom.add at sa
  ) sa SAtom.empty



let satisfy_reads tri unsafe = (* unsafe without ites *)

  (* Extract writes with their values from unsafe *)
  let writes, unsafe = SAtom.partition (fun a -> match a with
    | Atom.Comp (Write _, op, _) | Atom.Comp (_, op, Write _) when op <> Eq ->
       failwith "Weakwrite.satisfy_reads : Write with op <> Eq"
    | Atom.Comp (Write _, _, _) | Atom.Comp (_, _, Write _) -> true
    | _ -> false
  ) unsafe in

  (* Transform writes to a more suitable form *)
(*  let writes = SAtom.fold (fun aw wl -> match aw with
    | Atom.Comp (Write (p, v, vi, []), Eq, t)
    | Atom.Comp (t, Eq, Write (p, v, vi, [])) ->
       (p, (hW, mk_hV v, vi), t) :: wl
    | _ -> failwith "Weakwrite.satisfy_reads : invalid Write"
  ) writes [] in*)
  let writes = SAtom.fold (fun aw wl -> match aw with
    | Atom.Comp (Write (p, v, vi, srl), Eq, t)
    | Atom.Comp (t, Eq, Write (p, v, vi, srl)) when srl <> [] ->
       failwith "Weakwrite.satisfy_reads : srl <> []"
    | Atom.Comp (Write (p, v, vi, []), Eq, t)
    | Atom.Comp (t, Eq, Write (p, v, vi, [])) ->
       let p_v_vi = p :: v :: vi in
       let tl = try HLMap.find p_v_vi wl with Not_found -> [] in
       HLMap.add p_v_vi (t :: tl) wl
    | _ -> failwith "Weakwrite.satisfy_reads : invalid Write"
  ) writes HLMap.empty in
  let writes = HLMap.fold (fun p_v_vi tl wl -> match p_v_vi with
    | p :: v :: vi -> (p, (hW, mk_hV v, vi), tl) :: wl
    | _ -> failwith "Weakwrite.satisfy_read : internal error"
  ) writes [] in
  
  (* Build the relevant read-write combinations *)
  let wrcp = make_read_write_combinations writes unsafe in

  (* Generate the atom sets for each combination *)
  List.fold_left (fun pres wrcl ->
    let unsafe = List.fold_left (fun unsafe ((wp, (_, wv, wvi), wtl), rcl) ->
      let unsafe = List.fold_left (fun unsafe ((rp, re), (_, _)) ->
        subst_event_val (fun t (p, e) ->
	  if H.equal p rp && H.equal e re then wtl else [t]) unsafe
      ) unsafe rcl in
      let srl = List.fold_left (fun srl (reid, _) -> reid :: srl) [] rcl in
      let wv = H.make (var_of_v wv) in
      SAtom.add (mk_eq_true (Write (wp, wv, wvi, srl))) unsafe
    ) unsafe wrcl in
    unsafe :: pres
  ) [] wrcp



let satisfy_unsatisfied_reads sa =

  (* Retrieve unsatisfied reads *)
  let evts = SAtom.fold split_event sa H2Map.empty in
  let ur = H2Map.fold (fun eid (ed, vals) ur ->
    if is_read ed && vals <> [] then
      H2Map.add eid (sort_params ed (* , vals *)) ur
    else ur
  ) evts H2Map.empty in

  (* Satisfy them from init *)
  let sa = subst_event_val (fun _ eid ->
    let (_, v, vi) = H2Map.find eid ur in
    let v = H.make (var_of_v v) in
    if vi = [] then [Elem (v, Glob)] else [Access (v, vi)]
  ) sa in

  (* Add the necessary rf's *)
  H2Map.fold (fun (p, e) _ sa ->
    SAtom.add (mk_eq_true (Access (hRf, [hP0; hE0; p; e]))) sa) ur sa

(* if a read takes a value from init, then a previous read to the same var must take its value from init *)
(* or : if a read takes it values from a non-init write, then a next read to the same var can not take its value from init *)
(* should detect trivially unsatisfiable reads with const values from init *)
(* this requires the init state... *)









(*let satisfy_reads tri unsafe = (* unsafe without ites *)

  (* Extract writes with their values from unsafe *)
  let writes, unsafe = SAtom.partition (fun a -> match a with
    | Atom.Comp (Write _, _, _) | Atom.Comp (_, _, Write _) -> true
    | _ -> false
  ) unsafe in

  (* Transform writes to a more suitable form *)
  let writes = SAtom.fold (fun aw wl -> match aw with
    | Atom.Comp (Write (p, v, vi, _), Eq, t)
    | Atom.Comp (t, Eq, Write (p, v, vi, _)) ->
       (p, (hW, mk_hV v, vi), t) :: wl
    | _ -> failwith "Weakwrite.satisfy_reads : internal error"
  ) writes [] in (* should check that srl is empty *)

  (* Build the relevant read-write combinations *)
  let wrcp = make_read_write_combinations writes unsafe in

  (* Generate the atom sets for each combination *)
  List.fold_left (fun pres wrcl ->
    let unsafe = List.fold_left (fun unsafe ((wp, (_, wv, wvi), wt), rcl) ->
      let unsafe = List.fold_left (fun unsafe ((rp, re), (_, _)) ->
        SAtom.fold (fun at unsafe -> match at, false, true with (*what if 2 same reads in atom?*)
	  | Atom.Comp (Field (Field (Access (a, [p;e]), f),_), op, rt), rev,_
	  | Atom.Comp (rt, op, Field (Field (Access (a, [p;e]), f),_)), _,rev
	     when H.equal a hE &&  H.equal f hVal &&
		  H.equal p rp && H.equal e re ->
               let arw = if rev then Atom.Comp (rt, op, wt)
		         else Atom.Comp (wt, op, rt) in
	       SAtom.add arw (unsafe)
	  | _ -> SAtom.add at unsafe
        ) unsafe SAtom.empty
      ) unsafe rcl in
      let srl = List.fold_left (fun srl (reid, _) -> reid :: srl) [] rcl in
      let wv = H.make (var_of_v wv) in
      SAtom.add (mk_eq_true (Write (wp, wv, wvi, srl))) unsafe
    ) unsafe wrcl in
    unsafe :: pres
  ) [] wrcp*)






(*let satisfy_unsatisfied_reads sa =
  let ur = unsatisfied_reads sa in
  let rec process_t = function
    | Field (Field (Access (a, [p; e]), f), _)
         when H.equal a hE && H.equal f hVal ->
       let (_, v, vi) = H2Map.find (p, e) ur in
       let v = H.make (var_of_v v) in
       if vi = [] then Elem (v, Glob) else Access (v, vi)
    | Arith (t, c) ->
       let nt = process_t t in
       if nt == t then nt else Arith (nt, c)
    | t -> t
  in
  let sa = SAtom.fold (fun at sa -> match at with
    | Atom.Comp (t1, op, t2) ->
       let nt1 = process_t t1 in
       let nt2 = process_t t2 in
       if nt1 == t1 && nt2 == t2 then SAtom.add at sa
       else SAtom.add (Atom.Comp (nt1, op, nt2)) sa
    | Atom.Ite _ ->
       failwith "Weakwrite.satisfy_unsatisfied_reads : Ite should not be there"
    | _ -> SAtom.add at sa
  ) sa SAtom.empty
  in
  H2Map.fold (fun (p, e) _ sa ->
    SAtom.add (mk_eq_true (Access (hRf, [hP0; hE0; p; e]))) sa) ur sa*)






             
(*  SAtom.fold (fun at sa -> match at, false, true with
    (* WARNING : handle the case where both sides are events ! *)
    | Atom.Comp (Field (Field (Access (a, [p; e]), f), _), op, rt), rev, _
    | Atom.Comp (rt, op, Field (Field (Access (a, [p; e]), f), _)), _, rev
       when H.equal a hE && H.equal f hVal ->
         let (d, v, vi) = H2Map.find (p, e) ur in
         let wt = make_init_write (v, vi) in
         let arw = if rev then Atom.Comp (rt, op, wt)
		   else Atom.Comp (wt, op, rt) in
	 let arf = Atom.Comp (Access (hRf, [hP0; hE0; p; e]), Eq, eTrue) in
	 SAtom.add arf (SAtom.add arw sa)
  ) sa SAtom.empty*)
