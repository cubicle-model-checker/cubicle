
open Weakmem
open Types



(* Used internally by split_event *)
let find_event_safe eid evts =
  try H3Map.find eid evts
  with Not_found -> (hNone, hNone, [], [])

(* Used internally by split_event *)
let rec split_event_t = function
  | Field (Field (Access (a, [p; e; s]), f), _)
       when H.equal a hE && H.equal f hVal ->
     Some (p, e, s), None
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
     let (d, v, vi, vals) = find_event_safe eid evts in
     let tv = match c with Some c -> subs_const_from_term c tv | _ -> tv in
     H3Map.add eid (d, v, vi, (rev, op, tv) :: vals) evts
  | None -> evts

let split_event at evts = match at with
  (* Direction / Variable / Indices *)
  | Atom.Comp (Field (Access (a, [p; e; s]), f), Eq, Elem (c, t))
  | Atom.Comp (Elem (c, t), Eq, Field (Access (a, [p; e; s]), f))
       when H.equal a hE ->
     let (d, v, vi, vals) as evt = find_event_safe (p, e, s) evts in
     let evt = if H.equal f hDir then (c, v, vi, vals)
	  else if H.equal f hVar then (d, c, vi, vals)
	  else if is_param f then (d, v, (f, c) :: vi, vals)
	  else evt in
     H3Map.add (p, e, s) evt evts
  (* Value *)
  | Atom.Comp (t1, op, t2) ->
     let eid1, c1 = split_event_t t1 in
     let eid2, c2 = split_event_t t2 in
     let evts = process_event eid1 c1 false op t2 evts in
     process_event eid2 c2 true op t1 evts
  (* Others *)
  | _ -> evts



let events_by_thread sa =
  let evts = SAtom.fold split_event sa H3Map.empty in
  H3Map.fold (fun (p, e, s) (d, v, vi, vals) evts ->
    let pevts = try HMap.find p evts with Not_found -> [] in
    let vi = List.map (fun (_, i) -> i) (Weakutil.sort_hplist vi) in
    let pevts = ((p, e, s), (d, v, vi, vals)) :: pevts in
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

let split_read_chunk (_, wv, wvi, wt) pevts =
  let wv = mk_hV wv in
  let is_read (_, (d, _, _, _)) = H.equal d hR in
  let same_var (_, (d, v, vi, _)) = Weakmem.same_var (d, wv, wvi) (d, v, vi) in
  let compat_val (_, (_, _, _, vals)) =    
    List.for_all (fun (r, op, t) -> compatible_values wt op t r) vals
  in
  let is_satisfied (_, (_, _, _, vals)) = match vals with
    | [] -> true
    | _ -> false
  in
  let rec aux chunk = function (* all reads should also be inter-compatible *)
    | [] -> List.rev chunk, []
    | e :: pevts ->
       if not (same_var e) then aux chunk pevts
       else if not (is_read e) || is_satisfied e || not (compat_val e) then
	 List.rev chunk, pevts
       else aux (e :: chunk) pevts
  in
  aux [] pevts
	    
let read_chunks_for_write same_thread w pevts =
  let wp, wv, wvi, wt = w in
  let rec aux chunks = function
    | [] -> List.rev chunks
    | pevts ->
       let chunk, pevts = split_read_chunk w pevts in
       if same_thread then [chunk] else begin
        if chunk = [] then aux chunks pevts
        else aux (chunk :: chunks) pevts end
  in
  aux [] pevts

let read_chunks_by_thread_by_write writes evts = (* evts by thread *)
  List.fold_left (fun rctw ((wp, wv, wvi, wt) as w) ->
    let rct = HMap.fold (fun p pevts rct ->
      let rc = read_chunks_for_write (H.equal wp p) w pevts in
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
  List.fold_left (fun rctw (((wp, _, _, _) as w), rct) ->
    let rct = List.fold_left (fun rct (p, rc) ->
      let rc = List.fold_left (fun rc rl ->
        (read_combs (H.equal wp p) rl) @ rc
      ) [] rc in (* rc <- all read combinations for this thread *)
      (p, rc) :: rct (* source rc is a list of chunks *)
    ) [] rct in
    (w, rct) :: rctw
  ) [] rctw

let read_combs_by_write rctw =
  List.fold_left (fun rcw (((wp, wv, wi, wt) as w), rct) ->
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



let eTrue = Elem (Term.htrue, Constr)



let satisfy_reads tri unsafe = (* unsafe without ites *)

  let writes, unsafe = SAtom.partition (fun a -> match a with
    | Atom.Comp (Write _, _, _) | Atom.Comp (_, _, Write _) -> true
    | _ -> false
  ) unsafe in

  let writes = SAtom.fold (fun aw wl -> match aw with
    | Atom.Comp (Write (p, v, vi, _), Eq, t)
    | Atom.Comp (t, Eq, Write (p, v, vi, _)) -> (p, v, vi, t) :: wl
    | _ -> failwith "Weakwrite.satisfy_read : internal error"
  ) writes [] in

  let wrcp = make_read_write_combinations writes unsafe in

  List.fold_left (fun pres wrcl ->
    let unsafe = List.fold_left (fun unsafe ((wp, wv, wvi, wt), rcl) ->
      let unsafe = List.fold_left (fun unsafe ((rp, re, rs), (_, _, rvi, _)) ->
        SAtom.fold (fun at unsafe -> match at, false, true with (*what if 2 same reads in atom?*)
	  | Atom.Comp (Field (Field (Access (a, [p;e;s]), f),_), op, rt), rev,_
	  | Atom.Comp (rt, op, Field (Field (Access (a, [p;e;s]), f),_)), _,rev
	     when H.equal a hE &&  H.equal f hVal &&
		  H.equal p rp && H.equal e re && H.equal s rs ->
               let arw = if rev then Atom.Comp (rt, op, wt)
		         else Atom.Comp (wt, op, rt) in
	       SAtom.add arw (unsafe)
	  | _ -> SAtom.add at unsafe
        ) unsafe SAtom.empty
      ) unsafe rcl in
      let srl = List.fold_left (fun srl (reid, _) -> reid :: srl) [] rcl in
      SAtom.add (Atom.Comp (Write (wp, wv, wvi, srl), Eq, eTrue)) unsafe
    ) unsafe wrcl in
    unsafe :: pres
  ) [] wrcp



let unsatisfied_reads sa =
  let evts = SAtom.fold split_event sa H3Map.empty in (* params should be in order*)
  let ur = H3Map.fold (fun eid (d, v, vi, vals) ur ->
    if d = hR && vals <> [] then
      H3Map.add eid (v, List.map (fun (_, i) -> i) vi) ur
    else ur
  ) evts H3Map.empty in
  ur

let satisfy_unsatisfied_reads sa =
  let ur = unsatisfied_reads sa in
  (* could detect trivially unsatisfiable reads *)
  SAtom.fold (fun at sa -> match at, false, true with
    (* WARNING : handle the case where both sides are events ! *)
    | Atom.Comp (Field (Field (Access (a, [p; e; s]), f), _), op, rt), rev, _
    | Atom.Comp (rt, op, Field (Field (Access (a, [p; e; s]), f), _)), _, rev
       when H.equal a hE && H.equal f hVal ->
         let (v, vi) = H3Map.find (p, e, s) ur in
         let ((wp, we, ws), wt, na) = Weakevent.make_init_write (v, vi) in
         let arw = if rev then Atom.Comp (rt, op, wt)
		   else Atom.Comp (wt, op, rt) in
	 let arf = Atom.Comp (Access (hRf, [wp;we;ws;p;e;s]), Eq, eTrue) in
	 SAtom.add arf (SAtom.add arw (SAtom.union na sa))
    | _ -> SAtom.add at sa
  ) sa SAtom.empty


