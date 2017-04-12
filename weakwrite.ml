
open Weakmem
open Types

exception UnsatLocalWeakRead

type cop = CEq | CNeq | CLt | CLe | CGt | CGe

let cop_of_r_op r op =
  let open Types in
  match r, op with
  | _, Eq -> CEq
  | _, Neq -> CNeq
  | false, Lt -> CLt
  | false, Le -> CLe
  | true, Lt -> CGe
  | true, Le -> CGt

let string_of_cop = function
  | CEq -> "="
  | CNeq -> "<>"
  | CLt -> "<"
  | CGt -> ">"
  | CLe -> "<="
  | CGe -> ">="



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

let skip_incompatible edw wtl pevts =
  let rec aux incomp_rd = function
    | [] -> incomp_rd, []
    | ((_, (ed, vals)) as e) :: pevts ->
       if not (same_var edw ed) then aux incomp_rd pevts
       else if is_write ed || is_satisfied vals then aux incomp_rd pevts
       else if not (compat_val wtl vals) then aux true pevts
       else incomp_rd, e :: pevts
  in
  aux false pevts

let get_read_chunk edw wtl pevts = (* wtl should contain only 1 element *)
  let rec aux chunk = function
    | [] -> List.rev chunk, []
    | ((_, (ed, vals)) as e) :: pevts ->
       if not (same_var edw ed) then aux chunk pevts
       else if is_write ed || is_satisfied vals then List.rev chunk, pevts
       else if not (compat_val wtl vals) then List.rev chunk, e :: pevts
       else aux (e :: chunk) pevts
  in
  aux [] pevts

let read_chunks_for_write same_thread local_weak edw wtl pevts =
  let rec aux chunks = function
    | [] -> List.rev chunks
    | pevts ->
       let chunk, pevts = get_read_chunk edw wtl pevts in
       let incomp_rd, pevts = skip_incompatible edw wtl pevts in
       let chunk = if local_weak && incomp_rd then [] else chunk in
       if same_thread then begin
         if incomp_rd then raise UnsatLocalWeakRead;
         if chunk = [] then []
         else [chunk]
       end else begin
         if chunk = [] then aux chunks pevts
         else aux (chunk :: chunks) pevts
       end
  in
  aux [] pevts

let read_chunks_by_thread_by_write writes evts = (* evts by thread *)
  List.fold_left (fun rctw (((wp, _, wv, _) as edw, wtl) as w) ->
    let rct = HMap.fold (fun p pevts rct ->
      let rc = read_chunks_for_write (H.equal wp p)
        (is_local_weak wv) edw wtl pevts in
      if rc = [] then rct else (p, rc) :: rct
    ) evts [] in
    (w, rct) :: rctw
  ) [] writes

let read_combs same_thread local_weak rl =
  let rec aux = function
  | [] -> failwith "Weakwrite.read_combs : internal error" (*[[]], []*)
  | [r] -> if same_thread && local_weak then [[r]], [[r]] else [[r] ; []], [[r]]
  | r :: rl ->
     let combs, new_combs = aux rl in
     let combs, new_combs = List.fold_left (fun (combs, new_combs) nc ->
       let nc = (r :: nc) in
       nc :: combs, nc :: new_combs
     ) (if same_thread then [], [] else combs, []) new_combs in
     combs, if local_weak then new_combs else [r] :: new_combs
  in
  fst (aux rl)

let read_combs_by_thread_by_write rctw = (* merge with read_chunks_btbw *)
  List.fold_left (fun rctw ((((wp, _, wv, _), _) as w), rct) ->
    let rct = List.fold_left (fun rct (p, rc) ->
      let rc = List.fold_left (fun rc rl ->
        (read_combs (H.equal wp p) (is_local_weak wv) rl) @ rc
      ) [] rc in (* rc <- all read combinations for this thread *)
      (p, rc) :: rct (* source rc is a list of chunks *)
    ) [] rct in
    (w, rct) :: rctw
  ) [] rctw

let read_combs_by_write rctw =
  List.fold_left (fun rcw (w, rct) ->
    let lrc = List.fold_left (fun lrc (p, rcl) ->
      cartesian_product (fun rc1 rc2 -> rc1 @ rc2) lrc rcl
    ) [[]] rct in (* if no combination, we want to keep the write *)
    (w, lrc) :: rcw (* we just say that it satisfies no reads *)
  ) [] rctw

let all_combinations rcw =
  List.fold_left (fun combs (w, lrc) ->
    let lrc = List.map (fun rc -> [(w, rc)]) lrc in
    cartesian_product (fun rc comb -> rc @ comb) lrc combs
  ) [[]] rcw (* [[]] in case there is no combination / no write at all *)

let make_read_write_combinations writes sa =
  try
    let evts = events_by_thread sa in
    let rctw = read_chunks_by_thread_by_write writes evts in
    let rctw = read_combs_by_thread_by_write rctw in
    let rcw = read_combs_by_write rctw in
    all_combinations rcw
  with UnsatLocalWeakRead -> []



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

  (* Extract writes with their values from unsafe *)
  let writes, unsafe = SAtom.partition (fun a -> match a with
    | Atom.Comp (Write (_, _, _, []), Eq, _)
    | Atom.Comp (_, Eq, Write (_, _, _, [])) -> true
    | Atom.Comp (Write _, _, _) | Atom.Comp (_, _, Write _) ->
       failwith "Weakwrite.satisfy_reads : invalid Write"
    | _ -> false
  ) unsafe in

  (* Transform writes to a more suitable form *)
  let writes = SAtom.fold (fun aw wl -> match aw with
    | Atom.Comp (Write (p, v, vi, _), _, t)
    | Atom.Comp (t, _, Write (p, v, vi, _)) ->
       let p_v_vi = p :: v :: vi in
       let tl = try HLMap.find p_v_vi wl with Not_found -> [] in
       if tl <> [] then failwith "Weakwrite.satisfy_reads : anomaly";
       HLMap.add p_v_vi (t :: tl) wl
    | _ -> failwith "Weakwrite.satisfy_reads : internal error"
  ) writes HLMap.empty in
  let writes = HLMap.fold (fun p_v_vi tl wl -> match p_v_vi with
    | p :: v :: vi -> ((p, hW, mk_hV v, vi), tl) :: wl
    | _ -> failwith "Weakwrite.satisfy_read : internal error"
  ) writes [] in

  (* Build the relevant read-write combinations *)
  let wrcp = make_read_write_combinations writes unsafe in

  (* Generate the atom sets for each combination *)
  List.fold_left (fun pres wrcl ->
    let unsafe = List.fold_left (fun unsafe (((wp, _, wv, wvi), wtl), rcl) ->
      let unsafe = List.fold_left (fun unsafe (re, _) ->
        subst_event_val (fun t e ->
          if H.equal e re then wtl else [t]) unsafe
      ) unsafe rcl in
      let srl = List.fold_left (fun srl (re, _) -> re :: srl) [] rcl in
      let wv = H.make (var_of_v wv) in
      SAtom.add (mk_eq_true (Write (wp, wv, wvi, srl))) unsafe
    ) unsafe wrcl in
    unsafe :: pres
  ) [] wrcp



let satisfy_unsatisfied_reads sa =

  (* Retrieve unsatisfied reads *)
  let evts = SAtom.fold split_event sa HMap.empty in
  let ur = HMap.fold (fun e ((p, d, v, vi) as ed, vals) ur ->
    if is_read ed && vals <> [] then
      HMap.add e (sort_params ed (* , vals *)) ur
    else ur
  ) evts HMap.empty in

  (* Satisfy them from init *)
  let sa = subst_event_val (fun _ e ->
    let (_, _, v, vi) = HMap.find e ur in
    let v = H.make (var_of_v v) in
    if vi = [] then [Elem (v, Glob)] else [Access (v, vi)]
  ) sa in

  (* Add the necessary rf's *)
  HMap.fold (fun e _ sa ->
    SAtom.add (mk_eq_true (Access (hRf, [hE0; e]))) sa) ur sa

  (* SHOULD ADD DUMMY EVENT HERE *)        

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










(*
    let fmt = Format.std_formatter in
    List.iter (fun (((p, d, v, vi), t), rct) ->
      Format.fprintf fmt "W(%a,%a,[%a]) ->\n"
        H.print p H.print v (H.print_list ",") vi;
      List.iter (fun (p, rcl) ->
        Format.fprintf fmt "Proc %a\n" H.print p;
        List.iter (fun rc ->
          Format.fprintf fmt "Comb :";
          List.iter (fun (e, ((p, d, v, vi), vals)) ->
            Format.fprintf fmt " %a:R(%a,%a,[%a])"
              H.print e H.print p H.print v (H.print_list ",") vi;
          ) rc;
          Format.fprintf fmt "\n"
        ) rcl;
        Format.fprintf fmt "\n"
      ) rct;
      Format.fprintf fmt "\n"
    ) rctw2;
    Format.fprintf fmt "\n";
*)
(*
    let fmt = Format.std_formatter in
    Format.fprintf fmt "Read combinations by write :\n";
    List.iter (fun (((p, d, v, vi), t), rcl) ->
      Format.fprintf fmt "W(%a,%a,[%a]) ->\n"
        H.print p H.print v (H.print_list ",") vi;
      List.iter (fun rc ->
        Format.fprintf fmt "Comb :";
        List.iter (fun (e, ((p, d, v, vi), vals)) ->
          Format.fprintf fmt " %a:R(%a,%a,[%a])"
            H.print e H.print p H.print v (H.print_list ",") vi;
        ) rc;
        Format.fprintf fmt "\n"
      ) rcl;
      Format.fprintf fmt "\n"
    ) rcw;
    Format.fprintf fmt "\n";
 *)
(*
    let fmt = Format.std_formatter in
    Format.fprintf fmt "All combinations :\n";
    List.iter (fun comb ->
      Format.fprintf fmt "Comb :\n";
      List.iter (fun (((p, d, v, vi), t), rc) ->
        Format.fprintf fmt "W(%a,%a,[%a]) ->\n"
          H.print p H.print v (H.print_list ",") vi;
        List.iter (fun (e, ((p, d, v, vi), vals)) ->
          Format.fprintf fmt " %a:R(%a,%a,[%a])"
            H.print e H.print p H.print v (H.print_list ",") vi;
        ) rc;
        Format.fprintf fmt "\n"        
      ) comb;
      Format.fprintf fmt "\n";
    ) combs;
    Format.fprintf fmt "\n";
 *)


            
