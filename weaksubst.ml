
open Weakmem
open Types
open Util


(* evts : map (p, e) -> ed *)
(* res : map p -> map e -> ed *)
(* want : map p -> set (map e -> ed) *)
       
(* Retrive all events in a map of map (proc -> eid -> event *)
let get_evts ar =
  let evts = Array.fold_left (fun evts a ->
    Weakwrite.split_event a evts) HMap.empty ar in
  HMap.fold (fun e ((p, _, _, _) as ed, vals) evts ->
    let pevts = try HMap.find p evts with Not_found -> HMap.empty in
    let evt = (sort_params ed, vals) in
    HMap.add p (HMap.add e evt pevts) evts
  ) evts HMap.empty

(* Checks whether (cop1, c1) can subsume (cop2, c2) *)
let compatible_consts cop1 c1 cop2 c2 =
  let open Weakwrite in
  let c = Types.compare_constants c1 c2 in
  begin match cop1, cop2 with
  | CEq, CEq -> c = 0
  | CNeq, CEq -> c <> 0
  | CNeq, CNeq -> c = 0
  | CNeq, CLt -> c >= 0 (* must have c1 >= c2 *)
  | CNeq, CLe -> c > 0 (* must have c1 > c2 *)
  | CNeq, CGt -> c <= 0 (* must have c1 <= c2 *)
  | CNeq, CGe -> c < 0 (* must have c1 < c2 *)
  | CLt, CEq -> c > 0 (* must have c1 > c2 *)
  | CLt, CLt -> c >= 0 (* must have c1 >= c2 *)
  | CLt, CLe -> c > 0 (* must have c1 > c2 *)
  | CLe, CEq -> c >= 0 (* must have c1 >= c2 *)
  | CLe, CLt -> c >= 0 (* must have c1 >= c2-1 *)
  | CLe, CLe -> c >= 0 (* must have c1 >= c2 *)
  | CGt, CEq -> c < 0 (* must have c1 < c2 *)
  | CGt, CGt -> c <= 0 (* must have c1 <= c2 *)
  | CGt, CGe -> c < 0 (* must have c1 < c2 *)
  | CGe, CEq -> c <= 0 (* must have c1 <= c2 *)
  | CGe, CGt -> c <= 0 (* must have c1 <= c2-1 *)
  | CGe, CGe -> c <= 0 (* must have c1 <= c2 *)
  | _ -> false
  end

(* Checks whether (cop1, t1) can subsume (cop2, t2) *)
(* True means maybe, False means no *)
let compatible_terms cop1 t1 cop2 t2 =
  let open Weakwrite in
  match t1, t2 with
  | Const c1, Const c2 -> compatible_consts cop1 c1 cop2 c2
  | Elem (c1, Constr), Elem (c2, Constr) -> (* in dekker, msi, lamp_tso *)
     let equ = H.equal c1 c2 in
     begin match cop1, cop2 with
     | CEq, CEq -> equ | CEq, CNeq -> false
     | CNeq, CEq -> not equ | CNeq, CNeq -> equ
     | _ -> failwith "Weaksubst.compatible_values : invalid op on Constr"
     end
  | Elem (p1, Var), Elem (p2, Var) -> (* in dekker *)
     let equ = H.equal p1 p2 in
     begin match cop1, cop2 with
     | CEq, CEq -> equ | CEq, _ -> false
     | CNeq, CEq | CNeq, CLe | CNeq, CGe -> not equ
     | CNeq, CNeq -> equ | CNeq, _ -> true
     | CLt, CEq | CLt, CLe -> not equ | CLt, CLt -> true | CLt, _ -> false
     | CGt, CEq | CGt, CGe -> not equ | CGt, CGt -> true | CGt, _ -> false
     | CLe, CEq | CLe, CLe | CLe, CLt -> true | CLe, _ -> false
     | CGe, CEq | CGe, CGe | CGe, CGt -> true | CGe, _ -> false
     end
  | Elem (v1, Glob), Elem (v2, Glob) -> (* not in lamp_tso, msi, dekker *)
     if not (H.equal v1 v2) then
     begin match cop1, cop2 with
     | CEq, CEq -> true | CEq, _ -> false
     | CNeq, _ -> true
     | CLt, CEq | CLt, CLt | CLt, CLe -> true | CLt, _ -> false
     | CGt, CEq | CGt, CGt | CGt, CGe -> true | CGt, _ -> false
     | CLe, CEq | CLe, CLt | CLe, CLe -> true | CLe, _ -> false
     | CGe, CEq | CGe, CGt | CGe, CGe -> true | CGe, _ -> false
     end else
     begin match cop1, cop2 with
     | CEq, CEq -> true | CEq, _ -> false
     | CNeq, CNeq | CNeq, CLt | CNeq, CGt -> true | CNeq, _ -> false
     | CLt, CLt -> true | CLt, _ -> false
     | CGt, CGt -> true | CGt, _ -> false
     | CLe, CEq | CLe, CLe | CLe, CLt -> true | CLe, _ -> false
     | CGe, CEq | CGe, CGe | CGe, CGt -> true | CGe, _ -> false
     end
  (* | Access (v1, vi1), Access (v2, vi2) -> TODO *)
  | Arith (t1, c1), Arith (t2, c2) -> (* not in lamp_tso, msi, dekker *)
     if not (Term.equal t1 t2) then true
     else compatible_consts cop1 c1 cop2 c2
  | _ ->
     begin match cop1, cop2 with
     | CEq, CEq -> true | CEq, _ -> false
     | CNeq, _ -> true
     | CLt, CEq | CLt, CLt | CLt, CLe -> true | CLt, _ -> false
     | CGt, CEq | CGt, CGt | CGt, CGe -> true | CGt, _ -> false
     | CLe, CEq | CLe, CLt | CLe, CLe -> true | CLe, _ -> false
     | CGe, CEq | CGe, CGt | CGe, CGe -> true | CGe, _ -> false
     end (* not in lamp_tso, msi, dekker *)
(* add const vs elem/access *)
(* add event value vs event value (Field/Field)*)

(* Checks whether (ed1, vals) can subsume (ed2, vals2) *)
let compat_evts (ed1, vals1) (ed2, vals2) =
  same_proc ed1 ed2 && same_dir ed1 ed2 && same_var ed1 ed2 &&
    (vals1 = [] (*&& vals2 = []*) ||
     vals1 <> [] && vals2 <> [] &&
    (* (vals1 = [] || vals2 = [] || *)
     List.for_all (fun (cop1, t1) ->
       List.for_all (fun (cop2, t2) ->
         compatible_terms cop1 t1 cop2 t2
       ) vals2
     ) vals1)

(* SHOULD TAKE CARE OF SYNC ! *)
(* [Empty] -> the source was empty, this is a valid substitution
                (though it should not happen here)
   [] -> no combination (not enough compatible events in dest) *)
let make_e_combs p esf est = (* order between e matters *)
  let rec aux cc rcl esf est =
    try
      let ef, evtf = HMap.min_binding esf in
      let esf = HMap.remove ef esf in
      let rcl, _ = HMap.fold (fun et evtt (rcl, est) ->
	let est = HMap.remove et est in
        if compat_evts evtf evtt then
	  let cc = H2Map.add (p, ef) et cc in
	  aux cc rcl esf est, est
	else rcl, est
      ) est (rcl, est) (* To Set is finished -> combinations done for this ef *)
      in rcl
    with Not_found -> cc :: rcl (*From Set is empty -> the combinations are OK*)
  in
  aux H2Map.empty [] esf est

(* [Empty] -> the source was empty, this is a valid substitution
   [] -> no combination (not enough compatible events in dest)  *)
let make_p_combs psf pst = (* only map events from same procs *)
  let rec aux ccl psf pst =
    try
      let p, esf = HMap.choose psf in
      let psf = HMap.remove p psf in
      try
        let est = HMap.find p pst in
        let pst = HMap.remove p pst in
	let ncl = make_e_combs p esf est in (* might be [] or [Empty] *)
	if ncl = [] then []
	else
          let ccl = cartesian_product_h2m ncl ccl in
          aux ccl psf pst (* Next process *)
      with Not_found -> []
    with Not_found -> ccl (* From Set is empty -> we're done *)
  in
  aux [H2Map.empty] psf pst
      
(* from : visited node, more general / to : node to test, less general *)
let build_event_substs from_evts to_evts =
  TimeCSubst.start ();
  let es = make_p_combs from_evts to_evts in
  TimeCSubst.pause ();
  es






(* Retrive all events in a map of (eid -> (proc, event)) *)
let get_evts ar =
  let evts = Array.fold_left (fun evts a ->
    Weakwrite.split_event a evts) HMap.empty ar in
  let evts = HMap.map (fun (ed, vals) -> (sort_params ed, vals)) evts in
  evts

let po_agree cs ef pf et pt pof pot =
  let ppof = HMap.find pf pof in
  let ppot = HMap.find pt pot in
  HMap.for_all (fun ef0 (et0, mt0) ->
    (*if mt0 then true
    else*) if H2Set.mem (ef0, ef) ppof then H2Set.mem (et0, et) ppot
    else if H2Set.mem (ef, ef0) ppof then H2Set.mem (et, et0) ppot
    else true
  ) cs

(* po : pid -> (eid, eid) set
   fce : pid -> (eid, eid) set
   rf : eid -> eid list (write -> reads)
   rmw : eid -> eid (read -> write)
   s : (eid set) list *)
let make_prop (po, f, rf, rmw, sf) =
  let prop = HMap.fold (fun p ppo prop ->
    H2Set.union ppo prop) po H2Set.empty in
  let prop = HMap.fold (fun p pf prop ->
    H2Set.fold (fun (fef, fet) prop ->
      let pre = H2Set.filter (fun (_, pet) -> H.equal pet fef) prop in
      let post = H2Set.filter (fun (pef, _) -> H.equal fet pef) prop in
      let pre = H2Set.add (fef, fet) pre in
      let post = H2Set.add (fef, fet) post in
      H2Set.fold (fun (pef, _) prop ->
        H2Set.fold (fun (_, pet) prop ->
          H2Set.add (pef, pet) prop
        ) post prop
      ) pre prop
    ) pf prop
  ) po prop in
  let prop = HMap.fold (fun wef retl prop ->
    let pre = H2Set.filter (fun (_, pet) -> H.equal pet wef) prop in
    let post = H2Set.filter (fun (pef, _) ->
                 List.exists (fun ret -> H.equal ret pef) retl
               ) prop in
    let pre = List.fold_left (fun pre ret ->
                H2Set.add (wef, ret) pre) pre retl in
    let post = List.fold_left (fun post ret ->
                 H2Set.add (wef, ret) post) post retl in
    H2Set.fold (fun (pef, _) prop ->
      H2Set.fold (fun (_, pet) prop ->
        H2Set.add (pef, pet) prop
      ) post prop
    ) pre prop
  ) rf prop in
  prop  

let prop_agree cs ef pf et pt propf propt =
  HMap.for_all (fun ef0 (et0, mt0) ->
    (*if mt0 then true
    else*) if H2Set.mem (ef0, ef) propf then H2Set.mem (et0, et) propt
    else if H2Set.mem (ef, ef0) propf then H2Set.mem (et, et0) propt
    else true
  ) cs

let make_substs esf (pof, ff, rff, rmwf, sf) est (pot, ft, rft, rmwt, st) =
  let propf = make_prop (pof, ff, rff, rmwf, sf) in
  let propt = make_prop (pot, ft, rft, rmwt, st) in
  let rec aux csl cs esf est =
    try
      let ef, (((pf, df, vf, vif) as edf, valf) as evtf) = HMap.choose esf in
      let esf = HMap.remove ef esf in
      let csl = HMap.fold (
        fun et (((pt, dt, vt, vit) as edt, valt) as evtt) csl ->
        (* buggy patch to try to subsume more nodes *)            
        (*if valf = [] && is_read edf && is_read edt
          then aux csl (HMap.add ef (et, true) cs) esf (HMap.remove et est)
        else if (valf <> [] || is_write edf) &&
            compat_evts evtf evtt && po_agree cs ef pf et pt pof pot
          then aux csl (HMap.add ef (et, false) cs) esf (HMap.remove et est)
	else csl*)
        if valf = [] && valt = [] && same_dir edf edt && (*H.equal pf pt &&*)
           is_local_weak vf && is_local_weak vt && H.equal vf vt &&
             (*po_agree cs ef pf et pt pof pot &&*) H.equal pf pt
           && prop_agree cs ef pf et pt propf propt
          then aux csl (HMap.add ef (et, true) cs) esf (HMap.remove et est)
        else if compat_evts evtf evtt (*&& po_agree cs ef pf et pt pof pot*)
           && prop_agree cs ef pf et pt propf propt                  
          then aux csl (HMap.add ef (et, false) cs) esf (HMap.remove et est)
	else csl
      ) est csl
      in csl
    with Not_found ->
      let cs = HMap.map (fun (et, _) -> et) cs in
      cs :: csl (* From Set is empty -> we're done *)
  in
  aux [] HMap.empty esf est

(* from : visited node, more general / to : node to test, less general *)
let build_event_substs from_evts from_rels to_evts to_rels =  (*
  Format.eprintf "----------\nEvts from : \n";
  HMap.iter (fun e ((p, d, v, vi), vals) ->
    Format.eprintf "%a:%a:%a:%a[%a](%d)  " H.print e H.print p H.print d H.print v (H.print_list ",") vi (List.length vals);
  ) from_evts;
  Format.eprintf "\n----------\nEvts to : \n";
  HMap.iter (fun e ((p, d, v, vi), vals) ->
    Format.eprintf "%a:%a:%a:%a[%a](%d)  " H.print e H.print p H.print d H.print v (H.print_list ",") vi (List.length vals);
  ) to_evts;
  Format.eprintf "\n----------\n"; *)
  TimeCSubst.start ();
  let es = make_substs from_evts from_rels to_evts to_rels in (*
  List.iter (fun s ->
    Format.eprintf "Subst :";
    HMap.iter (fun ef et -> Format.eprintf " %a->%a" H.print ef H.print et) s;
    Format.eprintf "\n"
  ) es;
  if List.length es = 0 then Format.eprintf "No subst\n"; *)
  TimeCSubst.pause ();
  es




let remap_events_ar ar sub =
  let subst e =
    try HMap.find e sub with Not_found ->
      failwith "Weaksubst.remap_events : no substitution !"
  in
  let remap_sl sl =
    let rec aux rsl = function
      | [] -> rsl
      | e :: sl -> aux ((subst e) :: rsl) sl
    in
    List.rev (aux [] sl)
  in
  let rec remap_t = function
    | Arith (t, c) -> Arith (remap_t t, c)
    | Field (t, f) -> Field (remap_t t, f)
    | Access (a, [e]) when H.equal a hE || H.equal a hFence ->
        let e = subst e in Access (a, [e])
    | Access (a, [e1; e2]) when H.equal a hRf ->
        let e1 = subst e1 in
        let e2 = subst e2 in
        Access (a, [e1; e2])
    | Access (a, sl) when H.equal a hSync ->
       Access (a, remap_sl sl)
    (* Read / Write / Fence -> KO *)
    | t -> t
  in
  let rec remap_a = function
    | Atom.Comp (t1, op, t2) -> Atom.Comp (remap_t t1, op, remap_t t2)
    | Atom.Ite (sa, a1, a2) -> Atom.Ite (sa, remap_a a1, remap_a a2) (* KO ? *)
    | a -> a
  in
  let ar = Array.map remap_a ar in
  Array.fast_sort Atom.compare ar;
  ar

let remap_events ar substs =
(*  Format.eprintf "Subst : \n";
  List.iter (fun s ->
    HMap.iter (fun ef et ->
      Format.eprintf "%a->%a / " H.print ef H.print et
    ) s;
    if HMap.is_empty s then Format.eprintf "empty";
    Format.eprintf "\n"
  ) substs;*)
  TimeASubst.start ();
  let nl = List.fold_left (fun nodes s ->
    if HMap.is_empty s then ar :: nodes
    else (remap_events_ar ar s) :: nodes
  ) [] substs in
  TimeASubst.pause ();
  nl






(*= v1  = !<> v2      v1 = v2
  = v1  <> != v2      false
  = v1      < v2      false
  = v1     <= v2      false
  = v1    !<= v2      false
  = v1     !< v2      false

 <> v1  = !<> v2      v1 <> v2         eg : x <> 4 / x = 4 // x <> 4 / x = 5 
 <> v1  <> != v2      v1 = v2
 <> v1      < v2      v1 >= v2         eg : x <> 4 / x = 3 // x <> 4 / x = 4
 <> v1     <= v2      v1 > v2
 <> v1    !<= v2      v1 <= v2
 <> v1     !< v2      v1 < v2          eg : x <> 4 / x = 4 // x <> 4 / x = 5

  < v1  = !<> v2      v1 > v2          eg : x < 4 / x = 3 // x < 4 / x = 4 
  < v1  <> != v2      false
  < v1      < v2      v1 >= v2         eg : x < 4 / x <= 3 // x < 4 / x <= 4
  < v1     <= v2      v1 > v2
  < v1    !<= v2      false
  < v1     !< v2      false

 <= v1  = !<> v2      v1 >= v2         eg : x < 4 / x = 4 // x < 4 / x = 5 
 <= v1  <> != v2      false
 <= v1      < v2      v1+1 >= v2       eg : x <= 4 / x < 5 // x <= 4 / x < 6
 <= v1     <= v2      v1 >= v2
 <= v1    !<= v2      false
 <= v1     !< v2      false

  > v1  = !<> v2      v1 < v2          eg : x > 4 / x = 4 // x > 4 / x = 5 
  > v1  <> != v2      false
  > v1      < v2      false
  > v1     <= v2      false
  > v1    !<= v2      v1 <= v2
  > v1     !< v2      v1 < v2          eg : x > 4 / x >= 4 // x > 4 / x >= 5

 >= v1  = !<> v2      v1 <= v2         eg : x >= 4 / x = 3 // x >= 4 / x = 4 
 >= v1  <> != v2      false
 >= v1      < v2      false
 >= v1     <= v2      false
 >= v1    !<= v2      v1 <= v2+1
 >= v1     !< v2      v1 <= v2         eg : x >= 4 / x >= 3 // x <= 4 / x >= 4

x >= 4    x > 2   x > 3   x > 4   x > 5   x > 6    *)


