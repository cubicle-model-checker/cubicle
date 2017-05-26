
open Weakmem
open Weakevent
open Types
open Util

(* Checks whether (cop1, c1) can subsume (cop2, c2) *)
let compatible_consts cop1 c1 cop2 c2 =
  let open Weakpre in
  let c = Types.compare_constants c1 c2 in
  let res = begin match cop1, cop2 with
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
  end in
  (* Format.fprintf Format.std_formatter "%s %a // %s %a : %b\n" *)
  (*   (string_of_cop cop1) Term.print (Const c1) *)
  (*   (string_of_cop cop2) Term.print (Const c2) res; *)
  (* Format.print_flush (); *)
  res

(* Checks whether (cop1, t1) can subsume (cop2, t2) *)
(* True means maybe, False means no *)
let compatible_terms cop1 t1 cop2 t2 =
  let open Weakpre in
  match t1, t2 with
  | Const c1, Const c2 -> compatible_consts cop1 c1 cop2 c2
  | Elem (c1, Constr), Elem (c2, Constr) -> (* in dekker, msi, lamp_tso *)
     let equ = H.equal c1 c2 in
     begin match cop1, cop2 with
     | CEq, CEq -> equ | CEq, CNeq -> false
     | CNeq, CEq -> not equ | CNeq, CNeq -> equ
     | _ -> failwith "Weakfp.compatible_values : invalid op on Constr"
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
  same_dir ed1 ed2 && (same_var ed1 ed2 || no_var ed1) &&
    (vals1 = [] (*&& vals2 = []*) ||
     vals1 <> [] && vals2 <> [] &&
    (* (vals1 = [] || vals2 = [] || *)
     List.for_all (fun (cop1, t1) -> (* replaced forall by exists *)
       List.exists (fun (cop2, t2) -> (* see spinlock *)
         compatible_terms cop1 t1 cop2 t2
       ) vals2
     ) vals1)




(* let po_agree cs ef pf et pt (pof, _, _, _, _, _) (pot, _, _, _, _, _) = *)
(*   let ppof = HMap.find pf pof in *)
(*   let ppot = HMap.find pt pot in *)
(*   HMap.for_all (fun ef0 et0 -> *)
(*     if H2Set.mem (ef0, ef) ppof then H2Set.mem (et0, et) ppot *)
(*     else if H2Set.mem (ef, ef0) ppof then H2Set.mem (et, et0) ppot *)
(*     else true *)
(*   ) cs *)

let sync_agree cs ef pf et pt relf relt =
  HMap.for_all (fun ef0 et0 ->
    if Weakrel.Rel.mem_eq ef0 ef relf then Weakrel.Rel.mem_eq et0 et relt
    else if Weakrel.Rel.mem_eq ef ef0 relf then Weakrel.Rel.mem_eq et et0 relt
    else true
  ) cs
  
let rel_agree cs ef pf et pt relf relt =
  HMap.for_all (fun ef0 et0 ->
    if Weakrel.Rel.mem_lt ef0 ef relf then Weakrel.Rel.mem_lt et0 et relt
    else if Weakrel.Rel.mem_lt ef ef0 relf then Weakrel.Rel.mem_lt et et0 relt
    else true
  ) cs

let make_substs esf relf est relt =
  let (_, ghbf) = relf in
  let (_, ghbt) = relt in
  let rec aux csl cs esf est =
    try
      let ef, (((pf, df, vf, vif) as edf, valf) as evtf) = HMap.choose esf in
      (* Format.fprintf Format.std_formatter "From %a\n" H.print ef; *)
      let esf = HMap.remove ef esf in
      let csl = HMap.fold (
        fun et (((pt, dt, vt, vit) as edt, valt) as evtt) csl ->
        (* Format.fprintf Format.std_formatter "Try %a\n" H.print et; *)
        if valf = [] && valt = []
           && H.equal pf pt
           && is_read edf && is_read edt
           (* && po_agree cs ef pf et pt relf relt *)
           && sync_agree cs ef pf et pt ghbf ghbt
           && rel_agree cs ef pf et pt ghbf ghbt
          then aux csl (HMap.add ef et cs) esf (HMap.remove et est)
        else if compat_evts evtf evtt
           && H.equal pf pt
           (* && po_agree cs ef pf et pt relf relt *)
           && sync_agree cs ef pf et pt ghbf ghbt
           && rel_agree cs ef pf et pt ghbf ghbt
          then aux csl (HMap.add ef et cs) esf (HMap.remove et est)
	else begin (*Format.fprintf Format.std_formatter "No\n";*) csl end
      ) est csl
      in csl
    with Not_found ->
      cs :: csl (* From Set is empty -> we're done *)
  in
  aux [] HMap.empty esf est

(* from : visited node, more general / to : node to test, less general *)
let build_event_substs from_evts from_rels to_evts to_rels =

  (* let fprintf s = Format.fprintf Format.std_formatter s in *)
  (* fprintf "----------\nEvts from : \n"; *)
  (* HMap.iter (fun e ((p, d, v, vi), vals) -> *)
  (*   fprintf "%a:%a:%a:%a[%a](%d)  " H.print e H.print p H.print d H.print v (H.print_list ",") vi (List.length vals); *)
  (* ) from_evts; *)
  (* fprintf "\n"; *)
  (* let (_, fghb, _) = from_rels in *)
  (* H2Set.iter (fun (ef, et) -> fprintf "%a < %a   " H.print ef H.print et) fghb; *)
  (* fprintf "\n----------\nEvts to : \n"; *)
  (* HMap.iter (fun e ((p, d, v, vi), vals) -> *)
  (*   fprintf "%a:%a:%a:%a[%a](%d)  " H.print e H.print p H.print d H.print v (H.print_list ",") vi (List.length vals); *)
  (* ) to_evts; *)
  (* fprintf "\n"; *)
  (* let (_, tghb, _) = from_rels in   *)
  (* H2Set.iter (fun (ef, et) -> fprintf "%a < %a   " H.print ef H.print et) tghb; *)
  (* fprintf "\n----------\n";   *)
  TimeCSubst.start ();
  let es = make_substs from_evts from_rels to_evts to_rels in
  (* List.iter (fun s -> *)
  (*   fprintf "Subst :"; *)
  (*   HMap.iter (fun ef et -> fprintf " %a->%a" H.print ef H.print et) s; *)
  (*   fprintf "\n" *)
  (* ) es; *)
  (* if List.length es = 0 then fprintf "No subst\n"; *)
  TimeCSubst.pause ();
  es



let remap_events_ar ar sub =
  let subst e =
    try HMap.find e sub with Not_found ->
      failwith "Weakfp.remap_events : no substitution !"
  in
  let rec remap_t tt = match tt with
    | Arith (t, c) ->
       let t' = remap_t t in if t' == t then tt else Arith (t', c)
    | Access (a, [e]) when is_event a ->
       let e' = subst e in if e' == e then tt else Access (a, [e'])
    | Access (a, [p; e]) when H.equal a hFence ->
       let e' = subst e in if e' == e then tt else Access (a, [p; e'])
    | Access (a, [e1; e2]) when H.equal a hGhb || H.equal a hSync ->
       let e1' = subst e1 in
       let e2' = subst e2 in
       if e1' == e1 && e2' == e2 then tt else Access (a, [e1'; e2'])
    (* Read / Write / Fence -> KO *)
    | _ -> tt
  in
  let rec remap_a a = match a with
    | Atom.Comp (t1, op, t2) ->
       let t1' = remap_t t1 in
       let t2' = remap_t t2 in
       if t1' == t1 && t2' == t2 then a else Atom.Comp (t1', op, t2')
    | Atom.Ite (sa, a1, a2) ->
       let sa = SAtom.fold (fun a sa ->
         SAtom.add (remap_a a) sa) sa SAtom.empty in
       Atom.Ite (sa, remap_a a1, remap_a a2) (* KO ? *)
    | _ -> a
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


