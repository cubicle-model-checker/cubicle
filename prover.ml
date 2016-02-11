
(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2014                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

open Format
open Options
open Util
open Ast
open Types

module HMap = Hstring.HMap

open Event

module T = Smt.Term
module F = Smt.Formula

module SMT = Smt.Make (Options)

let proc_terms =
  let procs = (Hstring.make "#0") :: Variable.procs in
  List.iter 
    (fun x -> Smt.Symbol.declare x [] Smt.Type.type_proc) procs;
  List.map (fun x -> T.make_app x []) Variable.procs

let distinct_vars = 
  let t = Array.make max_proc F.f_true in
  let _ = 
    List.fold_left 
      (fun (acc,i) v -> 
	 if i<>0 then t.(i) <- F.make_lit F.Neq (v::acc);
	 v::acc, i+1) 
      ([],0) proc_terms 
  in
  function n -> if n = 0 then F.f_true else t.(n-1)

(* let _ = SMT.assume ~id:0 (distinct_vars max_proc) *)

let order_vars =
  let t = Array.make max_proc F.f_true in
  let _ =
    List.fold_left
      (fun (acc, lf, i) v ->
        match acc with
          | v2::r ->
            let lf = (F.make_lit F.Lt [v2;v]) :: lf in
            t.(i) <- F.make F.And lf;
            v::acc, lf, i+1
          | [] -> v::acc, lf, i+1)
      ([], [], 0) proc_terms
  in
  function n -> if n = 0 then F.f_true else t.(n-1)

let make_op_comp = function
  | Eq -> F.Eq
  | Lt -> F.Lt
  | Le -> F.Le
  | Neq -> F.Neq

let make_const = function
  | ConstInt i -> T.make_int i
  | ConstReal i -> T.make_real i
  | ConstName n -> T.make_app n []

let ty_const = function
  | ConstInt _ -> Smt.Type.type_int
  | ConstReal _ -> Smt.Type.type_real
  | ConstName n -> snd (Smt.Symbol.type_of n)

let rec mult_const tc c i =
 match i with
  | 0 -> 
    if ty_const c = Smt.Type.type_int then T.make_int (Num.Int 0)
    else T.make_real (Num.Int 0)
  | 1 -> tc
  | -1 -> T.make_arith T.Minus (mult_const tc c 0) tc
  | i when i > 0 -> T.make_arith T.Plus (mult_const tc c (i - 1)) tc
  | i when i < 0 -> T.make_arith T.Minus (mult_const tc c (i + 1)) tc
  | _ -> assert false

let make_arith_cs =
  MConst.fold 
    (fun c i acc ->
      let tc = make_const c in
      let tci = mult_const tc c i in
       T.make_arith T.Plus acc tci)

let make_cs cs =
  let c, i = MConst.choose cs in
  let t_c = make_const c in
  let r = MConst.remove c cs in
  if MConst.is_empty r then mult_const t_c c i
  else make_arith_cs r (mult_const t_c c i)
	 
let rec make_term = function
  | Elem (e, _) -> T.make_app e []
  | Const cs -> make_cs cs 
  | Access (a, li) -> T.make_app a (List.map (fun i -> T.make_app i []) li)
  | Arith (x, cs) -> 
      let tx = make_term x in
      make_arith_cs cs tx
  | Read (_, _, _) -> failwith "Prover.make_term : Read should not be in atom"
  | Field (t, f) ->
      let tt = make_term t in
      T.make_access tt f
  | List tl ->
     failwith "Prover.make_term Field TODO"


let split_order a =
  let ho = Hstring.make "_o" in
  match a with
  | Atom.Comp (List tl, Eq, Access (a, [p]))
  | Atom.Comp (Access (a, [p]), Eq, List tl) when a = ho ->
     let ord = List.map (fun t -> match t with
       | Elem (e, Glob) -> e
       | _ -> failwith "Prover.split_order error"
     ) tl in
     (None, Some (p, ord))
  | _ -> (Some a, None)

let split_order_array ar =
  Array.fold_left (fun (sa, ord) a -> match split_order a with
    | None, Some (p, o) -> (sa, HMap.add p o ord)
    | Some a, None -> (SAtom.add a sa, ord)
    | _, _ -> failwith "Prover.split_order_array error"
  ) (SAtom.empty, HMap.empty) ar

let split_order_set sa =
  SAtom.fold (fun a (sa, ord) -> match split_order a with
    | None, Some (p, o) -> (sa, HMap.add p o ord)
    | Some a, None -> (SAtom.add a sa, ord)
    | _, _ -> failwith "Prover.split_order_set error"
  ) sa (SAtom.empty, HMap.empty)

let get_events sa =
  let none = Hstring.make "" in
  let he = Hstring.make "_e" in
  let hdir = Hstring.make "_dir" in
  let hvar = Hstring.make "_var" in
  SAtom.fold (fun a evts -> match a with
    | Atom.Comp (Field (Access (a, [p ; e]), f), Eq, Elem (c, t))
    | Atom.Comp (Elem (c, t), Eq, Field (Access (a, [p ; e]), f)) when a = he ->
       let pevts = try HMap.find p evts with Not_found -> HMap.empty in
       let (d, v) = try HMap.find e pevts with Not_found -> (none, none) in
       let d = if f = hdir then c else d in
       let v = if f = hvar then c else v in
       HMap.add p (HMap.add e (d, v) pevts) evts
    | _ -> evts
  ) sa HMap.empty		      


let gen_po ord =
  let hf = Hstring.make "_f" in
  let rec aux p po = function
    | [] | [_] -> po
    | f :: pord when f = hf -> aux p po pord
    | e :: f :: pord when f = hf -> aux p po (e :: pord)
    | e1 :: ((e2 :: _) as pord) -> aux p ((p, e1, p, e2) :: po) pord
  in
  HMap.fold (fun p pord po -> aux p po pord) ord []

let gen_fence evts ord =
  let hf = Hstring.make "_f" in
  let hW = Hstring.make "_W" in
  let hR = Hstring.make "_R" in
  let rec split_at_first_fence lpord = function
    | [] -> lpord, []
    | f :: rpord when f = hf -> lpord, rpord
    | e :: rpord -> split_at_first_fence (e :: lpord) rpord
  in
  let rec first_event dir p = function
    | [] -> None
    | e :: pord ->
       let pevts = HMap.find p evts in
       let (d, _) = HMap.find e pevts in
       if d = dir then Some e else first_event dir p pord
  in
  let rec aux p fence lpord rpord = match rpord with
    | [] -> fence
    | _ ->
       let lpord, rpord = split_at_first_fence lpord rpord in
       match first_event hW p lpord, first_event hR p rpord with
       | Some w, Some r -> aux p ((p, w, p, r) :: fence) lpord rpord
       | _, _ -> aux p fence lpord rpord
  in
  HMap.fold (fun p pord fence -> aux p fence [] pord) ord []

let rec co_from_pord evts p pord co =
  let hW = Hstring.make "_W" in
  let pevts = try HMap.find p evts with Not_found -> HMap.empty in
  let pwrites = HMap.filter (fun e (d, _) -> d = hW) pevts in
  let rec aux co = function
  | [] -> co
  | e1 :: pord -> begin try
      let (_, v1) = HMap.find e1 pwrites in
      let co = List.fold_left (fun co e2 ->
	try let (_, v2) = HMap.find e2 pwrites in
	  if v1 = v2 then (p, e1, p, e2) :: co else co		   
	with Not_found -> co
      ) co pord in
      aux co pord
    with Not_found -> aux co pord end
  in
  aux co pord

let gen_co evts ord =
  let p0 = Hstring.make "#0" in
  let hW = Hstring.make "_W" in
  let writes = HMap.map (HMap.filter (fun e (d, _) -> d = hW)) evts in
  let iwrites, writes = HMap.partition (fun p _ -> p = p0) writes in
  (* Initial writes *)
  let co = HMap.fold (fun p1 -> HMap.fold (fun e1 (_, v1) co ->
    HMap.fold (fun p2 -> HMap.fold (fun e2 (_, v2) co ->
      if v1 = v2 then (p1, e1, p2, e2) :: co else co
    )) writes co
  )) iwrites [] in
  (* Writes from same thread *)
  HMap.fold (fun p pord co ->
    co_from_pord evts p pord co
  ) ord co
(*
let gen_co_cands evts ord = []
  let rec aux cco tpof1 pof =
    try
      let (tid2, tpof2) = IntMap.choose pof in
      let cco = List.fold_left (fun cco eid1 ->
        match write_from_id es eid1 with
        | None -> cco
        | Some e1 ->
           List.fold_left (fun cco eid2 ->
             match write_from_id es eid2 with
	     | None -> cco
	     | Some e2 ->
		if e1.var <> e2.var then cco
		else [ (e1, e2) ; (e2, e1) ] :: cco
	   ) cco tpof2
      ) cco tpof1 in
      aux cco tpof2 (IntMap.remove tid2 pof)
    with Not_found -> cco
  in
  try
    let (tid1, tpof1) = IntMap.choose es.po_f in
    aux [] tpof1 (IntMap.remove tid1 es.po_f)
  with Not_found -> []
 *)

let gen_co_cands evts =
  let p0 = Hstring.make "#0" in
  let hW = Hstring.make "_W" in
  let rec aux evts cco =
    try
      let (p1, p1evts) = HMap.choose evts in
      let evts = HMap.remove p1 evts in
      let cco = HMap.fold (fun e1 (d1, v1) cco ->
        HMap.fold (fun p2 p2evts cco ->
          HMap.fold (fun e2 (d2, v2) cco ->
	    if d1 = hW && d2 = hW && v1 = v2 then
	      [ (p1, e1, p2, e2) ; (p2, e2, p1, e1) ] :: cco     
	    else cco
	  ) p2evts cco
        ) evts cco
      ) p1evts cco in
      aux evts cco
    with Not_found -> cco
  in
  aux (HMap.remove p0 evts) []
  
let gen_rf_cands evts =
  let hR = Hstring.make "_R" in
  let reads, writes = HMap.fold (fun p pe (r, w) ->
    let pr, pw = HMap.partition (fun e (d, v) -> d = hR) pe in
    (HMap.add p pr r, HMap.add p pw w)
  ) evts (HMap.empty, HMap.empty) in
  HMap.fold (fun p1 -> HMap.fold (fun e1 (d1, v1) crf ->
    let ecrf = HMap.fold (fun p2 -> HMap.fold (fun e2 (d2, v2) ecrf ->
      if v1 <> v2 then ecrf
      else (p2, e2, p1, e1) :: ecrf
    )) writes [] in
    if ecrf = [] then crf else ecrf :: crf
  )) reads []


let make_orders ?(fp=false)evts ord =
  let f = [F.f_true] in
  let f = (F.make_rel "_po" (gen_po ord)) @ f in
  let f = (F.make_rel "_fence" (gen_fence evts ord)) @ f in
  let f = (F.make_rel "_co" (gen_co evts ord)) @ f in
  let f = (F.make_cands "_rf" (gen_rf_cands evts)) @ f in
  let f = (F.make_cands "_co" (gen_co_cands evts)) @ f in
  if fp then F.make F.And f else
  let el = HMap.fold (fun p -> HMap.fold (fun e _ el -> (p,e) :: el)) evts [] in
  let f = List.fold_left (fun f e -> (F.make_acyclic_rel e) @ f) f el in
  F.make F.And f


let rec make_formula_set sa =
  let sa, ord = split_order_set sa in
  let evts = get_events sa in
  (F.make F.And (SAtom.fold (fun a l -> make_literal a::l) sa []), ord, evts)

and make_literal = function
  | Atom.True -> F.f_true
  | Atom.False -> F.f_false
  | Atom.Comp (x, op, y) ->
      let tx = make_term x in
      let ty = make_term y in
      F.make_lit (make_op_comp op) [tx; ty]
  | Atom.Ite (la, a1, a2) -> 
      let (f, _, _) = make_formula_set la in
      let a1 = make_literal a1 in
      let a2 = make_literal a2 in
      let ff1 = F.make F.Imp [f; a1] in
      let ff2 = F.make F.Imp [F.make F.Not [f]; a2] in
      F.make F.And [ff1; ff2]

let make_formula atoms =
  let sa, ord = split_order_array atoms in
  let evts = get_events sa in
  (F.make F.And (SAtom.fold (fun a l -> make_literal a::l) sa []), ord, evts)

module HAA = Hashtbl.Make (ArrayAtom)

let make_formula =
  let cache = HAA.create 200001 in
  fun atoms ->
    try HAA.find cache atoms
    with Not_found ->
      let f = make_formula atoms in
      HAA.add cache atoms f;
      f

let make_formula array =
  TimeFormula.start ();
  let f = make_formula array in
  TimeFormula.pause ();
  f

let make_formula_set satom =
  TimeFormula.start ();
  let f = make_formula_set satom in
  TimeFormula.pause ();
  f

(*
let make_disjunction nodes = F.make F.Or (List.map make_formula nodes)


let make_conjuct atoms1 atoms2 =
  let l = Array.fold_left (fun l a -> make_literal a::l) [] atoms1 in
  let l = Array.fold_left (fun l a -> make_literal a::l) l atoms2 in
  F.make F.And l
 *)

let evt_cnt = ref HMap.empty
let evt_ord = ref HMap.empty
let new_atoms = ref []

let make_event d p v vi = 
  let eid = (try HMap.find p !evt_cnt with Not_found -> 0) + 1 in
  evt_cnt := HMap.add p eid !evt_cnt;
  let eid = Hstring.make ("_e" ^ (string_of_int eid)) in
  let ord = try HMap.find p !evt_ord with Not_found -> [] in
  evt_ord := HMap.add p (Elem (eid, Glob) :: ord) !evt_ord;
  let tevt = Access (Hstring.make "_e", [p ; eid]) in
  let tdir = Field (tevt, Hstring.make "_dir") in
  let tvar = Field (tevt, Hstring.make "_var") in
  let tval = Field (tevt, Hstring.make "_val") in
  let adir = Atom.Comp (tdir, Eq, Elem (Hstring.make d, Constr)) in
  let avar = Atom.Comp (tvar, Eq,
                      Elem (Hstring.make ("_V" ^ (Hstring.view v)), Constr)) in
  new_atoms := adir :: avar :: !new_atoms;
  tval

let event_of_term t = match t, [] with
  | Elem (v, Glob), vi | Access (v, vi), _ when Smt.Symbol.is_weak v ->
      make_event "_W" (Hstring.make "#0") v vi
  | _ -> t

let events_of_a = function
  | Atom.Comp (t1, op, t2) ->
     let t1' = event_of_term t1 in
     let t2' = event_of_term t2 in
     Atom.Comp (t1', op, t2')
  | a -> a

let events_of_dnf dnf =
  List.fold_left (fun dnf sa ->
    evt_cnt := HMap.empty; evt_ord := HMap.empty; new_atoms := [];
    let sa = SAtom.fold (fun a -> SAtom.add (events_of_a a)) sa SAtom.empty in
    let sa = List.fold_left (fun sa a -> SAtom.add a sa) sa !new_atoms in
    let sa = HMap.fold (fun p tl ->
      SAtom.add (Atom.Comp (Access ((Hstring.make "_o"), [p]), Eq, List tl))
    ) !evt_ord sa in (* should be no event order for #0 *)
    sa :: dnf
  ) [] dnf

let make_init_dnfs s n nb_procs =
  let { init_cdnf } = Hashtbl.find s.t_init_instances nb_procs in
  List.rev_map (fun dnf ->
    List.rev_map (make_formula_set) (events_of_dnf dnf)
  ) init_cdnf

let get_user_invs s nb_procs =
  let { init_invs } =  Hashtbl.find s.t_init_instances nb_procs in
  List.rev_map (fun a ->
    let (f, _, _) = make_formula a in
    F.make F.Not [f]) init_invs

let unsafe_conj { tag = id; cube = cube } nb_procs invs (init, iord, ievts) =
  if debug_smt then eprintf ">>> [smt] safety with: %a@." F.print init;
  SMT.clear ();
  SMT.assume ~id (distinct_vars nb_procs);
  List.iter (SMT.assume ~id) invs;
  let (f, ord, evts) = make_formula_set cube.Cube.litterals in
  if debug_smt then eprintf "[smt] safety: %a and %a@." F.print f F.print init;
  SMT.assume ~id init;
  SMT.assume ~id f;
  let ord = HMap.fold (fun p pord ord -> HMap.add p pord ord) iord ord in
  let evts = HMap.fold (fun p pevts evts -> HMap.add p pevts evts) ievts evts in
  SMT.assume ~id (make_orders ~fp:false evts ord);
  SMT.check ~fp:false ()

let unsafe_dnf node nb_procs invs dnf =
  try
    let uc =
      List.fold_left (fun accuc init ->
        try 
          unsafe_conj node nb_procs invs init;
          raise Exit
        with Smt.Unsat uc -> List.rev_append uc accuc)
        [] dnf in
    raise (Smt.Unsat uc)
  with Exit -> ()

let unsafe_cdnf s n =
  let nb_procs = List.length (Node.variables n) in
  let cdnf_init = make_init_dnfs s n nb_procs in
  let invs = get_user_invs s nb_procs in
  List.iter (unsafe_dnf n nb_procs invs) cdnf_init

let unsafe s n = unsafe_cdnf s n


let reached args s sa =
  SMT.clear ();
  SMT.assume ~id:0 (distinct_vars (List.length args));
  let (f, _, _) = make_formula_set (SAtom.union sa s) in
  SMT.assume ~id:0 f;
  SMT.check ~fp:false ()


let assume_goal_no_check ?(fp=false) { tag = id; cube = cube } =
  SMT.clear ();
  SMT.assume ~id (distinct_vars (List.length cube.Cube.vars));
  let (f, ord, evts) = make_formula cube.Cube.array in
  if debug_smt then eprintf "[smt] goal g: %a@." F.print f;
  SMT.assume ~id f;
  SMT.assume ~id (make_orders ~fp evts ord)

let assume_node_no_check ?(fp=false) { tag = id } ap =
  let (f, ord, evts) = make_formula ap in
  let f = F.make F.Not [f] in
  if debug_smt then eprintf "[smt] assume node: %a@." F.print f;
  SMT.assume ~id f;
  SMT.assume ~id (F.make F.Not [(make_orders ~fp evts ord)])

let assume_goal ?(fp=false) n =
  assume_goal_no_check ~fp n;
  SMT.check ~fp ()

let assume_node ?(fp=false) n ap =
  assume_node_no_check ~fp n ap;
  SMT.check ~fp ()


let run ?(fp=false) () = SMT.check ~fp ()

let check_guard args sa reqs =
  SMT.clear ();
  SMT.assume ~id:0 (distinct_vars (List.length args));
  let (f, _, _) = make_formula_set (SAtom.union sa reqs) in
  SMT.assume ~id:0 f;
  SMT.check ~fp:false ()

let assume_goal_nodes ?(fp=false) { tag = id; cube = cube } nodes =
  SMT.clear ();
  SMT.assume ~id (distinct_vars (List.length cube.Cube.vars));
  let (f, ord, evts) = make_formula cube.Cube.array in
  if debug_smt then eprintf "[smt] goal g: %a@." F.print f;
  SMT.assume ~id f;
  SMT.assume ~id (make_orders ~fp evts ord);
  List.iter (fun (n, a) -> assume_node_no_check ~fp n a) nodes;
  SMT.check ~fp ()

let init () =
  SMT.init_axioms ()
