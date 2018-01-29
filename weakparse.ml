
open Types
open Ptree

let hNone = Hstring.make ""

let rec process_event_term (fnr, fnf) = function
  | Read (p, v, vi) -> fnr p v vi
  | Fence (p) -> fnf p
  | Arith (t, c) -> Arith (process_event_term (fnr, fnf) t, c)
  | t -> t

let rec process_event_atom fn = function
  | Atom.Comp (t1, op, t2) ->
     Atom.Comp (process_event_term fn t1, op, process_event_term fn t2)
  | Atom.Ite (sa, a1, a2) ->
     Atom.Ite (SAtom.fold (fun a sa ->
       SAtom.add (process_event_atom fn a) sa) sa SAtom.empty,
       process_event_atom fn a1, process_event_atom fn a2)
  | t -> t

let process_event_pterm fn = function
  | TTerm t -> TTerm (process_event_term fn t)
  | t -> t

let process_event_patom fn = function
  | AAtom a -> AAtom (process_event_atom fn a)
  | AEq (t1, t2) -> AEq (process_event_pterm fn t1, process_event_pterm fn t2)
  | ANeq (t1, t2) -> ANeq (process_event_pterm fn t1, process_event_pterm fn t2)
  | ALe (t1, t2) -> ALe (process_event_pterm fn t1, process_event_pterm fn t2)
  | ALt (t1, t2) -> ALt (process_event_pterm fn t1, process_event_pterm fn t2)
  | t -> t

let rec process_event_pform fn = function
  | PAtom a -> PAtom (process_event_patom fn a)
  | PNot f -> PNot (process_event_pform fn f)
  | PAnd fl -> PAnd (List.map (process_event_pform fn) fl)
  | POr fl -> POr (List.map (process_event_pform fn) fl)
  | PImp (f1, f2) -> PImp (process_event_pform fn f1, process_event_pform fn f2)
  | PEquiv (f1, f2) ->
     PEquiv (process_event_pform fn f1, process_event_pform fn f2)
  | PIte (f1, f2, f3) ->
     PIte (process_event_pform fn f1, process_event_pform fn f2,
           process_event_pform fn f3)
  | PForall (vl, f) -> PForall (vl, process_event_pform fn f)
  | PExists (vl, f) -> PExists (vl, process_event_pform fn f)
  | PForall_other (vl, f) -> PForall_other (vl, process_event_pform fn f)
  | PExists_other (vl, f) -> PExists_other (vl, process_event_pform fn f)

let process_event_pswts fn s =
  List.map (fun (f, t) -> process_event_pform fn f, process_event_pterm fn t) s

let process_event_pgu fn = function
  | PUTerm t -> PUTerm (process_event_pterm fn t)
  | PUCase s -> PUCase (process_event_pswts fn s)

let fix_rd_thr t p v vi =
  let pdef = not (Hstring.equal p hNone) in
  match pdef, t with
  | false, Some t -> Read (t, v, vi)
  | true, None -> Read (p, v, vi)
  | false, None -> failwith "No thread in read"
  | true, Some t -> if Hstring.equal p t then Read (p, v, vi)
                    else failwith "Threads differ in read"

let fix_f_thr t p =
  let pdef = not (Hstring.equal p hNone) in
  match pdef, t with
  | false, Some t -> Fence (t)
  | true, None -> Fence (p)
  | false, None -> failwith "No thread in fence"
  | true, Some t -> if Hstring.equal p t then Fence (p)
                    else failwith "Threads differ in fence"

let no_fce _ _ =
  failwith "Fence not allowed in this context"

let fix_rd_upd t upd =
  { upd with pup_swts = process_event_pswts
      ((fix_rd_thr t), (no_fce t)) upd.pup_swts }

let fix_rd_assign t (v, pgu) =
  (v, process_event_pgu
      ((fix_rd_thr t), (no_fce t)) pgu)

let fix_rd_write t (p, v, vi, pgu) =
  let pgu = process_event_pgu ((fix_rd_thr t), (no_fce t)) pgu in
  match p, t with
  | None, Some p -> (p, v, vi, pgu)
  | Some p, None -> (p, v, vi, pgu)
  | None, None -> failwith "No thread in write"
  | Some p, Some q ->
     if Hstring.equal p q then (p, v, vi, pgu)
     else failwith "Threads differ in write"

let fix_rd_expr t expr =
  process_event_pform ((fix_rd_thr t), (fix_f_thr t)) expr

let fix_rd_init expr =
  process_event_pform ((fun p v vi ->
    if Hstring.equal p hNone then
      match vi with
      | [] -> Elem (v, Glob)
      | _ -> Access (v, vi)
    else
      failwith "Thread not allowed in init"
    ), (no_fce None)) expr
