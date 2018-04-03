open Types
open Ptree

let hNone = Hstring.make ""

let rec process_event_term fn = function
  | Recv (p, q, c) -> fn p q c
  | Arith (t, c) -> Arith (process_event_term fn t, c)
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

let fix_recv_thr t p q c =
  let pdef = not (Hstring.equal p hNone) in
  match pdef, t with
  | false, Some t -> Recv (t, q, c)
  | true, None -> Recv (p, q, c)
  | false, None -> Recv (p, q, c) (*failwith "No thread in recv"*)
  | true, Some t -> if Hstring.equal p t then Recv (p, q, c)
                    else failwith "Threads differ in recv"

let fix_recv_assign t (v, pgu) =
  (v, process_event_pgu (fix_recv_thr t) pgu)

let fix_recv_upd t upd =
  { upd with pup_swts = process_event_pswts (fix_recv_thr t) upd.pup_swts }

let fix_recv_send t (p, q, c, pt) =
  let pdef = not (Hstring.equal p hNone) in
  let pt = process_event_pterm (fix_recv_thr t) pt in
  match pdef, t with
  | false, Some t -> (t, q, c, pt)
  | true, None -> (p, q, c, pt)
  | false, None -> (p, q, c, pt) (*failwith "No thread in send"*)
  | true, Some t ->
     if Hstring.equal p t then (p, q, c, pt)
     else failwith "Threads differ in send"

let fix_recv_expr t expr =
  process_event_pform (fix_recv_thr t) expr

let forbid_recv expr =
  let _ = process_event_pform (fun _ _ _ ->
    failwith "Recv not allowed in init / unsafe / invariant") expr in ()
