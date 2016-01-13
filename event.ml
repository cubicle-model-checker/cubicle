
open Format

type dir = ERead | EWrite

type t = {
    uid : int;
    tid : Variable.t;
    dir : dir;
    var : Hstring.t * Variable.t list;
  }

module IntMap = Map.Make(struct type t = int let compare = compare end)

type structure = t list IntMap.t

type str = t list Map.Make(String).t

let empty_struct = IntMap.empty

let make =
  let cpt = ref 0 in
  fun p (v, vi) d ->
  cpt := !cpt + 1;
  { uid = !cpt; tid = p; dir = d; var = (v, vi) }
		     
let print_var fmt (v, vi) =
  if vi = [] then fprintf fmt "\\texttt{%a}" Hstring.print v
  else fprintf fmt "\\texttt{%a}[%a]"
 	       Hstring.print v (Hstring.print_list ", ") vi

let print_rd fmt (p, v, vi) =
  fprintf fmt "read(%a, %a)" Hstring.print p print_var (v, vi)

let print_evtval fmt e =
  let dir = if e.dir = ERead then "R" else "W" in
  fprintf fmt "event(%d, %a, %s, %a)"
    e.uid Hstring.print e.tid dir print_var e.var

let replace str s1 s2 =
  Str.global_replace (Str.regexp_string s1) s2 str

let event_name e = "e" ^ (string_of_int e.uid)

let smt_var_name v = "_V" ^ (replace (Hstring.view v) "#" "p")

let print_event_decl fmt e =
  let en = event_name e in
  let tid = replace (Hstring.view e.tid) "#" "p" in	   
  let dir = if e.dir = ERead then "R" else "W" in
  let var = smt_var_name (fst e.var) in
(*fprintf fmt "logic %s : event\n" en;
  fprintf fmt "axiom %s : %s.uid = %d and %s.tid = %s" en en e.uid en tid;
  fprintf fmt " and %s.dir = %s and %s.loc = %s\n" en dir en var*)
  fprintf fmt "logic %s : int\n" en;
  fprintf fmt "axiom %s : e(%s).tid = %s" en en tid;
  fprintf fmt " and e(%s).dir = %s and e(%s).loc = %s\n" en dir en var	   

let print_event_decls fmt el =
  List.iter (print_event_decl fmt) el

let rec print_po_pairs fmt = function
  |  e1 :: ((e2 :: _ :: _) as el) ->
      fprintf fmt " and po(%s, %s)" (event_name e1) (event_name e2);
      fprintf fmt " and not po(%s, %s)" (event_name e2) (event_name e1);
      print_po_pairs fmt el
  |  e1 :: e2 :: [] ->
      fprintf fmt " and po(%s, %s)" (event_name e1) (event_name e2);
      fprintf fmt " and not po(%s, %s)" (event_name e2) (event_name e1)
  | _ -> ()

let print_events_po fmt events =
  IntMap.iter (fun _ el -> print_po_pairs fmt el) events;
  fprintf fmt "\n"

let print_acyclic_rel fmt e =
  let en = event_name e in
  fprintf fmt
      " and not po_loc_U_com(%s, %s) and not co_U_prop(%s, %s)\n"
      en en en en

let print_acyclic_relations fmt esl =
  List.iter (print_acyclic_rel fmt) esl

let unique_events esl =
  let uel = ref [] in
  List.iter (IntMap.iter (fun _ -> List.iter (fun e ->
    if not (List.exists (fun ex -> ex.uid = e.uid) !uel) then uel := e :: !uel
  ))) esl;
  !uel

let axiom fp =
  let ax1 = "
type direction = R | W
type event = { tid : int; dir : direction; loc : tso_var; val : int }
logic e : int -> event
logic po : int, int -> prop
logic rf : int, int -> prop
logic co : int, int -> prop
logic fences : int, int -> prop
" in
  let ax2 =
"
logic po_loc : int, int -> prop
axiom po_loc :
  forall e1, e2 : int.
  po(e1, e2) and e(e1).loc = e(e2).loc
  <-> po_loc(e1, e2)
logic rfe : int, int -> prop
axiom rfe :
  forall e1, e2 : int.
  rf(e1, e2) and e(e1).tid <> e(e2).tid
  <-> rfe(e1, e2)
logic fr : int, int -> prop
axiom fr :
  forall e1, e2 : int. not fr(e1, e2)
logic com : int, int -> prop
axiom com :
  forall e1, e2 : int.
  co(e1, e2) or rf(e1, e2) or fr(e1, e2)
  <-> com(e1, e2)
logic ppo : int, int -> prop
axiom ppo_tso :
  forall e1, e2 : int.
  po(e1, e2) and not (e(e1).dir = W and e(e2).dir = R)
  <-> ppo(e1, e2)
logic propg : int, int -> prop
axiom propg_tso :
  forall e1, e2 : int.
  ppo(e1, e2) or fences(e1, e2) or rfe(e1, e2) (*or fr(e1, e2)*)
  <-> propg(e1, e2)
logic po_loc_U_com : int, int -> prop
axiom po_loc_U_com :
  forall e1, e2 : int.
  po_loc(e1, e2) or com(e1, e2) -> po_loc_U_com(e1, e2)
axiom po_loc_U_com_t :
  forall e1, e2, e3 : int.
  po_loc_U_com(e1, e2) and po_loc_U_com(e2, e3) -> po_loc_U_com(e1, e3)
logic co_U_prop : int, int -> prop
axiom co_U_prop :
  forall e1, e2 : int.
  co(e1, e2) or propg(e1, e2) -> co_U_prop(e1, e2)
axiom co_U_prop_t :
  forall e1, e2, e3 : int.
  co_U_prop(e1, e2) and co_U_prop(e2, e3) -> co_U_prop(e1, e3)
" in
  if fp then ax1 else ax1 ^ ax2
	      
(*
let axiom fp =
  let ax1 = "
type direction = R | W
type event = { uid : int; tid : int; dir : direction; loc : tso_var; val : int }
logic po : event, event -> prop
logic rf : event, event -> prop
logic co : event, event -> prop
logic fences : event, event -> prop
axiom diff_evt:
  forall e1, e2 : event. e1 <> e2 -> e1.uid <> e2.uid
" in
  let ax2 =
"  logic po_loc : event, event -> prop
axiom po_loc :
  forall e1, e2 : event.
  po(e1, e2) and e1.loc = e2.loc
  <-> po_loc(e1, e2)
logic rfe : event, event -> prop
axiom rfe :
  forall e1, e2 : event.
  rf(e1, e2) and e1.tid <> e2.tid
  <-> rfe(e1, e2)
logic fr : event, event -> prop
axiom fr :
  forall e1, e2 : event. not fr(e1, e2)
logic com : event, event -> prop
axiom com :
  forall e1, e2 : event.
  co(e1, e2) or rf(e1, e2) or fr(e1, e2)
  <-> com(e1, e2)
logic ppo : event, event -> prop
axiom ppo_tso :
  forall e1, e2 : event.
  po(e1, e2) and not (e1.dir = W and e2.dir = R)
  <-> ppo(e1, e2)
logic propg : event, event -> prop
axiom propg_tso :
  forall e1, e2 : event.
  ppo(e1, e2) or fences(e1, e2) or rfe(e1, e2) (*or fr(e1, e2)*)
  <-> propg(e1, e2)
logic po_loc_U_com : event, event -> prop
axiom po_loc_U_com :
  forall e1, e2 : event.
  po_loc(e1, e2) or com(e1, e2) -> po_loc_U_com(e1, e2)
axiom po_loc_U_com_t :
  forall e1, e2, e3 : event.
  po_loc_U_com(e1, e2) and po_loc_U_com(e2, e3) -> po_loc_U_com(e1, e3)
logic co_U_prop : event, event -> prop
axiom co_U_prop :
  forall e1, e2 : event.
  co(e1, e2) or propg(e1, e2) -> co_U_prop(e1, e2)
axiom co_U_prop_t :
  forall e1, e2, e3 : event.
  co_U_prop(e1, e2) and co_U_prop(e2, e3) -> co_U_prop(e1, e3)
" in
  if fp then ax1 else ax1 ^ ax2
 *)
   
