
open Format

type dir = ERead | EWrite

type t = {
    uid : int;
    tid : Variable.t;
    dir : dir;
    var : Hstring.t * Variable.t list; }

module IntMap = Map.Make(struct type t = int let compare = compare end)

type structure = {
    events : t IntMap.t;
    po_f : int list IntMap.t; }

let empty_struct = { events = IntMap.empty; po_f = IntMap.empty }

let make uid tid dir var =
  { uid; tid; dir; var }

let name e = "e" ^ (string_of_int e.uid)

let int_of_tid e =
  let tid = Hstring.view e.tid in
  let tid = String.sub tid 1 ((String.length tid)-1) in
  int_of_string tid

let print_var fmt (v, vi) =
  if vi = [] then fprintf fmt "\\texttt{%a}" Hstring.print v
  else fprintf fmt "\\texttt{%a}[%a]"
 	       Hstring.print v (Hstring.print_list ", ") vi

let print fmt { uid; tid; dir; var } =
  let dir = if dir = ERead then "R" else "W" in
  fprintf fmt "event(%d, %a, %s, %a)" uid Hstring.print tid dir print_var var

let print_rd fmt (p, v, vi) =
  fprintf fmt "read(%a, %a)" Hstring.print p print_var (v, vi)



let axiom_base = "
type direction = _R | _W
type event = { tid : int; dir : direction; loc : tso_var; val : int }
logic e : int -> event
logic po : int, int -> prop
logic rf : int, int -> prop
logic co : int, int -> prop
logic fence : int, int -> prop
"
let axiom_rels = "
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
  po(e1, e2) and not (e(e1).dir = _W and e(e2).dir = _R)
  <-> ppo(e1, e2)
logic propg : int, int -> prop
axiom propg_tso :
  forall e1, e2 : int.
  ppo(e1, e2) or fence(e1, e2) or rfe(e1, e2) (*or fr(e1, e2)*)
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
"


let replace str s1 s2 =
  Str.global_replace (Str.regexp_string s1) s2 str

let print_var_name fmt v =
  fprintf fmt "_V%s" (replace (Hstring.view v) "#" "p")

let unique_events esl =
  let uel = ref [] in
  List.iter (fun es -> IntMap.iter (fun _ e ->
    if not (List.exists (fun ex -> ex.uid = e.uid) !uel) then uel := e :: !uel
  ) es.events) esl;
  !uel

let print_hset_sep sep pfun fmt set =
  let first = ref true in
  Hstring.H.iter (fun k v ->
    if !first then begin pfun fmt (k, v); first := false end
    else fprintf fmt " %s %a" sep pfun (k, v)) set

let print_decls fmt fp tso_vars esl =
  if Hstring.H.length tso_vars > 0 then begin

    (* Additional proc #0 for initial events *)
    fprintf fmt "\nlogic p0 : int\n";
    fprintf fmt "axiom p0 : p0 <> p1 <> p2 <> p3 <> p4 <> p5";
    fprintf fmt " <> p6 <> p7 <> p8 <> p9 <> p10\n\n";

    (* List of TSO variables *) (* could use their original names *)
    fprintf fmt "type tso_var = %a\n" (print_hset_sep "|"
      (fun fmt (f, (fx, args, ret)) -> print_var_name fmt f)) tso_vars;

    (* Axiomatization *)
    fprintf fmt "%s" axiom_base;
    if not fp then fprintf fmt "%s" axiom_rels;
    fprintf fmt "\n";

    (* Declaration of events *)
    List.iter (fun e ->
      fprintf fmt "logic %s : int\n" (name e)
    ) (List.rev (unique_events esl));
    fprintf fmt "\n";

  end

let gen_po es =
  let rec aux po = function
    | e1 :: ((e2 :: _) as el) -> aux ((e1, e2) :: po) el
    | _ -> po
  in
  IntMap.fold (fun _ tpof po ->
    aux po (List.filter (fun e -> e <> 0) tpof)
  ) es.po_f []

let gen_co es =
  let writes = IntMap.filter (fun _ e -> e.dir = EWrite) es.events in
  let iwrites, writes = IntMap.partition (fun _ e ->
    Hstring.view e.tid = "#0") writes in
  IntMap.fold (fun iw _ co ->
    IntMap.fold (fun w _ co -> (iw, w) :: co) writes co
  ) iwrites []

let gen_fence es =
  let rec split_at_first_fence ll = function
    | 0 :: rl | ([] as rl) -> ll, rl
    | e :: rl -> split_at_first_fence (e :: ll) rl
  in
  let rec first_event dir = function
    | [] -> None
    | e :: el ->
       try
	 let e' = IntMap.find e es.events in
	 if e'.dir = dir then Some e else first_event dir el
       with Not_found -> failwith "Event.gen_fence : unknown event id"
  in
  let rec aux fence ll rl = match rl with
    | [] -> fence
    | _ ->
       let ll, rl = split_at_first_fence ll rl in
       match first_event EWrite ll, first_event ERead rl with
       | Some w, Some r -> aux ((w, r) :: fence) ll rl
       | _, _ -> aux fence ll rl
  in
  IntMap.fold (fun _ tpof fence ->
    aux fence [] tpof
  ) es.po_f []
