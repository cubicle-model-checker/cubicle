(**************************************************************************)
(*                                                                        *)
(*                       Extension to Cubicle                             *)
(*                                                                        *)
(*                       Copyright (C) 2018                               *)
(*                                                                        *)
(*                        Philippe Queinnec                               *)
(*                          INP Toulouse                                  *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

open Printf
open Ast
open Types

let concat_map sep op list =
  String.concat sep (List.map op list)

(* ================ *)

let view_consts consts =
  "CONSTANT\n  "
  ^ String.concat ",\n  " ("proc" :: List.map (fun (_, c, _) -> Hstring.view c) consts)
  ^ "\n"

(* ================ *)

(* Generate the user type definitions: each constructor is a symbol, and the type is the set of its constructors. *)
let view_type_defs type_defs =
  let view_type (_, (name, constructors)) =
    if (Hstring.view name = "mbool") then "" (* don't declare mbool. *)
    else
      let consnames = List.map Hstring.view constructors in
      concat_map "" (fun c -> sprintf "%s == \"%s\"\n" c c) consnames
      ^ sprintf "%s == { %s }\n" (Hstring.view name) (String.concat ", " consnames)
  in concat_map "" view_type type_defs

(* ================ *)

let get_variables_names globals arrays =
      (List.map (fun (_,n,_) -> Hstring.view n) globals)
      @ (List.map (fun (_,n,_) -> Hstring.view n) arrays)

(* Generate the variables (globals and arrays) declaration. *)
let view_variables varnames =
  (sprintf "VARIABLES\n  %s\n" (String.concat ",\n  " varnames))
  ^ "\n"
  ^ (sprintf "variables == <<%s>>\n" (String.concat "," varnames))

(* ================ *)

let str_op_comp = function Eq -> "=" | Lt -> "<" | Le -> "<=" | Neq -> "#"

(* Types.Term only provides a print function. *)
(* TODO : will probably be forced to reimplement it to ensure TLA+ syntax.
 * Currently, it works! *)
let view_term t =
  Term.print Format.str_formatter t;
  Format.flush_str_formatter ()
  |> Str.global_replace (Str.regexp "@MTrue") "TRUE"
  |> Str.global_replace (Str.regexp "@MFalse") "FALSE"
(* |> Str.global_replace (Str.regexp "#") "proc" *)

let rec view_atom = function
    | Atom.True ->  "TRUE"
    | Atom.False -> "FALSE"
    | Atom.Comp (x, op, y) ->
       sprintf "%s %s %s" (view_term x) (str_op_comp op) (view_term y)
    | Atom.Ite (la, a1, a2) ->
        sprintf "(IF %s THEN %s ELSE %s)" (view_satoms la) (view_atom a1) (view_atom a2)
and
 view_satoms sa =
  "(" ^ concat_map " /\\ " view_atom (SAtom.elements sa) ^ ")"

(* Given a list of variables, generate the universal/existential quantification *)
let varlist_quantify quantifier varlist =
  match varlist with
  | [] -> ""
  | _  -> Printf.sprintf "%s %s \\in proc : " quantifier (concat_map ", " Hstring.view varlist)

(* Given a list of variables, generate the formula stating they are all different.
 * (generate an empty sring if one variable or none) *)
let varlist_alldistincts varlist =
  let rec allcouples varlist =
    match varlist with
    | [] -> []
    | _::[] -> []
    | x::l' -> (List.map (fun y -> (x,y)) l') @ (allcouples l')
  in
  concat_map " /\\ " (fun (x,y) -> Hstring.view x ^ " # " ^ Hstring.view y) (allcouples varlist)

(* ================ *)

let view_type t =
  if Hstring.equal t Smt.Type.type_int then "Int"
  else if Hstring.equal t Smt.Type.type_real then "Real"
  else if Hstring.equal t Smt.Type.type_bool then "BOOLEAN"
  else if Hstring.equal t Smt.Type.type_proc then "proc"
  else if Hstring.view t = "mbool" then "BOOLEAN"
  else Hstring.view t

(* Generate the typeinvariant formula of the global variables and of the arrays. *)
let typeinvariant globals arrays =
  concat_map "" (fun (_,var,typ) -> sprintf "  /\\ %s \\in %s\n" (Hstring.view var) (view_type typ)) globals
  ^ concat_map ""
      (fun (_,var,(typlist,typ)) ->
        sprintf "  /\\ %s \\in [ %s -> %s ]\n" (Hstring.view var) (concat_map " \\X " view_type typlist) (view_type typ))
      arrays

let view_typeinvariant globals arrays =
  "TypeInvariant ==\n" ^ typeinvariant globals arrays

(* ================ *)

(* Generate a list of invariants *)
let view_props basename invs =
  let view_inv num (_, varlist, inv) =
    sprintf "%s%d == " basename num
    ^ sprintf "%s" (varlist_quantify "\\A" varlist)
    ^ (if List.length varlist <= 1 then ""
       else sprintf "%s => " (varlist_alldistincts varlist))
    ^ sprintf "\\neg %s\n" (view_satoms inv)
  in String.concat "" (List.mapi view_inv invs)

let view_invs invs =
  if invs = [] then ""
  else
    view_props "invariant" invs
    ^ sprintf "invariant == %s\n" (String.concat " /\\ " (List.mapi (fun num _ -> "invariant" ^ string_of_int num) invs))

let view_unsafe = view_props "unsafe"

(* ================ *)

(* Like List.map but discard None *)
let filter_map f l =
  let rec loop acc = function
    | [] -> acc
    | h :: t ->
      match f h with
      | None -> loop acc t
      | Some x -> loop (x::acc) t
  in loop [] l

(* Generate the init formula in three steps: the assignments, the type invariant for the uninitialized variables and lastly the arbitrary formula (hoping that TLC will manage to handle it) *)
(* XXXX note that a quantified init (init (p) {...}) is handled exactly as a non-quantified init.
The reason is that a quantified init is (almost exclusively - see below) used
to initialized arrays (X[p] = ...) and it's translated in TLA+ in a global
initialisation of the array (X = [ p \in proc |-> ... ]). The one peculiar
case is to initialize a variable to something else: X <> p which would means X
is anything except a valid proc value. This is impossible to handle in TLA+ as
X is also declared to be a proc. *)
let view_init globals arrays init hasinvariants =
  let view_init_term2 var value =
    match var with
    | Elem (s, _) -> sprintf "%s = %s\n" (Hstring.view s) (view_term value)
    | Access (a, li) -> sprintf "%s = [ %s \\in proc |-> %s ]\n" (Hstring.view a) (concat_map ", " Hstring.view li) (view_term value)
    | _ -> failwith "Init term not in the form 'var = val' or 'var[x,...] = val'"
  in
  let view_init_term_assign t =
    match t with
    | Atom.Comp (t1, Eq, t2) -> Some ("  /\\ " ^ view_init_term2 t1 t2)
    | _ -> None (* ignored in first pass *)
  in
  let view_init_term_formula t =
    match t with
    | Atom.Comp (_, Eq, _) -> None (* already handled *)
    | _ -> Printf.eprintf "warn: Init term not in the form 'expr = expr': %s\n" (view_atom t);
           Some ("  /\\ " ^ view_atom t ^ "\n")
  in
  match init with
  | (_, varlist, ([dnf])) ->
      "_Init ==\n"
      ^ String.concat "" (filter_map view_init_term_assign (SAtom.elements dnf))
      ^ "  /\\ TypeInvariant\n"
      ^ String.concat "" (filter_map view_init_term_formula (SAtom.elements dnf))
      ^ (if hasinvariants then " /\\ invariant\n" else "")
  | _ -> failwith "Unexpected multiple inits"

(* ================ *)

(* Formula stating that var is different from all variables in varlist *)
let varlist_distincts var varlist =
  concat_map " /\\ " (fun y -> Hstring.view var ^ " # " ^ Hstring.view y) varlist

(* Non-quantified require: a simple conjunction *)
let view_reqs reqs =
  if (SAtom.elements reqs) =  [Atom.True] then "" (* transition with no requires *)
  else sprintf "  /\\ %s\n" (view_satoms reqs)

(* Quantified (forall_other) require, disjoint from the potential parameters of the transition *)
let view_ureq args (v, dnf) =
  sprintf "  /\\ \\A %s \\in proc : " (Hstring.view v)
  ^ (if args = [] then "" else (varlist_distincts v args) ^ " => ")
  ^ concat_map " \\/ " view_satoms dnf
  ^ "\n"

(* Case value in an assignement *)
let rec view_swts swts =
  let view_swt (sa,t) = sprintf "IF %s THEN %s" (view_satoms sa) (view_term t)
  in
  match swts with
    | [] -> failwith "Impossible empty switch"
    | [(_,t)] -> (view_term t)  (* last case is always TRUE -> ... *)
    | swt::swts' -> (view_swt swt) ^ " ELSE " ^ (view_swts swts')

(* Assignment to a global variable *)
let view_assign (v, upd) =
      match upd with
      | Ast.UTerm t    -> sprintf "  /\\ %s' = %s\n" (Hstring.view v) (view_term t)
      | Ast.UCase swts -> sprintf "  /\\ %s' = %s\n" (Hstring.view v) (view_swts swts)

(* Assignment to an array *)
let view_upd upd =
  sprintf "  /\\ %s' = [ %s \\in proc |-> " (Hstring.view upd.up_arr) (concat_map ", " Hstring.view upd.up_arg)
  ^ view_swts upd.up_swts
  ^ " ]\n"

(* Non-deterministic assignment to a global variable : x = ? (necessarily a proc) *)
let view_nondet nondet =
  sprintf "  /\\ %s' \\in proc\n" (Hstring.view nondet)

(* Generate the unchanged variables by making the difference between all the variables and the variables updated in the transition. *)
let view_unchanged transition_info varnames =
  let assigns = List.map (fun (v,_) -> Hstring.view v) transition_info.tr_assigns in
  let upds = List.map (fun v -> Hstring.view v.up_arr) transition_info.tr_upds in
  let nondets = List.map Hstring.view transition_info.tr_nondets in
  let transvar = assigns @ upds @ nondets in
  let notassigned = List.filter (fun v -> not (List.mem v transvar)) varnames in
  match notassigned with
  | [] -> ""
  | _ -> sprintf "  /\\ UNCHANGED << %s >>\n" (String.concat ", " notassigned)

(* Generate a transition *)
let view_transition_info varnames transition_info =
  sprintf "%s == " (Hstring.view transition_info.tr_name)
  ^ sprintf "%s\n" (varlist_quantify "\\E" transition_info.tr_args)
  ^ (if List.length transition_info.tr_args <= 1 then ""
     else sprintf "  /\\ %s\n" (varlist_alldistincts transition_info.tr_args))
  ^ view_reqs transition_info.tr_reqs
  ^ concat_map "" (view_ureq transition_info.tr_args) transition_info.tr_ureq
  ^ concat_map "" view_assign transition_info.tr_assigns
  ^ concat_map "" view_upd transition_info.tr_upds
  ^ concat_map "" view_nondet transition_info.tr_nondets
  ^ view_unchanged transition_info varnames

(* Generate all the transitions *)
let view_trans trans varnames =
  concat_map "\n" (view_transition_info varnames) trans

let view_next trans hasinvariants =
  sprintf "_Next == (%s)%s\n"
    (concat_map " \\/ " (fun t -> Hstring.view t.tr_name) trans)
    (if hasinvariants then " /\\ invariant'" else "")

(* use _Init, _Next, _Fairness to reduce probability of clash *)
let view_spec =
  "_Fairness == WF_variables(_Next)\n"
  ^ "\n"
  ^ "Spec == _Init /\\ [][_Next]_variables /\\ _Fairness\n"

(* ================ *)

(* Build a new transition system where transition names have been made unique *)
let make_unique_tr_names trans =
  (* add successive "_" until the name is not found *)
  let rec build_unique name names =
    if Hstring.HSet.mem name names then build_unique (Hstring.make (Hstring.view name ^ "_")) names
    else name
  in
  let (res, _) = List.fold_left
      (fun (newtrans, names) tr ->
        let newname = build_unique tr.tr_name names in
        let newtr = { tr with tr_name = newname } in
        (newtr :: newtrans, Hstring.HSet.add newname names))
      ([], Hstring.HSet.empty) trans
  in res

exception NameClashWithTLA of string

let check_clash symbols =
  let reservedwords =
    [ "ASSUMPTION"; "AXIOM"; "BOOLEAN"; "CASE"; "CONSTANT"; "CONSTANTS"; "EXCEPT";
      "EXTENDS"; "FALSE"; "IF"; "INSTANCE"; "LOCAL"; "MODULE"; "OTHER"; "STRING";
      "THEOREM"; "TRUE"; "VARIABLE"; "VARIABLES"; "WITH"; "BY"; "OBVIOUS"; "HAVE";
      "QED"; "TAKE"; "DEF"; "HIDE"; "RECURSIVE"; "USE"; "DEFINE"; "PROOF";
      "WITNESS"; "PICK"; "DEFS"; "SUFFICES"; "NEW"; "LAMBDA"; "STATE"; "ACTION";
      "TEMPORAL"; "ONLY"; "OMITTED"; "ONLY"; "LEMMA"; "PROPOSITION"; "COROLLARY";
      "WF"; "SF"; "CHOOSE"; "ENABLED"; "UNCHANGED"; "SUBSET"; "UNION"; "DOMAIN";
      "ELSE"; "THEN"; "LET"; "IN"; "ASSUME"; "PROVE";
      "Int"; "Nat"; "Real"; "Infinity";
      "_Spec"; "_Init"; "_Next"; "_Fairness" ]
  in List.iter (fun n -> if List.mem n reservedwords then raise (NameClashWithTLA n) else ()) symbols

let sanitize_modulename s =
  Str.global_replace (Str.regexp "[^a-zA-Z0-9_]") "_" s

let view_header =
  sprintf "-------- MODULE %s --------\n" (Options.file |> Filename.remove_extension |> Filename.basename |> sanitize_modulename)
  ^ "EXTENDS Reals, Integers\n"

(* the names of all declared symbols: const, types, variables, transitions *)
let allsymbols s =
  (List.map (fun (_, c, _) -> Hstring.view c) s.consts)
  @ get_variables_names s.globals s.arrays
  @ List.map (fun (_, (name, _)) -> Hstring.view name) s.type_defs
  @ List.concat (List.map (fun (_, (_, cons)) -> List.map Hstring.view cons) s.type_defs)
  @ List.map (fun tr -> Hstring.view tr.tr_name) s.trans

let print fmt s =
  let s = { s with trans = make_unique_tr_names s.trans } in
  allsymbols s |> check_clash;
  let varnames = get_variables_names s.globals s.arrays in
  let hasinvariants = (s.invs <> []) in
  (* call all the generators before printing anything, in case of failure. *)
  let s = ""
    ^ (view_header)
    ^ "\n"
    ^ (view_consts s.consts)
    ^ "\n"
    ^ (view_type_defs s.type_defs)
    ^ "\n"
    ^ (view_variables varnames)
    ^ "\n"
    ^ (view_typeinvariant s.globals s.arrays)
    ^ "\n"
    ^ (view_invs s.invs)
    ^ "\n"
    ^ (view_unsafe s.unsafe)
    ^ "\n"
    ^ (view_init s.globals s.arrays s.init hasinvariants)
    ^ "\n"
    ^ (view_trans s.trans varnames)
    ^ "\n"
    ^ (view_next s.trans hasinvariants)
    ^ "\n"
    ^ (view_spec)
    ^ "\n"
    ^ "======================\n"
  in output_string fmt s;
