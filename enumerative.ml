(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                  Universite Paris-Sud 11                               *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

open Options
open Format
open Ast
open Cube

module MapT = Map.Make (struct type t = term let compare = compare_term end)


module HT = Hashtbl.Make (struct
  type t = term
  let equal x y = compare_term x y = 0
  let hash = hash_term
end)

module HI = Hashtbl.Make 
  (struct 
  type t = int 
  let equal = (=) 
  let hash x = x end)


type state = int array


type state_info = int HT.t

let equal_state a1 a2 =
  let n = Array.length a1 in
  let n2 = Array.length a2 in
  if n <> n2 then false
  else
    let res = ref true in
    let i = ref 0 in 
    while !res && !i < n  do
      res := a1.(!i) = a2.(!i);
      incr i
    done;
    !res

let hash_state st =
  let h = ref 1 in
  let n = ref 2 in
  for i = 0 to Array.length st - 1 do
    h := !h * st.(i) + !n;
    n := 13 * !n + 7;      
  done;
  !h

module HST = Hashtbl.Make (struct 
  type t = state
  let equal = equal_state
  let hash = hash_state
end)



type env = {
  var_terms : STerm.t;
  nb_vars : int;
  perm_procs : (int * int) list list;
  first_proc : int;
  extra_proc : int;
  all_procs : Hstring.t list;
  id_terms : int HT.t;
}



exception Found of term

let id_to_term env id =
  try
    HT.iter (fun t i -> if id = i then raise (Found t)) env.id_terms;
    raise Not_found
  with Found t -> t
      

let state_to_cube env st =
  let i = ref 0 in
  Array.fold_left (fun sa sti ->
    let sa = 
      if sti <> -1 then
	let t1 = id_to_term env !i in
	let t2 = id_to_term env sti in
	SAtom.add (Atom.Comp (t1, Eq, t2)) sa
      else sa
    in
    incr i; sa)
    SAtom.empty st

    

let all_constr_terms () =
  List.rev_map (fun x -> Elem (x, Constr)) (Smt.Type.all_constructors ())

let proc_terms =
  List.map (fun x -> Elem (x, Var))

let init_tables procs s =
  let var_terms = all_var_terms procs s in
  let proc_terms = proc_terms procs in
  let constr_terms = all_constr_terms () in
  let nb_vars = STerm.cardinal var_terms in
  let nb_consts = List.length proc_terms + List.length constr_terms in
  let ht = HT.create (nb_vars + nb_consts) in
  let i = ref 0 in
  let proc_ids = ref [] in
  STerm.iter (fun t -> HT.add ht t !i; incr i) var_terms;
  let first_proc = !i in
  List.iter (fun t -> HT.add ht t !i; proc_ids := !i :: !proc_ids; incr i)
    proc_terms;
  (* add an extra process in case we need it : change this to statically compute
     how many extra processes are needed *)
  let ep = List.nth Ast.proc_vars (List.length proc_terms) in
  let all_procs = procs @ [ep] in
  HT.add ht (Elem (ep, Var)) !i;
  let extra_proc = !i in
  incr i;

  List.iter (fun t -> HT.add ht t !i; incr i) constr_terms;
  let proc_ids = List.rev !proc_ids in
  let prem_procs = 
    List.filter (fun sigma ->
      List.exists (fun (x,y) -> x <> y) sigma
    ) (Cube.all_permutations proc_ids proc_ids) in
  if debug then
    HT.iter (fun t i -> eprintf "%a -> %d@." Pretty.print_term t i ) ht;
  { var_terms = var_terms;
    nb_vars = nb_vars;
    perm_procs = prem_procs;
    first_proc = first_proc;
    extra_proc = extra_proc;
    all_procs = all_procs;
    id_terms = ht }


let apply_subst env st sigma =
  let st' = Array.copy st in
  for i = 0 to env.nb_vars - 1 do
    try let v = List.assoc st'.(i) sigma in st'.(i) <- v
    with Not_found -> ()
  done;
  st'


let mkinit arg init args =
  match arg with
    | None -> init
    | Some z ->
        let abs_init = SAtom.filter (function
	  | Atom.Comp ((Elem (x, _) | Access (x,_,_)), _, _) ->
	      not (Smt.Symbol.has_infinite_type x)
	  | _ -> true) init in
	let abs_init = simplification_atoms SAtom.empty abs_init in
	let sa, cst = SAtom.partition (has_var z) abs_init in
	List.fold_left (fun acc h ->
	  SAtom.union (subst_atoms [z, h] sa) acc) cst args

let mkinit_s procs ({t_init = ia, init}) =
  let sa, (nargs, _) = proper_cube (mkinit ia init procs) in
  sa, nargs



let write_atom_to_state env st = function
  | Atom.Comp (t1, Eq, t2) ->
      st.(HT.find env.id_terms t1) <- HT.find env.id_terms t2
  | Atom.Comp (t1, Neq, Elem(_, Var)) ->
      (* Assume an extra process if a disequality is mentioned on
         type proc in init formula : change this to something more robust *)
      st.(HT.find env.id_terms t1) <- env.extra_proc
  | _ -> assert false
  
let write_cube_to_state env st =
  SAtom.iter (write_atom_to_state env st)


let init_to_states env procs s =
  let nb = env.nb_vars in
  let st_init = Array.make nb (-1) in
  let init, _ = mkinit_s procs s in
  write_cube_to_state env st_init init;
  [st_init]

type st_req = int * op_comp * int

type st_action = 
  | St_ignore
  | St_assign of int * int 
  | St_ite of st_req list * st_action * st_action

let atom_to_st_req env = function 
  | Atom.Comp (t1, op, t2) -> 
      HT.find env.id_terms t1, op, HT.find env.id_terms t2
  | _ -> assert false

let satom_to_st_req env sa =
  SAtom.fold (fun a acc -> 
    try (atom_to_st_req env a) :: acc
    with Not_found -> acc) sa []

let rec atom_to_st_action env = function 
  | Atom.Comp (t1, Eq, t2) -> 
    eprintf "%a <- %a@." Pretty.print_term t1 Pretty.print_term t2;
      St_assign (HT.find env.id_terms t1, HT.find env.id_terms t2)
  | Atom.Ite (sa, a1, a2) ->
      St_ite (satom_to_st_req env sa, atom_to_st_action env a1, 
	      atom_to_st_action env a2)
  | _ -> assert false

let satom_to_st_action env sa =
  SAtom.fold (fun a acc -> (atom_to_st_action env a) :: acc) sa []


type trivial_cond = Trivial of bool | Not_trivial

let trivial_cond env (i, op, v) =
  if env.first_proc <= i && i <= env.extra_proc && 
     env.first_proc <= v && v <= env.extra_proc then 
    match op with
      | Eq -> Trivial (i = v)
      | Neq -> Trivial (i <> v)
      | Le -> Trivial (i <= v)
      | Lt -> Trivial (i <> v)
  else Not_trivial

let trivial_conds env l =
  if l = [] then Trivial false
  else
    try
      List.iter (fun c -> match trivial_cond env c with
	| Trivial true -> ()
	| Trivial false -> raise Exit
	| Not_trivial -> raise Not_found
      ) l;
      Trivial true
    with 
      | Exit -> Trivial false
      | Not_found -> Not_trivial


let assigns_to_actions env sigma acc =
  List.fold_left 
    (fun acc (h, t) ->
      let nt = Elem (h, Glob) in
      let t = subst_term sigma t in
      try (St_assign (HT.find env.id_terms nt, HT.find env.id_terms t)) :: acc
      with Not_found -> acc
    ) acc

let nondets_to_actions env sigma acc =
  List.fold_left 
    (fun acc (h) ->
      let nt = Elem (h, Glob) in
      try (St_assign (HT.find env.id_terms nt, -1)) :: acc
      with Not_found -> acc
    ) acc

let update_to_actions procs sigma env acc {up_arr=a; up_arg=j; up_swts=swts} =
  let rec sd acc = function
    | [] -> assert false
    | [d] -> acc, d
    | s::r -> sd (s::acc) r in
  let swts, (d, t) = sd [] swts in
  (* assert (d = SAtom.singleton True); *)
  List.fold_left (fun acc i ->
    let sigma = (j,i)::sigma in
    let at = Access (a, i, Var) in
    let t = subst_term sigma t in
    let default = St_assign (HT.find env.id_terms at, HT.find env.id_terms t) in
    let ites = 
      List.fold_left (fun ites (sa, t) ->
	let sa = subst_atoms sigma sa in
	let t = subst_term sigma t in
	let sta = 
	  try St_assign (HT.find env.id_terms at, HT.find env.id_terms t)
	  with Not_found -> St_ignore
	in
	let conds = satom_to_st_req env sa in
	match trivial_conds env conds with
	  | Trivial true -> sta
	  | Trivial false -> ites
	  | Not_trivial -> St_ite (satom_to_st_req env sa, sta, ites)
      ) default swts
    in ites :: acc
  ) acc procs

let missing_reqs_to_actions acct =
  List.fold_left (fun acc -> function
    | (a, Eq, b) ->
        if List.exists (function St_assign (a', _) -> a = a' | _ -> false) acct
        then acc
        else (St_assign (a,b)) :: acc
    | _ -> acc) acct

exception Not_applicable

let value_in_state env st i = if i <> -1 && i < env.nb_vars then st.(i) else i

let check_req env st (i1, op, i2) =
  try
    let v1 = value_in_state env st i1 in
    let v2 = value_in_state env st i2 in
    v1 = -1 || v2 = -1 ||
	match op with
	  | Eq -> v1 = v2
	  | Neq -> v1 <> v2
	  | Le -> v1 <= v2
	  | Lt -> v1 < v2
  with Not_found -> true

let check_reqs env st = List.for_all (check_req env st)


let rec apply_action env st st' = function
  | St_ignore -> ()
  | St_assign (i1, i2) ->
    begin
      try
	let v2 = value_in_state env st i2 in
	st'.(i1) <- v2
      with Not_found -> ()
    end 
  | St_ite (reqs, a1, a2) ->
      if check_reqs env st reqs then apply_action env st st' a1
      else apply_action env st st' a2

let apply_actions env st acts =
  let st' = Array.copy st in
  List.iter (apply_action env st st') acts;
  st'


(* factorize this *)
let uguard_dnf sigma args tr_args = function
  | [] -> []
  | [j, dnf] ->
      let uargs = List.filter (fun a -> not (H.list_mem a tr_args)) args in
      List.map (fun i ->
	List.map (fun sa -> subst_atoms ((j, i)::sigma) sa) dnf) uargs
  | _ -> assert false


let rec extra_args procs tr_args =
  let proc_vars =
    List.fold_left (fun pr _ -> match pr with _::r -> r | [] -> assert false)
      Ast.proc_vars procs in
  let acc, _ =
    List.fold_left 
      (fun (acc, pr) _ -> match pr with x::r -> x::acc, r | [] -> assert false)
      ([], proc_vars) tr_args in
  List.rev acc 


let rec print_action env fmt = function
  | St_ignore -> ()
  | St_assign (i, -1) -> 
      fprintf fmt "%a = ." Pretty.print_term (id_to_term env i)
  | St_assign (i, v) -> 
      fprintf fmt "%a" Pretty.print_atom 
	(Atom.Comp (id_to_term env i, Eq, id_to_term env v))
  | St_ite (l, a1, a2) ->
      fprintf fmt "ITE (";
      List.iter (fun (i, op, v) -> 
	eprintf "%a && " Pretty.print_atom 
	  (Atom.Comp (id_to_term env i, op, id_to_term env v))
      ) l;
      fprintf fmt ", %a , %a )" (print_action env) a1 (print_action env) a2


let print_transition_fun env name sigma st_reqs st_udnfs st_actions fmt =
  fprintf fmt "%a (%a)\n" Hstring.print name Pretty.print_subst sigma;
  fprintf fmt "requires { \n";
      List.iter (fun (i, op, v) -> 
	fprintf fmt "          %a\n" Pretty.print_atom 
	  (Atom.Comp (id_to_term env i, op, id_to_term env v))
      ) st_reqs;
      List.iter (fun dnf ->
	fprintf fmt "          ";
	List.iter (fun r ->
	  List.iter (fun (i, op, v) -> 
	    fprintf fmt "%a &&" Pretty.print_atom 
	      (Atom.Comp (id_to_term env i, op, id_to_term env v))
	  ) r;
	  fprintf fmt " || ";
	) dnf;
	fprintf fmt "\n";
      ) st_udnfs;
      fprintf fmt "}\n";
      fprintf fmt "actions { \n";
      List.iter (fun a -> 
	fprintf fmt "         %a\n" (print_action env) a;
      ) st_actions;
      fprintf fmt "}\n@."
  

let rec action_to_lits = function
  | St_ignore -> []
  | St_assign (a, b) -> [a, Eq, b]
  | St_ite (reqs, a1, a2) -> reqs @ (action_to_lits a1) @ (action_to_lits a2)

let transitions_to_func procs trans env =
  let aux (acc, loc_cands) { tr_args = tr_args; 
		             tr_reqs = reqs; 
		             tr_name = name;
		             tr_ureq = ureqs;
		             tr_assigns = assigns; 
		             tr_upds = upds; 
		             tr_nondets = nondets } =
    (* let _, others = Forward.missing_args procs tr_args in *)
    let d = all_permutations tr_args procs in
    (* do it even if no arguments *)
    let d = if d = [] then [[]] else d in
    List.fold_left (fun (acc, loc_cands) sigma ->
      let reqs = subst_atoms sigma reqs in
      let t_args_ef = 
	List.fold_left (fun acc p -> 
	  try (svar sigma p) :: acc
	  with Not_found -> p :: acc) [] tr_args in
      let udnfs = uguard_dnf sigma procs t_args_ef ureqs in
      let st_reqs = satom_to_st_req env reqs in
      let st_udnfs = List.map (List.map (satom_to_st_req env)) udnfs in
      let st_actions = assigns_to_actions env sigma [] assigns in
      let st_actions = nondets_to_actions env sigma st_actions nondets in
      let st_actions = List.fold_left 
	(update_to_actions procs sigma env)
	st_actions upds in
      let st_actions = missing_reqs_to_actions st_actions st_reqs in
      if debug then
        print_transition_fun env name sigma st_reqs st_udnfs st_actions 
	  err_formatter;
      let f = fun st ->
	if not (check_reqs env st st_reqs) then raise Not_applicable;
	if not (List.for_all (List.exists (check_reqs env st)) st_udnfs)
	then raise Not_applicable;
	apply_actions env st st_actions
      in
      let lits =
        (List.fold_left (fun acc act -> action_to_lits act @ acc) [] st_actions) @
        (List.flatten (List.flatten st_udnfs)) @ st_reqs in
      let loc_cands =
        List.fold_left (fun acc ((a1, _, b1) as l1) ->
          if a1 = b1 then acc
          else
            List.fold_left (fun acc ((a2, _, b2) as l2) ->
              if a2 <> b2 && l1 <> l2 then (l1, l2) :: acc else acc
            ) acc lits
        ) loc_cands lits in
      f :: acc, loc_cands
    ) (acc, loc_cands) d
  in
  List.fold_left aux ([], []) trans



let post st trs acc =
  List.fold_left (fun acc f_tr ->
    try (f_tr st) :: acc
    with Not_applicable -> acc) acc trs



module MC = Map.Make 
  (struct type t = int * int let compare = Pervasives.compare end)

module SC = Set.Make 
  (struct type t = int * int let compare = Pervasives.compare end)


let localized_candidates_init init_state =
  let a = ref (-1) in
  Array.fold_left (fun acc va ->
    incr a;
    if va <> -1 then
      let lita = (!a, Eq, va) in
      let b = ref (-1) in
      Array.fold_left (fun acc vb ->
        incr b;    
        let litb = (!b, Eq, vb) in
        if vb <> -1 && lita <> litb then    
          (lita, litb) :: acc
        else acc) acc init_state
    else acc) [] init_state
  


let pair_to_atom env (x,y) =
  Atom.Comp (id_to_term env x, Eq, id_to_term env y)
  

let add_companions st mc =
  let a = ref (-1) in
  Array.fold_left (fun mc va ->
    incr a;
    let lit = (!a, va) in
    let comps = try MC.find lit mc with Not_found -> SC.empty in
    let i = ref (-1) in
    let comps =
      Array.fold_left (fun sc v -> 
	incr i;
	let iv = !i, v in
	if iv <> lit then SC.add iv sc else sc
      ) comps st in
    MC.add lit comps mc) mc st


let ids_to_companions env mc =
  MC.fold (fun ((_,va) as lit) comps fmc ->
    if va = -1 then fmc
    else
      let a = pair_to_atom env lit in
      let sa_comps_unc = 
	SC.fold (fun ((i,v) as l) (sa, unc) ->
	  if v = -1 then sa, STerm.add (id_to_term env i) unc
	  else SAtom.add (pair_to_atom env l) sa, unc
	) comps (SAtom.empty, STerm.empty)
      in
      Forward.MA.add a sa_comps_unc fmc)
    mc Forward.MA.empty


let check_cand env state (l1, l2) =
  not (check_req env state l1) || check_req env state l2


let ids_to_candidates s env =
  let cpt = ref (-1) in
  List.fold_left (fun acc ((a1, op1, b1), (a2, op2, b2)) ->
    try
      let l1 = Atom.Comp (id_to_term env a1, op1, id_to_term env b1) in
      let l2 = Atom.Comp (id_to_term env a2, op2, id_to_term env b2) in
      let sa = SAtom.add (Atom.neg l2) (SAtom.singleton l1) in    
      let sa', (args, _) = proper_cube sa in
      let ar' = ArrayAtom.of_satom sa' in
      let s' = 
        { s with
	  t_from = [];
	  t_unsafe = args, sa';
	  t_arru = ar';
	  t_alpha = ArrayAtom.alpha ar' args;
	  t_deleted = false;
	  t_nb = !cpt;
	  t_nb_father = -1 } in
      if List.exists (fun s -> ArrayAtom.equal s.t_arru s'.t_arru) acc then acc
      else (decr cpt; s' :: acc)
    with Not_found -> acc
  ) []


let stateless_forward s procs trs loc_cands env l =
  let h_visited = HI.create 2_000_029 in
  let cpt_f = ref 0 in
  let rec forward_rec s procs trs loc_cands mc = function
    | [] ->
        eprintf "Total forward nodes : %d@." !cpt_f;
        if localized then ids_to_candidates s env loc_cands
        else Forward.extract_candidates_from_compagnons (ids_to_companions env mc) s
    | st :: to_do ->
        let hst = hash_state st in
        if HI.mem h_visited hst then
	  forward_rec s procs trs loc_cands mc to_do
        else
          let loc_cands =
            if localized then List.filter (check_cand env st) loc_cands
            else loc_cands in
	  let to_do = post st trs to_do in
	  incr cpt_f;
	  if debug && verbose > 1 then 
            eprintf "%d : %a\n@." !cpt_f Pretty.print_cube (state_to_cube env st);
	  if !cpt_f mod 1000 = 0 then eprintf "%d (%d)@."
	    !cpt_f (List.length to_do);
	  HI.add h_visited hst ();
	  let mc = if localized then mc else add_companions st mc in
	  forward_rec s procs trs loc_cands mc to_do
  in
  forward_rec s procs trs loc_cands MC.empty l



let stateless_search procs init =
  let env = init_tables procs init in
  let st_inits = init_to_states env procs init in
  if debug then 
    List.iter (fun st ->
      eprintf "init : %a\n@." Pretty.print_cube (state_to_cube env st))
      st_inits;
  let trs, loc_cands = transitions_to_func procs init.t_trans env in
  let loc_cands = 
    List.fold_left (fun acc i ->
      localized_candidates_init i @ acc) loc_cands st_inits in
  stateless_forward init procs trs loc_cands env st_inits










