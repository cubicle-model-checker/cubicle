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

open Options
open Format
open Ast
open Types
open Util

module H = Hstring

module HT = Hashtbl.Make (Term)

module HI = Hashtbl.Make (struct 
  type t = int 
  let equal = (=) 
  let hash x = x
end)


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


let hash_state st = Hashtbl.hash_param 100 500 st


module HST = Hashtbl.Make 
  (struct 
    type t = state
    let equal = (=)
    let hash = hash_state
   end)

  
type st_req = int * op_comp * int

type st_action = 
  | St_ignore
  | St_assign of int * int 
  | St_arith of int * int * int
  | St_ite of st_req list * st_action * st_action


exception Not_applicable

type state_transistion = {
  st_name : Hstring.t;
  st_reqs : st_req list;
  st_udnfs : st_req list list list;
  st_actions : st_action list;
  st_f : state -> state list;
  st_vars : Hstring.HSet.t;
  st_args : Hstring.t list;
}


type env = {
  model_cardinal : int;
  var_terms : Term.Set.t;
  nb_vars : int;
  perm_procs : (int * int) list list;
  perm_states : ((Hstring.t * Hstring.t) list *
                    (int * int) list * (int * int) list) list;
  first_proc : int;
  extra_proc : int;
  all_procs : Hstring.t list;
  proc_ids : int list;
  id_terms : int HT.t;
  id_true : int;
  id_false : int;
  st_trs : state_transistion list;
  low_int_abstr : int;
  up_int_abstr : int;
  pinf_int_abstr : int;
  minf_int_abstr : int;

  mutable explicit_states : unit HST.t;
  mutable states : state list;
}

let empty_env = {
  model_cardinal = 0;
  var_terms = Term.Set.empty;
  nb_vars = 0;
  perm_procs = [];
  perm_states = [];
  first_proc = 0;
  extra_proc = 0;
  all_procs = [];
  proc_ids = [];
  id_terms = HT.create 0;
  id_true = 0;
  id_false = 0;
  st_trs = [];
  low_int_abstr = 0;
  up_int_abstr = 0;
  pinf_int_abstr = 0;
  minf_int_abstr = 0;

  explicit_states = HST.create 0;
  states = [];
}


let build_state_procs_map id_terms procs var_terms proc_terms =
  let build_int_perms sigma lt =
    List.fold_left (fun acc_s t ->
      let t_s = Term.subst sigma t in
      if not (Term.equal t_s t) then
        (HT.find id_terms t, HT.find id_terms t_s) :: acc_s
      else acc_s
    ) [] lt
  in
  let d = Variable.all_permutations procs procs in
  List.rev_map (fun sigma ->
    let p_vars = build_int_perms sigma (Term.Set.elements var_terms) in
    let p_procs = build_int_perms sigma proc_terms in
    sigma, p_vars, p_procs
  ) d


let swap a (i,j) =
  if i <> j then
    let tmp = a.(i) in
    a.(i) <- a.(j);
    a.(j) <- tmp
    
let apply_perm_state env st (_, p_vars, p_procs) =
  let st' = Array.copy st in
  List.iter (swap st') p_vars;
  for i = 0 to env.nb_vars - 1 do
    try let v = List.assoc st'.(i) p_procs in st'.(i) <- v
    with Not_found -> ()
  done;
  st'
  
let apply_subst env st sigma =
  let st' = Array.copy st in
  for i = 0 to env.nb_vars - 1 do
    try let v = List.assoc st'.(i) sigma in st'.(i) <- v
    with Not_found -> ()
  done;
  st'

let normalize_state env st =
  let met = ref [] in
  let remaining = ref env.proc_ids in
  let sigma = ref [] in
  for i = 0 to Array.length st - 1 do
    let v = st.(i) in
    if !remaining <> [] then
      let r = List.hd !remaining in
      if env.first_proc <= v && v < env.extra_proc && 
        not (List.mem v !met) && v <> r then begin
          met := v :: !met;
          remaining := List.tl !remaining;
          sigma := (v,r) :: (r,v) :: !sigma
        end;
  done;
  apply_subst env st !sigma


let global_envs = ref []


exception Found of term


let make_range (low, up) =
  let l = ref [] in
  for i = up downto low do
    l := i :: !l
  done;
  !l

let abstr_range = make_range num_range

let abstr_add env x y =
  let r =
    if x = env.minf_int_abstr then
      if y <> env.pinf_int_abstr then x
      else -1 (* raise Not_found *)
    else if x = env.pinf_int_abstr then
      if y <> env.minf_int_abstr then x
      else -1 (* raise Not_found *)
    else
      if y = env.pinf_int_abstr || y = env.minf_int_abstr then y
      else x + y in
  if r < env.low_int_abstr then env.minf_int_abstr
  else if r > env.up_int_abstr then env.pinf_int_abstr
  else r

let abstr_add env x y =
  let r = abstr_add env x y in
  if r = env.minf_int_abstr || r = env.pinf_int_abstr then raise Not_applicable;
  r

(* inefficient but only used for debug *)
let id_to_term env id =
  try
    HT.iter (fun t i -> if id = i then raise (Found t)) env.id_terms;
    raise Not_found
  with Found t -> t
      

let is_int_real = function
  | Elem (x,Glob) | Access (x, _) -> 
      snd (Smt.Symbol.type_of x) = Smt.Type.type_int ||
      snd (Smt.Symbol.type_of x) = Smt.Type.type_real
  | _ -> false

(* inefficient but only used for debug *)
let state_to_cube env st =
  let i = ref 0 in
  Array.fold_left (fun sa sti ->
    let sa = 
      if sti <> -1 then
	let t1 = id_to_term env !i in
	let t2 =
          if sti = env.minf_int_abstr then Elem (Hstring.make "-oo", Constr)
          else if  sti = env.pinf_int_abstr then Elem (Hstring.make "+oo", Constr) 
          else id_to_term env sti in
	SAtom.add (Atom.Comp (t1, Eq, t2)) sa
      else sa
    in
    incr i; sa)
    SAtom.empty st

    

let all_constr_terms () =
  List.rev_map (fun x -> Elem (x, Constr)) (Smt.Type.all_constructors ())

let terms_of_procs = List.map (fun x -> Elem (x, Var))


let rec power_p i p = if p <= 0 then 1 else i * power_p i (p-1)

let table_size nb_procs nb_vars =
  let r = min 2_000_009
  (max 100 ((power_p (nb_procs * nb_vars) nb_procs) * (nb_procs ))) in
  if not quiet then eprintf "table size : %d@." r;
  r


let init_tables procs s =
  let var_terms = Forward.all_var_terms procs s in
  let proc_terms = terms_of_procs procs in (* constantes *)
  let constr_terms = all_constr_terms () in (* constantes *)
  let nb_vars = Term.Set.cardinal var_terms in
  let nb_procs = List.length proc_terms in
  let nb_consts = nb_procs + List.length constr_terms in
  let ht = HT.create (nb_vars + nb_consts) in
  let i = ref 0 in
  Term.Set.iter (fun t -> HT.add ht t !i; incr i) var_terms;
  let proc_ids = ref [] in
  let first_proc = !i in
  List.iter (fun t -> HT.add ht t !i; proc_ids := !i :: !proc_ids; incr i)
    proc_terms;
  (* add an extra process in case we need it : change this to statically compute
     how many extra processes are needed *)
  let ep = List.nth Variable.procs nb_procs in
  let all_procs = procs @ [ep] in
  HT.add ht (Elem (ep, Var)) !i;
  let extra_proc = !i in
  incr i;

  List.iter (fun t -> HT.add ht t !i; incr i) constr_terms;
  let proc_ids = List.rev !proc_ids in
  let perm_procs = 
    List.filter (fun sigma ->
      List.exists (fun (x,y) -> x <> y) sigma
    ) (Variable.all_permutations proc_ids proc_ids) in
  let perm_states = build_state_procs_map ht procs var_terms proc_terms in
  if debug then
    HT.iter (fun t i -> eprintf "%a -> %d@." Term.print t i ) ht;
  let id_true =
    try HT.find ht (Elem (Term.htrue, Constr)) with Not_found -> -2 in
  let id_false =
    try HT.find ht (Elem (Term.hfalse, Constr)) with Not_found -> -2 in
   
  let a_low = !i in
  List.iter (fun c ->
    HT.add ht (Const (MConst.add (ConstInt (Num.Int c)) 1 MConst.empty)) !i;
    HT.add ht (Const (MConst.add (ConstReal (Num.Int c)) 1 MConst.empty)) !i;
    incr i) abstr_range;
  let a_up = !i - 1 in

  { model_cardinal = nb_procs;
    var_terms = var_terms;
    nb_vars = nb_vars;
    perm_procs = perm_procs;
    perm_states = perm_states;
    first_proc = first_proc;
    extra_proc = extra_proc;
    all_procs = all_procs;
    proc_ids = proc_ids;
    id_terms = ht;
    id_true = id_true;
    id_false = id_false;
    st_trs = [];

    low_int_abstr = a_low;
    up_int_abstr = a_up;
    pinf_int_abstr = a_up + 1;
    minf_int_abstr = -3;

    explicit_states = HST.create (table_size nb_procs nb_vars);
    states = [];
  }



let abs_inf = 
  SAtom.filter (function
    | Atom.Comp ((Elem (x, Glob) | Access (x,_)), _, _) ->
	if abstr_num then not (Smt.Symbol.has_abstract_type x)
        else not (Smt.Symbol.has_infinite_type x)
    | _ -> true)


let make_init_cdnf args lsa lvars =
  match args, lvars with
    | [], _ ->   
	[lsa]
    | _, [] ->
        [List.map 
            (SAtom.filter (fun a -> 
              not (List.exists (fun z -> Atom.has_var z a) args)))
            lsa]
    | _ ->
        let lsigs = Variable.all_instantiations args lvars in
        List.fold_left (fun conj sigma ->
          let dnf = List.fold_left (fun dnf sa ->
            let sa = abs_inf sa in
            let sa = SAtom.subst sigma sa in
            try (Cube.simplify_atoms sa) :: dnf
            with Exit -> dnf
          ) [] lsa in
          dnf :: conj
        ) [] lsigs

let rec cdnf_to_dnf_rec acc = function
  | [] -> acc
  | [] :: r ->
      cdnf_to_dnf_rec acc r
  | dnf :: r ->
      let acc = 
        List.flatten (List.rev_map (fun sac -> 
          List.rev_map (SAtom.union sac) dnf) acc) in
      cdnf_to_dnf_rec acc r

let cdnf_to_dnf = function
  | [] -> [SAtom.singleton Atom.False]
  | l -> cdnf_to_dnf_rec [SAtom.singleton Atom.True] l

(* let make_sorts = *)
(*   let cpt = ref 0 in *)
(*   List.fold_left (fun sa p -> *)
(*     incr cpt; *)
(*     let s = if !cpt <= 2 then "CId" else "L1Id" in *)
(*     let a = Atom.Comp (Access (Hstring.make "Sort", [p]), Eq, *)
(*                   Elem (Hstring.make s, Constr)) in *)
(*     SAtom.add a sa) SAtom.empty *)

(* let add_sorts procs = *)
(*   let sorts = make_sorts procs in *)
(*   List.map (SAtom.union sorts) *)

let mkinits procs ({t_init = ia, l_init}) =
  let lsa = cdnf_to_dnf (make_init_cdnf ia l_init procs) in
  (* add_sorts procs *) lsa


let int_of_const = function
  | ConstInt n -> Num.int_of_num n
  | ConstReal n -> Num.int_of_num (Num.integer_num n)
  | ConstName _ -> 1

let int_of_consts cs =
  MConst.fold (fun c i acc -> i * (int_of_const c) + acc) cs 0

let write_atom_to_states env sts = function
  | Atom.Comp (t1, (Le | Lt as op), (Const _ as t2)) when abstr_num ->
      let v2 = HT.find env.id_terms t2 in
      let i1 = HT.find env.id_terms t1 in
      let l = ref [] in
      for i2 = env.low_int_abstr to (if op = Lt then v2 - 1 else v2) do
        List.iter (fun st ->
          let st = Array.copy st in
          st.(i1) <- i2;
          l := st :: !l
        ) sts
      done;
      !l
  | Atom.Comp ((Const _ as t1), (Le | Lt as op), t2) when abstr_num  ->
      let v1 = HT.find env.id_terms t1 in
      let i2 = HT.find env.id_terms t2 in
      let l = ref [] in
      for i1 = (if op = Lt then v1 + 1 else v1) to env.up_int_abstr do
        List.iter (fun st ->
          let st = Array.copy st in
          st.(i2) <- i1;
          l := st :: !l
        ) sts
      done;
      !l
  | Atom.Comp (t1, Eq, t2) ->
      List.iter (fun st -> 
        st.(HT.find env.id_terms t1) <- HT.find env.id_terms t2) sts;
      sts
  | Atom.Comp (t1, Neq, Elem(_, Var)) ->
      (* Assume an extra process if a disequality is mentioned on
         type proc in init formula : change this to something more robust *)
      List.iter (fun st -> st.(HT.find env.id_terms t1) <- env.extra_proc) sts;
      sts
  | _ -> sts
  
let write_cube_to_states env st sa =
  SAtom.fold (fun a sts -> write_atom_to_states env sts a) sa [st]

let init_to_states env procs s =
  let nb = env.nb_vars in
  let l_inits = mkinits procs s in
  let sts =
    List.fold_left (fun acc init -> 
      let st_init = Array.make nb (-1) in
      let sts = write_cube_to_states env st_init init in
      List.rev_append sts acc
    ) [] l_inits in
  List.map (fun st -> 0, st) sts
  

let atom_to_st_req env = function
  | Atom.Comp (t1, op, t2) -> 
      HT.find env.id_terms t1, op, HT.find env.id_terms t2
  | _ -> assert false

let satom_to_st_req env sa =
  SAtom.fold (fun a acc -> 
    try (atom_to_st_req env a) :: acc
    with Not_found -> acc) sa []

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
  let some_non_trivial = ref false in
  if l = [] then Trivial false
  else
    try
      List.iter (fun c -> match trivial_cond env c with
	| Trivial true -> ()
	| Trivial false -> raise Exit
	| Not_trivial -> some_non_trivial := true
      ) l;
      if !some_non_trivial then Not_trivial else Trivial true
    with 
      | Exit -> Trivial false

let assigns_to_actions env sigma acc =
  List.fold_left 
    (fun acc (h, t) ->
      let nt = Elem (h, Glob) in
      let t = Term.subst sigma t in
      try 
        let a = match t with
          | Arith (t', cs) ->
              St_arith (HT.find env.id_terms nt, HT.find env.id_terms t', int_of_consts cs)
          | _ ->
              St_assign (HT.find env.id_terms nt, HT.find env.id_terms t)
        in a :: acc
      with Not_found -> acc
    ) acc

let nondets_to_actions env sigma acc =
  List.fold_left 
    (fun acc (h) ->
      let nt = Elem (h, Glob) in
      try (St_assign (HT.find env.id_terms nt, -1)) :: acc
      with Not_found -> acc
    ) acc

let update_to_actions procs sigma env acc
    {up_arr=a; up_arg=lj; up_swts=swts} =
  let rec sd acc = function
    | [] -> assert false
    | [d] -> acc, d
    | s::r -> sd (s::acc) r in
  let swts, (d, t) = sd [] swts in
  (* assert (d = SAtom.singleton True); *)
  let indexes = Variable.all_arrangements_arity a procs in
  List.fold_left (fun acc li ->
    let sigma = (List.combine lj li) @ sigma in
    let at = Access (a, li) in
    let t = Term.subst sigma t in
    let default =
      try match t with
        | Arith (t', cs) ->
            St_arith (HT.find env.id_terms at,
                      HT.find env.id_terms t', int_of_consts cs)            
        | _ ->
            St_assign (HT.find env.id_terms at, HT.find env.id_terms t)
      with Not_found -> St_ignore
    in
    let ites = 
      List.fold_left (fun ites (sa, t) ->
	let sa = SAtom.subst sigma sa in
	let t = Term.subst sigma t in
	let sta = 
          try match t with
            | Arith (t', cs) ->
                St_arith (HT.find env.id_terms at, 
                          HT.find env.id_terms t', int_of_consts cs)
            | _ ->
                St_assign (HT.find env.id_terms at, HT.find env.id_terms t)
	  with Not_found -> St_ignore
	in
	let conds = satom_to_st_req env sa in
	match trivial_conds env conds with
	  | Trivial true -> sta
	  | Trivial false -> ites
	  | Not_trivial -> St_ite (satom_to_st_req env sa, sta, ites)
      ) default swts
    in ites :: acc
  ) acc indexes

let missing_reqs_to_actions acct =
  List.fold_left (fun acc -> function
    | (a, Eq, b) ->
        if List.exists
          (function St_assign (a', _) -> a = a' | _ -> false) acct
        then acc
        else (St_assign (a,b)) :: acc
    | _ -> acc) acct

let value_in_state env st i =
  if i <> -1 && i < env.nb_vars then st.(i) else i

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


let neg_req env = function
  | a, Eq, b ->
      if b = env.id_true then a, Eq, env.id_false
      else if b = env.id_false then a, Eq, env.id_true
      else a, Neq, b
  | a, Neq, b -> a, Eq, b
  | a, Le, b -> b, Lt, a
  | a, Lt, b -> b, Le, a


let rec apply_action env st sts' = function
  | St_assign (i1, i2) ->
    begin
      try
	let v2 = value_in_state env st i2 in
	List.iter (fun st' -> st'.(i1) <- v2) sts';
        sts'
      with Not_found -> sts'
    end 
  | St_arith (i1, i2, c) when abstr_num ->
    begin
      try
	let v2 = value_in_state env st i2 in
	List.iter (fun st' -> st'.(i1) <- abstr_add env v2 c) sts';
        sts'
      with Not_found -> sts'
    end 
  | St_ite (reqs, a1, a2) -> (* explore both branches if possible *)
      let sts'1 = 
        if check_reqs env st reqs then 
          let sts' = List.map Array.copy sts' in 
          apply_action env st sts' a1
        else [] in
      let sts'2 =
        if List.exists (fun req -> check_req env st (neg_req env req)) reqs
        then 
          let sts' = List.map Array.copy sts' in
          apply_action env st sts' a2
        else [] in
      begin
        match sts'1, sts'2 with
          | [], [] -> sts'
          | _::_, [] -> sts'1
          | [], _::_ -> sts'2
          | _, _ -> List.rev_append sts'1 sts'2
      end
  | _ (* St_ignore or St_arith when ignoring nums *) -> sts'

let apply_actions env st acts =
  let st' = Array.copy st in
  List.fold_left (apply_action env st) [st'] acts


let rec print_action env fmt = function
  | St_ignore -> ()
  | St_arith (i, v, c) -> 
      fprintf fmt "%a + %d" Atom.print 
	(Atom.Comp (id_to_term env i, Eq, id_to_term env v)) c
  | St_assign (i, -1) -> 
      fprintf fmt "%a = ." Term.print (id_to_term env i)
  | St_assign (i, v) -> 
      fprintf fmt "%a" Atom.print 
	(Atom.Comp (id_to_term env i, Eq, id_to_term env v))
  | St_ite (l, a1, a2) ->
      fprintf fmt "ITE (";
      List.iter (fun (i, op, v) -> 
	eprintf "%a && " Atom.print 
	  (Atom.Comp (id_to_term env i, op, id_to_term env v))
      ) l;
      fprintf fmt ", %a , %a )" (print_action env) a1 (print_action env) a2


let print_transition_fun env name sigma { st_reqs = st_reqs;
                                          st_udnfs = st_udnfs;
                                          st_actions = st_actions } fmt =
  fprintf fmt "%a (%a)\n" Hstring.print name Variable.print_subst sigma;
  fprintf fmt "requires { \n";
      List.iter (fun (i, op, v) -> 
	fprintf fmt "          %a\n" Atom.print 
	  (Atom.Comp (id_to_term env i, op, id_to_term env v))
      ) st_reqs;
      List.iter (fun dnf ->
	fprintf fmt "          ";
	List.iter (fun r ->
	  List.iter (fun (i, op, v) -> 
	    fprintf fmt "%a &&" Atom.print 
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


let rec ordered_subst = function
  | [] | [_] -> true
  | (_, x) :: ((_, y) :: _ as r) ->
      Hstring.compare x y <= 0 && ordered_subst r

let ordered_fst_subst = function
  | [] -> true
  | (_, x) :: _ as sb ->
      Hstring.equal x (List.hd Variable.procs) && ordered_subst sb



(****************************************************)
(* Instantiate transitions and transform to closure *)
(****************************************************)
        
let transitions_to_func_aux procs env reduce acc { tr_args = tr_args; 
		                                   tr_reqs = reqs; 
		                                   tr_name = name;
		                                   tr_ureq = ureqs;
		                                   tr_assigns = assigns; 
		                                   tr_upds = upds; 
		                                   tr_nondets = nondets } =
  if List.length tr_args > List.length procs then acc
  else 
    let d = Variable.all_permutations tr_args procs in
    (* do it even if no arguments *)
    let d = if d = [] then [[]] else d in
    (* let d = List.filter ordered_subst d in *)
    List.fold_left (fun acc sigma ->
      let reqs = SAtom.subst sigma reqs in
      let t_args_ef = 
	List.fold_left (fun acc p -> 
	  try (Variable.subst sigma p) :: acc
	  with Not_found -> p :: acc) [] tr_args in
      let udnfs = Forward.uguard_dnf sigma procs t_args_ef ureqs in
      let st_reqs = satom_to_st_req env reqs in
      let st_udnfs = List.map (List.map (satom_to_st_req env)) udnfs in
      let st_actions = assigns_to_actions env sigma [] assigns in
      let st_actions = nondets_to_actions env sigma st_actions nondets in
      let st_actions = List.fold_left 
	(update_to_actions procs sigma env)
	st_actions upds in
      let st_actions = missing_reqs_to_actions st_actions st_reqs in
      let f = fun st ->
	if not (check_reqs env st st_reqs) then raise Not_applicable;
	if not (List.for_all (List.exists (check_reqs env st)) st_udnfs)
	then raise Not_applicable;
	apply_actions env st st_actions
      in
      let st_vars = 
        List.fold_left (fun acc (_, x) ->
          Hstring.HSet.add x acc) Hstring.HSet.empty sigma in
      let st_tr = {
        st_name = name;
        st_reqs = st_reqs;
        st_udnfs = st_udnfs;
        st_actions = st_actions;
        st_vars = st_vars;
        st_args = t_args_ef;
        st_f = f;
      } in
      if debug then print_transition_fun env name sigma st_tr err_formatter;
      reduce acc st_tr
    ) acc d


let transitions_to_func procs env =
  List.fold_left 
    (transitions_to_func_aux procs env (fun acc st_tr -> st_tr :: acc)) []





let post st visited trs acc cpt_q depth =
  if limit_forward_depth && depth >= forward_depth then acc
  else
    List.fold_left (fun acc st_tr ->
      try 
        let sts = st_tr.st_f st in
        List.fold_left (fun acc s ->
          if HST.mem visited s then acc else
            (incr cpt_q; (depth + 1, s) :: acc)
        ) acc sts
      with Not_applicable -> acc) acc trs


let post_bfs st visited trs q cpt_q depth =
  if not limit_forward_depth || depth < forward_depth then
    List.iter (fun st_tr ->
      try 
        let sts = st_tr.st_f st in
        List.iter (fun s ->
          if not (HST.mem visited s) then begin
            incr cpt_q;
            Queue.add (depth + 1, s) q
          end
        ) sts
      with Not_applicable -> ()) trs

let hset_none = Hstring.HSet.singleton (Hstring.make "none")

let post_bfs_switches st visited trs q cpt_q cpt_f depth prev_vars =
  let temp_table = HST.create 2009 in
  let rec aux = function
    | [] -> ()
    | (st, last_vars) :: r ->
        let to_do =
          List.fold_left (fun to_do st_tr ->
            try 
              let sts = st_tr.st_f st in
              let vars = st_tr.st_vars in
              let switching = Hstring.HSet.equal vars last_vars ||
                Hstring.HSet.equal last_vars hset_none in
              List.fold_left (fun to_do s ->
                if not (HST.mem visited s || HST.mem temp_table s) then
                  if switching then begin
                    incr cpt_q;
                    Queue.add (depth + 1, vars, s) q;
                    incr cpt_f;
                    HST.add visited st ();
                    to_do
                  end 
                  else begin 
                    HST.add temp_table st ();
                    (s, vars) :: to_do
                  end
                else to_do
              ) to_do sts
            with Not_applicable -> to_do) r trs
        in
        aux to_do
  in
  if not limit_forward_depth || depth < forward_depth then aux [st, prev_vars]


let check_cand env state cand = 
  not (List.for_all (fun l -> check_req env state (neg_req env l)) cand)


let forward_dfs s procs env l =
  let explicit_states = env.explicit_states in
  let cpt_f = ref 0 in
  let cpt_q = ref 1 in
  let trs = env.st_trs in
  let rec forward_rec s procs trs = function
    | [] ->
        if not quiet then eprintf "Total forward nodes : %d@." !cpt_f
    | (depth, st) :: to_do ->
	decr cpt_q;
	if HST.mem explicit_states st then
	  forward_rec s procs trs to_do
        else
	  let to_do = post st explicit_states trs to_do cpt_q depth in
	  incr cpt_f;
	  if debug && verbose > 1 then
            eprintf "%d : %a\n@." !cpt_f
              SAtom.print (state_to_cube env st);
	  if not quiet && !cpt_f mod 1000 = 0 then
            eprintf "%d (%d)@." !cpt_f !cpt_q;
	  (* HI.add explicit_states hst st; *)
	  HST.add explicit_states st ();
          env.states <- st :: env.states;
	  forward_rec s procs trs to_do
  in
  forward_rec s procs trs l

let remove_first h =
  try HST.iter (fun hst _ -> HST.remove h hst; raise Exit) h
  with Exit -> ()

let already_visited env h st =
  HST.mem h st ||
  List.exists (fun st_sigma ->
    HST.mem h (apply_perm_state env st st_sigma)) env.perm_states

let add_all_syms env h st =
  HST.add h st ();
  List.iter (fun st_sigma ->
    HST.add h (apply_perm_state env st st_sigma) ()) env.perm_states

let forward_bfs s procs env l =
  let h_visited = env.explicit_states in
  let cpt_f = ref 0 in
  let cpt_r = ref 0 in
  let cpt_q = ref 1 in
  let trs = env.st_trs in
  let to_do = Queue.create () in
  List.iter (fun td -> Queue.add td to_do) l;
  while not (Queue.is_empty to_do) &&
          (max_forward = -1 || !cpt_f < max_forward) do
    let depth, st = Queue.take to_do in
    decr cpt_q;
    if not (HST.mem h_visited st) then begin
    (* if not (already_visited env explicit_states st) then begin *)
      post_bfs st h_visited trs to_do cpt_q depth;
      incr cpt_f;
      if debug && verbose > 1 then
        eprintf "%d : %a\n@." !cpt_f
          SAtom.print (state_to_cube env st);
      if not quiet && !cpt_f mod 1000 = 0 then
        eprintf "%d (%d)@." !cpt_f !cpt_q;
      (* if !cpt_f mod 3 = 1 then *)
      incr cpt_r;
      HST.add h_visited st ();
      env.states <- st :: env.states;
      (* add_all_syms env explicit_states st *)
    end
  done;
  if not quiet then eprintf "Total forward nodes : %d@." !cpt_r

let forward_bfs_switches s procs env l =
  let explicit_states = env.explicit_states in
  let cpt_f = ref 0 in
  let cpt_q = ref 1 in
  let trs = env.st_trs in
  let to_do = Queue.create () in
  List.iter (fun (idp, ist)  -> 
    Queue.add (idp, hset_none, ist) to_do) l;
  while not (Queue.is_empty to_do) do
    let depth, last_vars, st = Queue.take to_do in
    decr cpt_q;
    if not (HST.mem explicit_states st) then begin
      post_bfs_switches 
        st explicit_states trs to_do cpt_q cpt_f depth last_vars;
      incr cpt_f;
      if debug && verbose > 1 then
        eprintf "%d : %a\n@." !cpt_f
          SAtom.print (state_to_cube env st);
      if not quiet (* && !cpt_f mod 1000 = 0 *) then
        eprintf "%d (%d)@." !cpt_f !cpt_q;
      (* if !cpt_f > 3_000_000 then remove_first explicit_states; *)
      HST.add explicit_states st ();
      env.states <- st :: env.states;
    end
  done;
  if not quiet then eprintf "Total forward nodes : %d@." !cpt_f

    
(************************************************************************)
(* Forward enumerative search, states are insterted in the global hash- *)
(* table explicit_states                                                *)
(************************************************************************)

let search procs init =
  TimeForward.start ();
  let procs = procs (*@ init.t_glob_proc*) in
  let env = init_tables procs init in
  let st_inits = init_to_states env procs init in
  if debug then 
    List.iter (fun (_, st) ->
      eprintf "init : %a\n@." SAtom.print (state_to_cube env st))
      st_inits;
  let env = { env with st_trs = transitions_to_func procs env init.t_trans } in
  global_envs := env :: !global_envs;
  forward_bfs init procs env st_inits;
  let st = HST.stats env.explicit_states in
  if verbose > 0 then begin
    printf "\nStatistics@.";
    printf   "----------@.";
    printf "num_bindings : %d@." st.Hashtbl.num_bindings;
    printf "num_buckets : %d@." st.Hashtbl.num_buckets;
    printf "max_bucket_length : %d@." st.Hashtbl.max_bucket_length;
    printf "Bucket histogram : @?";
    Array.iteri (fun i v -> if v <> 0 then printf "[%d->%d]" i v )
		st.Hashtbl.bucket_histogram;
    printf "@.";
  end;
  List.iter (fun s -> Obj.set_tag (Obj.repr s) (Obj.no_scan_tag)) env.states;
  (* Prevent the GC from scanning the list env.states as it is going to be
     kept in memory all the time. *)
  env.explicit_states <- HST.create 1;
  Gc.compact ();
  TimeForward.pause ()


let resume_search_from procs init = assert false


exception Found_f of state_transistion

let find_tr_funs env name =
  List.filter (fun tr -> Hstring.equal tr.st_name name) env.st_trs

let replay_trace_and_expand procs system faulty =
  List.iter (fun env ->
  (* let tmp_visited = HST.create 2_000_001 in *)
  let st_inits = List.map snd (init_to_states env procs system) in
  let trc = faulty.from in
  let rec replay trc sts depth =
    if depth >= forward_depth then sts
    else match sts, trc with
      | [], _ | _, [] -> sts
      | _, ({tr_name = name}, args, _) :: trc ->
          let st_trs = find_tr_funs env name in
          let to_do =
            List.fold_left (fun acc st_tr ->
              List.fold_left (fun acc st ->
                
                eprintf ">>> : %a\n@."
                  SAtom.print (state_to_cube env st);

                try List.rev_append (st_tr.st_f st) acc
                with Not_applicable -> acc) acc sts
            ) [] st_trs in
          eprintf "%a ( %a )@." Hstring.print name Variable.print_vars args; 
          replay trc to_do (depth + 1)
  in
  let new_inits = replay trc st_inits 0 in
  List.iter (fun (st) ->
  eprintf "new_inits : %a\n@." SAtom.print (state_to_cube env st))
    new_inits;
  forward_bfs faulty procs env (List.map (fun s -> 0, s) new_inits)
 ) !global_envs


let satom_to_cand env sa =
  SAtom.fold (fun a c -> match Atom.neg a with
    | Atom.Comp (t1, op, t2) -> 
        (HT.find env.id_terms t1, op, HT.find env.id_terms t2) :: c
    | _ -> raise Not_found)
    sa []


exception Sustainable of Node.t list


(*********************************************************************)
(* Check if there exists one (or many) approximation candidates that *)
(* cannot be disproved by the finite model                           *)
(*********************************************************************)


exception TooBig of t_system list

let alpha_renamings env procs s =
  let d = List.rev (Variable.all_permutations (Node.variables s) procs) in
  (* keep list.rev in order for the first element of perm to be
     a normalized cube as we will keep this only one if none of
     perm can be disproved *)
  List.fold_left (fun p sigma ->
    let c = Cube.subst sigma s.cube in
    let s' = Node.create ~kind:Approx c in
    (satom_to_cand env (Node.litterals s'), s') :: p
  ) [] d



let resist_on_trace_size progress_inc ls env =
  let procs = List.rev (List.tl (List.rev env.all_procs)) in
  let cands, too_big =
    List.fold_left (fun (acc, too_big) s ->
      if Node.dim s > env.model_cardinal then acc, s :: too_big
      else
	try (alpha_renamings env procs s) :: acc, too_big
	with Not_found -> acc, too_big
    ) ([], []) ls  in
  let cands = ref (List.rev cands) in
  let too_big = List.rev too_big in
  if !cands = [] then []
  else
    try
      if not quiet then eprintf "@{<fg_black_b>@{<i>";
                        (* will be forgotten by flushs *)
      let one_step () = if nocolor then eprintf "#@?" else eprintf " @?" in
      let cpt = ref 0 in
      List.iter (fun st ->
        incr cpt;
        if not quiet && !cpt mod progress_inc = 0 then one_step ();
        cands := List.filter (fun p -> 
          List.for_all (fun (c, _) -> check_cand env st c) p
        ) !cands;
        if !cands = [] then raise Exit;
      ) env.states;
      let remain = List.fold_left (fun acc clas ->
	match clas with
	| [] -> acc
	| (_, s) :: _ -> s :: acc) [] !cands in
      List.rev_append remain too_big
    with 
      | Exit | Not_found -> too_big


let smallest_to_resist_on_trace ls =
  try
    let nb =
      List.fold_left (fun nb env -> nb + List.length env.states)
		     0 !global_envs
    in
    let progress_inc = nb / Pretty.vt_width + 1 in
    TimeCheckCand.start ();
    let resistants =
      List.fold_left
	(resist_on_trace_size progress_inc) ls !global_envs in
    match resistants with
      | s :: _ -> raise (Sustainable [s])
      | [] -> raise Not_found
  with
  | Exit | Not_found ->
     TimeCheckCand.pause ();
     if not quiet then eprintf "@{</i>@}@{<bg_default>@}@{<fg_red>X@}@.";
     []
  | Sustainable ls ->
     TimeCheckCand.pause ();
     if not quiet then eprintf "@{</i>@}@{<bg_default>@}@{<fg_green>!@}@.";
     ls



let one_resist_on_trace_size s env =
    if Node.dim s > env.model_cardinal then true
    else
      try
        let procs = List.rev (List.tl (List.rev env.all_procs)) in
        let ls = alpha_renamings env procs s in
        List.iter (fun st ->
          if not (List.for_all (fun (c, _) -> check_cand env st c) ls) then
            raise Exit;
        ) env.states;
        true
    with 
      | Exit | Not_found -> false


let fast_resist_on_trace ls =
  let progress_inc = (List.length ls) / Pretty.vt_width + 1 in
  if not quiet then eprintf "@{<fg_black_b>@{<i>";
  (* will be forgotten by flushs *)
  let one_step () = if nocolor then eprintf "#@?" else eprintf " @?" in
  let cpt = ref 0 in
  TimeCheckCand.start ();
  try 
    List.iter (fun s ->
      incr cpt;
      if not quiet && !cpt mod progress_inc = 0 then one_step ();
      if (List.for_all (one_resist_on_trace_size s) !global_envs)
      then raise (Sustainable [s])
    ) ls;
    TimeCheckCand.pause ();
    if not quiet then eprintf "@{</i>@}@{<bg_default>@}@{<fg_red>X@}@.";
    []
  with Sustainable cand ->
       TimeCheckCand.pause ();
       if not quiet then eprintf "@{</i>@}@{<bg_default>@}@{<fg_green>!@}@.";
       cand





(*-------------- interface -------------*)


let init system =
  set_liberal_gc ();
  let low = if brab_up_to then 1 else enumerative in
  for i = enumerative downto low do
    let procs = Variable.give_procs i in
    if not quiet then
      Pretty.print_title std_formatter
        ("STATEFULL ENUMERATIVE FORWARD ["^(string_of_int i)^" procs]");
    search procs system;
    if not quiet then printf "%a@." Pretty.print_double_line ();
  done;
  reset_gc_params ()
   

let first_good_candidate candidates =
  match fast_resist_on_trace candidates with
  | c :: _ -> Some c
  | [] -> None
