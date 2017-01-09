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
open Cubtypes
open Util

type trans_history = (Hstring.t * Hstring.t list) list

type richstate = {st : int array; mutable from : trans_history list}

module H = Hstring

module HT = Hashtbl.Make (Term)

module HH = Hashtbl.Make (H)

module HHL = Hashtbl.Make (struct
                 type t = Hstring.t * Hstring.t list
                 let equal (h1, hl1) (h2, hl2) = 
                   Hstring.equal h1 h2 && Hstring.list_equal hl1 hl2
                 let hash = Hashtbl.hash
               end)

module HI = Hashtbl.Make (struct 
                type t = int 
                let equal = (=) 
                let hash x = x
              end)

module HLI = Hashtbl.Make (struct 
                 type t = int list 
                 let equal = (=) 
                 let hash = Hashtbl.hash
               end)

module SI = Set.Make (struct
                type t = int
                let compare = Pervasives.compare
              end)

module SLI = Set.Make (struct
                 type t = int list
                 let compare = Pervasives.compare
               end)

module TMap = Map.Make (Term)

type state_info = int HT.t

let hash_state st = Hashtbl.hash_param 100 500 st

module HST = Hashtbl.Make 
               (struct 
                 (* type t = State.t *)
                 type t = State.t
                 let equal = (=)
                 let hash = hash_state
               end)


let rec pvars fmt = function 
  | [v] -> Format.fprintf fmt "%a" Hstring.print v
  | v :: tl -> Format.fprintf fmt "%a, %a" Hstring.print v pvars tl
  | _ -> ()

let rec phistory fmt = function
  | [] -> ()
  | [e, v] -> Format.fprintf fmt "%a(%a)\\" Hstring.print e pvars v;
  | (a, v) :: tl -> Format.fprintf fmt "%a(%a) -> %a" Hstring.print a 
                      pvars v phistory tl

let rec pfrom fmt = function
  | [] -> ()
  | [h] -> Format.fprintf fmt "%a!" phistory h;
  | h :: hl -> Format.fprintf fmt "%a\n%a" phistory h pfrom hl


(* This is a queue with a hash table on the side to avoid storing useless
   states, the overhead of the hashtable is negligible and allows to reduce the
   memory occupied by the queue (which is generally a lot larger than the state
   table for BFS) *)
module HQueue : sig
  
  type elt = int * richstate * State.t
  type t = elt Queue.t * richstate HST.t
                                   
  val create : int -> t
  val add : ?cpt_q : int ref -> ?debug : bool -> elt -> t -> unit
  val is_empty : t -> bool
  val take : t -> elt

end = struct

  type elt = int * richstate * State.t
  type t = elt Queue.t * richstate HST.t

  let create size = Queue.create (), HST.create size

  let add ?(cpt_q=ref 0) ?(debug=false) x (q, h) =
    let (_, rs, s) = x in
    try 
      let {from} = HST.find h s in
      if debug then 
        Format.eprintf " @{<fg_red>Already Visited@}@.\t%a@." 
          pfrom (List.rev from)
    with Not_found ->
         if debug then Format.eprintf " @{<fg_green>New@}@.";
         incr cpt_q;
         HST.add h s rs;
         Queue.add x q

  let is_empty (q, _) = Queue.is_empty q

  let take (q, h) =
    let x = Queue.take q in
    let _, _, s = x in
    HST.remove h s;
    x
      
end




type st_req = int * op_comp * int

type st_action = 
  | St_ignore
  | St_assign of int * int 
  | St_arith of int * int * int
  | St_ite of st_req list * st_action * st_action


exception Not_applicable

type state_transition = {
    st_name : Hstring.t;
    st_reqs : st_req list;
    st_udnfs : st_req list list list;
    st_actions : st_action list;
    st_f : State.t -> State.t list;
    st_vars : Hstring.t list;
    st_args : Hstring.t list;
  }


type env = {
    model_cardinal : int;
    var_terms : Term.Set.t;
    nb_vars : int;
    max_id_vars : int;
    perm_procs : (int * int) list list;
    perm_states : ((Hstring.t * Hstring.t) list *
                     (int * int) list * (int * int) list) list;
    first_proc : int;
    extra_proc : int;
    all_procs : Hstring.t list;
    proc_ids : int list;
    id_terms : int HT.t;
    terms_id : Term.t HI.t;
    intervals : (int * int) HH.t;
    id_true : int;
    id_false : int;
    st_trs : state_transition list;
    low_int_abstr : int;
    up_int_abstr : int;
    pinf_int_abstr : int;
    minf_int_abstr : int;
    proc_substates : int list HLI.t;
    reverse_proc_substates : int list HI.t;
    partial_order : int list list;

    table_size : int;
    mutable explicit_states : (richstate option) HST.t;
    (* mutable states : State.t list; *)
    mutable states : richstate list;
    mutable histories : trans_history list;
    mutable fringe : State.t list;
    mutable bad_states : ((int * op_comp * int) list * Node.t * Variable.subst) list
  }

let empty_env = {
    model_cardinal = 0;
    var_terms = Term.Set.empty;
    max_id_vars = 0;
    nb_vars = 0;
    perm_procs = [];
    perm_states = [];
    first_proc = 0;
    extra_proc = 0;
    all_procs = [];
    proc_ids = [];
    id_terms = HT.create 0;
    terms_id = HI.create 0;
    intervals = HH.create 0;
    id_true = 0;
    id_false = 0;
    st_trs = [];
    low_int_abstr = 0;
    up_int_abstr = 0;
    pinf_int_abstr = 0;
    minf_int_abstr = 0;
    proc_substates = HLI.create 0;
    reverse_proc_substates = HI.create 0;
    partial_order = [];

    table_size = 0;
    explicit_states = HST.create 0;
    states = [];
    histories = [];
    fringe = [];
    bad_states = [];
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

exception Found of term

(* inefficient but only used for debug *)
let id_to_term env id =
  try
    HT.iter (fun t i -> if id = i then raise (Found t)) env.id_terms;
    raise Not_found
  with Found t -> t

(* inefficient but only used for debug *)
let state_to_cube env st =
  let i = ref 0 in
  Array.fold_left (fun sa sti ->
      let sa = 
        if sti <> -1 then
	  let t1 = id_to_term env !i in
	  let t2 =
            if sti = env.minf_int_abstr then Elem (Hstring.make "-oo", Constr)
            else if sti = env.pinf_int_abstr then Elem (Hstring.make "+oo", Constr) 
            else id_to_term env sti in
	  SAtom.add (Atom.Comp (t1, Eq, t2)) sa
        else sa
      in
      incr i; sa)
    SAtom.empty st

let print_state env fmt st = SAtom.print fmt (state_to_cube env st)

let print_state_ia fmt st =
  Array.iter (Format.fprintf fmt "%d;") st

(* let print_all env = *)
(*   List.iter (eprintf "--- @[<hov>%a@]@." (print_state env)) env.states *)

let print_all env =
  List.iter (fun {st} -> 
      eprintf "--- @[<hov>%a@]@." (print_state env) st) env.states

let print_fringe env frg =
  List.iter (eprintf "--- @[<hov>%a@]@." (print_state env)) frg

let swap a i j =
  if i <> j then
    let tmp = a.(i) in
    a.(i) <- a.(j);
    a.(j) <- tmp
               
let swap_c a (i,j) = swap a i j

let apply_perm_state env st (_, p_vars, p_procs) =
  let st' = Array.copy st in
  List.iter (swap_c st') p_vars;
  for i = 0 to env.nb_vars - 1 do
    try let v = List.assoc st'.(i) p_procs in st'.(i) <- v
    with Not_found -> ()
  done;
  st'

(* Applying substitutions in place is tricky because some idexes of the array
   encode terms like A[#1,#2]. We proceed by swapping here, and remember the
   shifting introduced thanks to the mapping rho. *)
let apply_subst_in_place env st sigma =
  if not (HI.length sigma = 0) then begin

      let proc_subs = ref SLI.empty in
      let rho = HLI.create env.nb_vars in

      (* First apply substitutions in the values of the state variables *)
      for i = 0 to env.nb_vars - 1 do
        (try st.(i) <- HI.find sigma st.(i) 
         with Not_found -> ());

        try
          (* collect process domains (like (#1, #2) ) *)
          let proc_domain = HI.find env.reverse_proc_substates i in
          proc_subs := SLI.add proc_domain !proc_subs;
        with Not_found -> ()

      done;

      SLI.iter (fun proc_domain ->
          try
            (* sigma(proc_domain) *)
            let sigma_proc_domain = List.fold_left (fun acc j ->
                                        try HI.find sigma j :: acc
                                        with Not_found -> acc
                                      ) [] proc_domain |> List.rev in
            (* rho(proc_domain) *)
            let rho_proc_domain =
              try HLI.find rho proc_domain with Not_found -> sigma_proc_domain in
            (* encoding in terms of indexes *)
            let sigma_proc_sub = HLI.find env.proc_substates sigma_proc_domain in
            let rho_proc_sub = HLI.find env.proc_substates rho_proc_domain in

            (* Perform actual swaps on the encoded versions *)
            List.iter2 (fun i j ->
                (* eprintf "   exchanging %a <---> %a@."
             Term.print (id_to_term env i) Term.print (id_to_term env j); *)
                swap st i j) sigma_proc_sub rho_proc_sub;

            (* rho += sigma(proc_domain) |--> rho(proc_domain) *)
            HLI.replace rho sigma_proc_domain rho_proc_domain;
          with Not_found ->()
        ) !proc_subs

    end

let apply_subst env st sigma =
  let st' = Array.copy st in
  apply_subst_in_place env st' sigma;
  st'

let is_proc env v = env.first_proc <= v && v < env.extra_proc




let find_subst_for_norm env st =
  let met = ref [] in
  let remaining = ref env.proc_ids in
  let sigma = HI.create env.model_cardinal in
  for i = 0 to Array.length st - 1 do
    let v = st.(i) in
    match !remaining with
      | r :: tail ->
          if is_proc env v && v <> env.extra_proc && (* r <> env.extra_proc && *)
               not (List.mem v !met) then begin
              met := v :: !met;
              remaining := tail;
              if v <> r then HI.add sigma v r;
            end
      | _ -> ()
  done;
  let not_met = List.filter (fun v -> not (List.mem v !met)) env.proc_ids in
  List.iter2 (fun v r -> if v <> r then HI.add sigma v r) not_met !remaining;
  sigma

let rec map_with_procs acc procs ord = match procs, ord with
    | p :: rp, (_,_,o) :: ro -> map_with_procs ((p, o) :: acc) rp ro
    | _, [] -> List.rev acc
    | [], _ -> assert false

let find_subst_for_norm2 sigma env st =
  (* let sigma = HI.create env.model_cardinal in *)
  List.iter (fun order ->
      HI.clear sigma;
      List.map (fun i ->
          let lpi = List.hd (List.rev (HI.find env.reverse_proc_substates i)) in
          (i, st.(i), lpi)
        ) order
      |> List.stable_sort (fun (_, v1, _) (_, v2, _) -> compare v1 v2)
      |> map_with_procs [] env.proc_ids
      |> List.iter (fun (x, y) ->
             (* let y = try HI.find sigma y with Not_found -> y in *)
             if x <> y then HI.replace sigma x y);
      apply_subst_in_place env st sigma;
    ) [List.hd env.partial_order]
            
let normalize_state env st =
  let sigma = find_subst_for_norm env st in
  apply_subst_in_place env st sigma
                       
let normalize_state2 env st =
  let st' = Array.copy st in
  let sigma = find_subst_for_norm env st in
  find_subst_for_norm2 sigma env st';
  st'

let global_envs = ref []

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


let is_variable env id = id <= env.max_id_vars

let is_int_real = function
  | Elem (x,Glob) | Access (x, _) -> 
      snd (Smt.Symbol.type_of x) = Smt.Type.type_int ||
        snd (Smt.Symbol.type_of x) = Smt.Type.type_real
  | _ -> false

let all_constr_terms () =
  List.rev_map (fun x -> Elem (x, Constr)) (Smt.Type.all_constructors ())

let terms_of_procs = List.map (fun x -> Elem (x, Var))


let rec power_p i p = if p <= 0 then 1 else i * power_p i (p-1)

let table_size nb_procs nb_vars =
  let r = min 2_000_009
            (max 100 ((power_p (nb_procs * nb_vars) nb_procs) * (nb_procs ))) in
  if not quiet then eprintf "table size : %d@." r;
  r

let add_pos_to_proc_substate ht
      proc_substates reverse_proc_substates =
  Term.Set.iter (function
      | Access (_, ps) as t ->
          let i = HT.find ht t in
          let ids_ps = List.map (fun hp -> HT.find ht (Elem (hp, Var))) ps in
          let sub_ps = try HLI.find proc_substates ids_ps with Not_found -> [] in
          (* List.iter (fun p -> eprintf "%d (%a), " p Term.print t) ids_ps; *)
          (* eprintf "at %d@." i; *)
          HLI.replace proc_substates ids_ps (i :: sub_ps);
          HI.add reverse_proc_substates i ids_ps
      | _ -> ()
    )

let partial_order ht var_terms nb_vars =
  (* let orders = HI.create nb_vars in *)
  let map_orders =
    Term.Set.fold (fun t acc -> match t with
                                  | Access (a, ps) ->
                                      let i = HT.find ht t in
                                      let ups = List.rev (List.tl (List.rev ps)) in
                                      let t_par = Access (a, ups) in
                                      let others = try TMap.find t_par acc with Not_found -> SI.empty in
                                      let pord = SI.add i others in
                                      TMap.add t_par pord acc
                                  | _ -> acc
      ) var_terms TMap.empty 
  in
  (* let rec populate_orders = function *)
  (*   | [] -> () *)
  (*   | i :: after -> HI.add i after; populate_orders after *)
  (* in *)
  let orders = TMap.fold (fun _ one_order acc ->
                   (SI.elements one_order) :: acc
                 ) map_orders [] in
  List.sort (fun l1 l2 -> compare (List.hd l1) (List.hd l2)) orders

let init_tables ?(alloc=true) procs s =
  let var_terms = Forward.all_var_terms procs s in
  let proc_terms = terms_of_procs procs in (* constantes *)
  let constr_terms = all_constr_terms () in (* constantes *)
  let nb_vars = Term.Set.cardinal var_terms in
  let nb_procs = List.length proc_terms in
  let nb_consts = nb_procs + List.length constr_terms in
  let ht = HT.create (nb_vars + nb_consts) in
  let i = ref 0 in

  let intervals = HH.create nb_vars in
  
  let pow2 n = 2 lsl (n-1) in
  
  Term.Set.iter (fun t ->
      (match t with
         | Access (h, vl) ->
             if not (HH.mem intervals h) then
               let it = pow2 (List.length vl) in
               HH.add intervals h (!i, !i + it - 1)
         | _ -> ()
      );
      HT.add ht t !i; incr i) var_terms;

  let max_id_vars = !i - 1 in
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
  if debug && verbose > 2 then
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
  let hi = HI.create (nb_vars + nb_consts) in
  HT.iter (fun t i -> HI.add hi i t) ht;
  (* This is some bookeeping to allow in place substitutions *)
  let proc_substates = HLI.create nb_procs in
  let reverse_proc_substates = HI.create nb_procs in
  add_pos_to_proc_substate ht proc_substates reverse_proc_substates var_terms; 

  let tsize = table_size nb_procs nb_vars in
  
  { model_cardinal = nb_procs;
    var_terms = var_terms;
    nb_vars = nb_vars;
    max_id_vars = max_id_vars;
    perm_procs = perm_procs;
    perm_states = perm_states;
    first_proc = first_proc;
    extra_proc = extra_proc;
    all_procs = all_procs;
    proc_ids = proc_ids;
    id_terms = ht;
    terms_id = hi;
    intervals = intervals;
    id_true = id_true;
    id_false = id_false;
    st_trs = [];

    low_int_abstr = a_low;
    up_int_abstr = a_up;
    pinf_int_abstr = a_up + 1;
    minf_int_abstr = -3;

    proc_substates = proc_substates;
    reverse_proc_substates = reverse_proc_substates;
    partial_order = partial_order ht var_terms nb_vars;

    table_size = tsize;
    explicit_states = HST.create (if alloc then tsize else 0);
    states = [];
    histories = [];
    fringe = [];
    bad_states = [];
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
  List.map (fun st -> 0, {st; from = [[]]}, st) sts
           

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

let swts_to_stites env at sigma swts =
  let rec sd acc = function
    | [] -> assert false
    | [d] -> acc, d
    | s::r -> sd (s::acc) r in
  let swts, (d, t) = sd [] swts in
  (* assert (d = SAtom.singleton True); *)
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


let assigns_to_actions env sigma acc tr_assigns =
  List.fold_left 
    (fun acc (h, gu) ->
      let nt = Elem (h, Glob) in
      match gu with
        | UTerm t ->
            let t = Term.subst sigma t in
            begin
              try 
                let a = match t with
                    | Arith (t', cs) ->
                        St_arith (HT.find env.id_terms nt,
                                  HT.find env.id_terms t', int_of_consts cs)
                    | _ ->
                        St_assign (HT.find env.id_terms nt, HT.find env.id_terms t)
                in a :: acc
              with Not_found -> acc
            end
        | UCase swts -> swts_to_stites env nt sigma swts :: acc
    ) acc tr_assigns

let nondets_to_actions env sigma acc =
  List.fold_left 
    (fun acc (h) ->
      let nt = Elem (h, Glob) in
      try (St_assign (HT.find env.id_terms nt, -1)) :: acc
      with Not_found -> acc
    ) acc

let update_to_actions procs sigma env acc
      {up_arr=a; up_arg=lj; up_swts=swts} =
  let indexes = Variable.all_arrangements_arity a procs in
  List.fold_left (fun acc li ->
      let sigma = (List.combine lj li) @ sigma in
      let at = Access (a, li) in
      swts_to_stites env at sigma swts :: acc
    ) acc indexes

let missing_reqs_to_actions env acct =
  List.fold_left (fun acc -> function
      | (a, Eq, b) ->
          (* variable on lhs *)
          let a, b =
            if not (is_variable env a) && is_variable env b then b, a
            else a, b in
          if List.exists
               (function St_assign (a', _) -> a = a' | _ -> false) acct
          then acc
          else (St_assign (a,b)) :: acc
      | _ -> acc) acct

let value_in_state env st i =
  if i <> -1 && i < env.nb_vars then st.(i) else i

let check_req env st (i1, op, i2) =
  let v1 = value_in_state env st i1 in
  let v2 = value_in_state env st i2 in
  v1 = -1 || v2 = -1 ||
    match op with
      | Eq -> v1 = v2
      | Neq -> v1 <> v2
      | Le -> v1 <= v2
      | Lt -> v1 < v2

let check_reqs env st = List.for_all (check_req env st)


let neg_req env = function
  | a, Eq, b ->
      if b = env.id_true then a, Eq, env.id_false
      else if b = env.id_false then a, Eq, env.id_true
      else a, Neq, b
  | a, Neq, b -> a, Eq, b
  | a, Le, b -> b, Lt, a
  | a, Lt, b -> b, Le, a


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
                                                                
let transitions_to_func_aux procs env reduce acc 
      { tr_info = { tr_args = tr_args; 
		    tr_reqs = reqs; 
		    tr_name = name;
		    tr_ureq = ureqs;
		    tr_assigns = assigns; 
		    tr_upds = upds; 
		    tr_nondets = nondets }} =
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
        let st_actions = missing_reqs_to_actions env st_actions st_reqs in
        let f = fun st ->
	  if not (check_reqs env st st_reqs) then raise Not_applicable;
	  if not (List.for_all (List.exists (check_reqs env st)) st_udnfs)
	  then raise Not_applicable;
	  apply_actions env st st_actions
        in
        let st_vars = 
          List.map (fun (_, x) -> x) sigma in
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

let is_general env l = 
  let seen = HH.create 0 in
  List.for_all (fun (i, _) ->
      let ti = HI.find env.terms_id i in
      match ti with
        | Access (h, _) -> if HH.mem seen h then false else
                             (HH.add seen h (); true)
        | _ -> false
    ) l

let create_new_state env s l =
  let s' = State.copy s in
  List.iter (fun (i, (_, e2)) ->
      let ti = HI.find env.terms_id i in
      match ti with
        | Access (h, _) ->
            let (bi, bs) = HH.find env.intervals h in
            for j = bi to bs do
              s'.(j) <- e2
            done
        | _ -> (* assert false *) ()
    ) l; s'

let generalize_state env s hs system =
  let s' = State.copy s in
  let vars = hs in
  List.iter (fun arr ->
      let ta = Access(arr, vars) in
      try
        let i = HT.find env.id_terms ta in
        let (bi, bs) = HH.find env.intervals arr in
        let def = s.(i) in
        for i = bi to bs do s'.(i) <- def done;
      with Not_found -> ()
    ) system.t_arrays;
  s'
    
let forward_depth = ref (-1)
let limit_forward_depth = ref false

let post_dfs st visited trs q cpt_q depth = 
  if not !limit_forward_depth || depth < !forward_depth then
    List.iter (fun st_tr ->
        try
          let sts = st_tr.st_f st in
          List.iter (fun s ->
              if not (HST.mem visited s) then begin
                  incr cpt_q;
                  Stack.push (depth + 1, s) q
                end
            ) sts
        with Not_applicable -> ()) trs

let hset_none = Hstring.HSet.singleton (Hstring.make "none")

(* let  *)

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
                let switching = assert false(* Hstring.HSet.equal vars last_vars || *)
                (* Hstring.HSet.equal last_vars hset_none  *)in
                List.fold_left (fun to_do s ->
                    if not (HST.mem visited s || HST.mem temp_table s) then
                      if switching then begin
                          incr cpt_q;
                          Queue.add (depth + 1, vars, s) q;
                          incr cpt_f;
                          HST.add visited st None;
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
  if not !limit_forward_depth || depth < !forward_depth then aux [st, prev_vars]


let check_cand env state cand = 
  not (List.for_all (fun l -> check_req env state l) cand)

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

let forward_dfs s procs env l =
  let h_visited = env.explicit_states in
  let cpt_f = ref 0 in
  let cpt_r = ref 0 in
  let cpt_q = ref 1 in
  let trs = env.st_trs in
  let to_do = Stack.create () in
  List.iter (fun td -> Stack.push td to_do) l;
  while not (Stack.is_empty to_do) &&
          (max_forward = -1 || !cpt_f < max_forward) do
    let depth, st = Stack.pop to_do in
    decr cpt_q;
    if not (HST.mem h_visited st) then begin
        (* if not (already_visited env explicit_states st) then begin *)
        post_dfs st h_visited trs to_do cpt_q depth;
        incr cpt_f;
        if debug && verbose > 1 then
          eprintf "%d : %a\n@." !cpt_f
            SAtom.print (state_to_cube env st);
        if not quiet && !cpt_f mod 1000 = 0 then
          eprintf "%d (%d)@." !cpt_f !cpt_q;
        (* if !cpt_f mod 3 = 1 then *)
        incr cpt_r;
        HST.add h_visited st None;
        env.states <- {st; from = [[]]} :: env.states;
        if !limit_forward_depth && depth = !forward_depth then
          env.fringe <- st :: env.fringe;
        (* add_all_syms env explicit_states st *)
      end
  done


let maxd = ref 0

let forward_bfs_switches s procs env l = 
  let explicit_states = env.explicit_states in
  let cpt_f = ref 0 in
  let cpt_q = ref 1 in
  let trs = env.st_trs in
  let to_do = Queue.create () in
  List.iter (fun (idp, ist)  ->
      Queue.add (idp, [], ist) to_do) l;
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
        HST.add explicit_states st None;
        env.states <- {st; from = [[]] } :: env.states;
        if !limit_forward_depth && depth = !forward_depth - 1 then
          env.fringe <- st :: env.fringe;
      end
  done
    
(***********************************************************************)
(* Forward enumerative search, states are inserted in the global hash- *)
(* table explicit_states                                               *)
(***********************************************************************)
let shuffle d =
  let nd = List.rev_map (fun c -> (Random.bits (), c)) d in
  let sond = List.sort compare nd in
  List.rev_map snd sond

let no_scan_states env =
  (* Prevent the GC from scanning the list env.states as it is going to be
     kept in memory all the time. *)
  List.iter (fun {st; from} -> Obj.set_tag (Obj.repr st) (Obj.no_scan_tag);
                               List.iter (fun th -> 
                                   List.iter (fun (s, sl) ->
                                       Obj.set_tag (Obj.repr st) (Obj.no_scan_tag);
                                       List.iter (fun s -> Obj.set_tag (Obj.repr st) (Obj.no_scan_tag)) sl
                                     ) th
                                 ) from
    ) env.states


let study_fringe env =
  let f = env.fringe in
  let f' = List.map (normalize_state2 env) f in
  (match f' with
     | [] -> eprintf "Nothing to study@."
     | hd::tl -> 
         let st = Array.copy hd in
         List.iter (
             fun st' -> Array.iteri (
                            fun i v ->
                            if st.(i) <> v then st.(i) <- -1
                          ) st'
           ) tl;
         eprintf "State : %a@." (print_state env) st);
  (match f with
     | [] -> eprintf "Nothing to study@."
     | hd::tl -> 
         let st = Array.copy hd in
         List.iter (
             fun st' -> Array.iteri (
                            fun i v ->
                            if st.(i) <> v then st.(i) <- -1
                          ) st'
           ) tl;
         eprintf "State : %a@." (print_state env) st)

let nums = ref 0

let save_stats () =
  let st = HST.stats (List.hd (!global_envs)).explicit_states in
  nums := st.Hashtbl.num_bindings;
  Format.eprintf "Nums : %d@." !nums

let get_stats () = !nums

let finalize_search env =
  save_stats ();
  let st = HST.stats env.explicit_states in
  if not quiet then (
    printf "Total forward nodes : %d@." st.Hashtbl.num_bindings;
    printf "All (depth max : %d) : %d@." !maxd (List.length env.states);
    if print_forward_all then print_all env;
    printf "Fringe : %d@." (List.length env.fringe);
    if print_forward_frg then (
      print_fringe env env.fringe;
      study_fringe env
    )
  );
  if verbose > 0 || profiling then begin
      printf "\n%a" Pretty.print_line ();
      printf "@{<b>Statistics@}\n";
      printf "----------\n";
      printf "Bindings         : %d@." st.Hashtbl.num_bindings;
      printf "Buckets          : %d@." st.Hashtbl.num_buckets;
      printf "Max bucket size  : %d@." st.Hashtbl.max_bucket_length;
      printf "Bucket histogram : @?";
      Array.iteri (fun i v -> if v <> 0 then printf "[%d->%d]" i v )
        st.Hashtbl.bucket_histogram;
      printf "@.";
    end;
  no_scan_states env;
  env.explicit_states <- HST.create 1;
  Gc.compact ();
  Gc.full_major ();
  TimeForward.pause ()


let install_sigint () =
  Sys.set_signal Sys.sigint 
    (Sys.Signal_handle 
       (fun _ ->
         printf "\n\n@{<b>@{<fg_red>ABORTING ENUMERATIVE!@}@} \
                 Received SIGINT@.";
         printf "Finalizing search.@.";
         raise Exit
    ))

let resume_search_from procs init = assert false


exception Found_f of state_transition

let find_tr_funs env name =
  List.filter (fun tr -> Hstring.equal tr.st_name name) env.st_trs

let satom_to_cand env sa =
  SAtom.fold (fun a c -> match a with
                           | Atom.Comp (t1, op, t2) -> 
                               (HT.find env.id_terms t1, op, HT.find env.id_terms t2) :: c
                           | _ -> raise Not_found)
    sa []


exception Sustainable of Node.t * Node.t list


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
      (satom_to_cand env (Node.litterals s'), s', sigma) :: p
    ) [] d


let one_step () = if nocolor then eprintf "#@?" else eprintf " @?"


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
      let cpt = ref 0 in
      List.iter (fun {st} ->
          incr cpt;
          if not quiet && !cpt mod progress_inc = 0 then one_step ();
          cands := List.filter (fun p -> 
                       List.for_all (fun (c, _, _) -> check_cand env st c) p
                     ) !cands;
          if !cands = [] then raise Exit;
        ) env.states;
      let remain = List.fold_left (fun acc clas ->
	               match clas with
	                 | [] -> acc
	                 | (_, s, _) :: _ -> s :: acc) [] !cands in
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
      | s :: _ -> raise (Sustainable (s, [s]))
      | [] -> raise Not_found
  with
    | Exit | Not_found ->
        TimeCheckCand.pause ();
        if not quiet then eprintf "@{</i>@}@{<bg_default>@}@{<fg_red>X@}@.";
        []
    | Sustainable (_, ls) ->
        TimeCheckCand.pause ();
        if not quiet then eprintf "@{</i>@}@{<bg_default>@}@{<fg_green>!@}@.";
        ls



type result_check = Good | Bad of State.t | CantSay
exception EBad of State.t * env
exception ECantSay


let state_impossible env st s =
  if Node.dim s > env.model_cardinal then true
  else
    try
      check_cand env st (satom_to_cand env (Node.litterals s))
    with 
      | Not_found -> false

let pp_op fmt = function
  | Eq -> Format.fprintf fmt "="
  | Lt -> Format.fprintf fmt "<"
  | Le -> Format.fprintf fmt "<="
  | Neq -> Format.fprintf fmt "!="

let pp_iopi_list fmt l =
  Format.eprintf "@[<hov 2>[@{<bg_default>@}@,";
  List.iter (fun (i1, op, i2) ->
      Format.eprintf "@[<hov>%d %a %d@]@ " i1 pp_op op i2
    ) l;
  Format.eprintf "@]]@\n"

let one_resist_on_trace_size s env =
  if Node.dim s <= env.model_cardinal then
    try
      let hahtbl = HT.create (Node.size s) in
      let atoms_cand = Node.litterals s in
      (* Format.eprintf "Node : %a@." Node.print s; *)
      (* Format.eprintf "Atoms_cand : %a@." SAtom.print atoms_cand; *)
      let fill_hahtbl st comp sigma =
        let amgis = Variable.inverse_subst sigma in
        let mapping =
          List.fold_left (fun acc (i1, _, _) ->
              let key = HI.find env.terms_id i1 in
              let bind = HI.find env.terms_id st.(i1) in
              let skey = Term.subst amgis key in
              let sbind = Term.subst amgis bind in
              TMap.add skey sbind acc
            ) TMap.empty comp in
        (* Format.eprintf "State : %a@\nSigma : %a@\nMapping : @." *)
        (*   (print_state env) st Variable.print_subst amgis; *)
        (* TMap.iter (fun t1 t2 -> *)
        (*     Format.eprintf "Key : %a@\nBind : %a@." *)
        (*       Term.print t1 Term.print t2 *)
        (*   ) mapping; *)
        (* Format.eprintf "<<<<<<<@."; *)
        SAtom.iter (fun a ->
            match a with
              | Atom.Comp (ta1, op, ta2) ->
                  let atoms, children =
                    try HT.find hahtbl ta1
                    with Not_found -> SAtom.empty, TMap.empty
                  in
                  let rep, mapping =
                    TMap.partition (
                        fun t1 t2 ->
                        Term.equal ta1 t1 &&
                          (match op with
                             | Eq -> Term.equal ta2 t2
                             | Neq -> not (Term.equal ta2 t2)
                             | _ -> assert false
                          )
                      ) mapping in
                  (* Format.eprintf "Rep : @."; *)
                  (* TMap.iter (fun t1 t2 -> *)
                  (*     Format.eprintf "%a@\nBind : %a@." *)
                  (*       Term.print t1 Term.print t2 *)
                  (*   ) rep; *)
                  (* TMap.iter (fun t1 t2 -> *)
                  (*     Format.eprintf "Map : %a@\nBind : %a@." *)
                  (*       Term.print t1 Term.print t2 *)
                  (*   ) mapping; *)
                  if not (TMap.is_empty rep) then
                    let nchildren =
                      TMap.fold (fun t1 t2 acc ->
                          if not (Term.equal t1 ta1) then
                            let s = try TMap.find t1 children
                                    with Not_found -> Term.Set.empty
                            in
                            let s' = Term.Set.add t2 s in
                            TMap.add t1 s' acc
                          else acc
                        ) mapping children in
                    HT.replace hahtbl ta1 (SAtom.add a atoms, nchildren)
                  (* else Format.eprintf "Nothing to do@."; *)
                  (* Format.eprintf "<<<<<<<@." *)

              | _ -> ()
          ) atoms_cand
      in
      let procs = List.rev (List.tl (List.rev env.all_procs)) in
      let ls = alpha_renamings env procs s in
      TimerICands.start ();
      let interpol =
        interpolate_cands &&
          SAtom.for_all (
              function
              | Atom.Comp (_, (Eq | Neq), t) ->
                  Smt.Type.is_constructor (Term.type_of t)
              | _ -> false
            ) (Node.litterals s) in
      TimerICands.pause ();
      List.iter (fun {st} ->
          if not
               (List.for_all
                  (fun (comp, node, sigma) ->
                    if interpol then
                      begin
                        TimerICands.start ();
                        fill_hahtbl st comp sigma;
                        TimerICands.pause ();
                      end;
                    check_cand env st comp) ls) then
            raise (EBad (st, env));
        ) env.states;
      (* Format.eprintf "Create ns@."; *)
      let ns =
        if interpol then
          HT.fold (fun t (atoms, children) acc ->
              (* 'map' contains a mapping from variables/arrays to their values in
               * the reachable states *)
              (* Format.eprintf "Term Rep : %a@\nSAtom : %a@." *)
              (*   Term.print t SAtom.print atoms; *)
              let sa' =
                TMap.fold (fun term values acc ->
                        (* Format.eprintf "Term child : %a@\n\t@[<hov>%a@]@." *)
                        (*   Term.print term Term.print_set values; *)
                    let nb_constr =
                      try
                        match term with
                          | Elem (h, _) | Access (h, _) ->
                              let _, ret = Smt.Symbol.type_of h in
                              let l = Smt.Type.constructors ret in
                              List.length l
                          | _ -> -1
                      with Not_found -> -1
                    in
                    let new_atoms =
                      if Term.Set.cardinal values = 1 && nb_constr > 2 then
                        SAtom.singleton
                          (Atom.Comp (term, Neq, Term.Set.choose values))
                      else
                        Node.find_atoms s term
                    in
                    SAtom.union new_atoms acc
                  ) children SAtom.empty in
              let sa' = SAtom.union atoms sa' in
              let cube = Cube.create (Node.variables s) sa' in
              let n = Node.create cube ~kind:Approx in
              n :: acc
            ) hahtbl []
        else [s] in
      match ns with
        | [] -> [s]
        | _ -> ns
    with
      | Not_found -> raise ECantSay
  else [s]

let check_state_according_to_bwd state env bwd =
  try
    let procs = List.rev (List.tl (List.rev env.all_procs)) in
    let ls = alpha_renamings env procs state in
    List.iter (fun st ->
        if not (List.for_all (fun (c, _, _) -> check_cand env st c) ls) then
          raise (EBad (st, env));
      ) bwd;
  with 
    | Not_found -> raise ECantSay

let print_iopi_list =
  List.iter (fun (c, n) -> 
      Format.eprintf "@[<v 3>@[---%a@,@]@]@."
        Node.print n
    )

let rec is_sublist l1 l2 =
  match l1, l2 with
    | [], _ -> true
    | _, [] -> false
    | (t1, _) :: tl1, (t2, _) :: tl2 when Hstring.equal t1 t2 -> 
        is_sublist tl1 tl2
    | _, _ :: tl -> is_sublist l1 tl

let longest xs ys = if List.length xs > List.length ys then xs else ys
                                                                      
let post_bfs env (from, st) visited trs q cpt_q depth autom init =
  if not !limit_forward_depth || depth < !forward_depth then
    List.iter (fun st_tr ->
        try
          let sts = st_tr.st_f st in
          List.iter (fun s ->
              if forward_sym then normalize_state env s;
              let from = List.map (fun hl -> 
                             (st_tr.st_name, List.rev st_tr.st_args) :: hl)
                           from in
              let morf = if debug_regexp || copy_regexp 
                         then List.map List.rev from
                         else [] in
              let der = debug_regexp && 
                          List.exists (Regexp.Automaton.recognize autom) morf in
              if der then begin
                  Format.eprintf "@{<fg_green>YES !@} %a" pfrom morf;
                  if verbose > 2 then
                    Format.eprintf "%a@." (print_state env) s;
                end;
              try 
                (match HST.find visited s with
                   | Some rs -> rs.from <- List.rev_append from rs.from;
                   | _ -> assert false);
                if der then
                  Format.eprintf " @{<fg_red>Already Visited@}@."
              with Not_found ->
                   if copy_regexp && List.exists (Regexp.Automaton.recognize autom) morf
                   then begin
                       let s' = generalize_state env s st_tr.st_args init in
                       if debug then (
                         Format.eprintf "@{<fg_green>YES !@} %a@." pfrom morf;
                         Format.eprintf "Pre state : %a@." (print_state env) st;
                         Format.eprintf "New state : %a@." (print_state env) s;
                         Format.eprintf "Cop state : %a@." (print_state env) s'
                       );
                       HQueue.add ~cpt_q (depth + 1, {st = s'; from}, s') q
                     end;
                   if der then begin
                       HQueue.add ~cpt_q ~debug:true (depth + 1, {st = s; from}, s) q
                     end else HQueue.add ~cpt_q (depth + 1, {st = s; from}, s) q
            ) sts
        with Not_applicable -> ()) trs

let hstl_to_string hl =
  let hl = List.rev hl in
  let b = Buffer.create 32 in
  List.iter (fun (tn, vars) ->
      Buffer.add_string b (Hstring.view tn);
      Buffer.add_string b "(";
      List.iter (fun v -> Buffer.add_string b (Hstring.view v)) vars;
      Buffer.add_string b ")"
    ) hl;
  Buffer.contents b
                  
let forward_bfs init env l autom =
  maxd := !forward_depth;
  let h_visited = (* HST.create 17 *) env.explicit_states in
  let cpt_f = ref 0 in
  let cpt_r = ref 0 in
  let cpt_q = ref 1 in
  let trs = env.st_trs in
  let to_do = HQueue.create env.table_size in
  List.iter (fun td -> HQueue.add td to_do) l;
  while not (HQueue.is_empty to_do) && 
          (max_forward = -1 || !cpt_f < max_forward) do
    let depth, rs, st = HQueue.take to_do in
    decr cpt_q;
    if not (HST.mem h_visited st) then begin
        HST.add h_visited st (Some rs);
        post_bfs env (rs.from, st) h_visited trs to_do cpt_q depth autom init ;
        incr cpt_f;
        if debug && verbose > 1 then
          eprintf "%d : %a\n@." !cpt_f
            SAtom.print (state_to_cube env st);
        if not quiet && !cpt_f mod 1000 = 0 then
          eprintf "%d (%d)@." !cpt_f !cpt_q;
        incr cpt_r;
        env.states <- rs :: env.states;
        if depth > !maxd then maxd := depth;
        if !limit_forward_depth && depth = !forward_depth then
          env.fringe <- st :: env.fringe;
      end
  done;
  (* if debug && verbose > 3 then *)
  
  HST.iter (fun s rl ->
      match rl with
        | Some rs ->
            let f = List.map List.rev rs.from in
            rs.from <- f;
            env.histories <- List.rev_append f env.histories;
        | _ -> assert false
    ) h_visited;
  env.histories <- List.fast_sort (
                       fun l1 l2 ->
                       compare (List.length l1) (List.length l2)) env.histories;
  if verbose > 0 then Format.eprintf "%a\n------------@." pfrom env.histories
                                     
let get_histories () = List.map (fun env -> env.histories) !global_envs 

let nodes_to_iopi_list env bwd =
  let procs = List.rev (List.tl (List.rev env.all_procs)) in
  List.fold_left (
      fun acc s -> 
      if Node.dim s <= env.model_cardinal then
        List.rev_append (alpha_renamings env procs s) acc
      else acc
    ) [] bwd
                 
let search bwd procs init =
  TimeForward.start ();
  let procs = procs (*@ init.t_glob_proc*) in
  eprintf "Init table@.";
  let env = init_tables procs init in
  eprintf "Init to states@.";
  let st_inits = init_to_states env procs init in
  if debug then 
    List.iter (fun (_, _, st) ->
        eprintf "init : %a\n@." SAtom.print (state_to_cube env st))
      st_inits;
  let bwd = nodes_to_iopi_list env bwd in
  let env = {env with 
              st_trs = transitions_to_func procs env init.t_trans;
              bad_states = bwd;
            } in
  global_envs := env :: !global_envs;
  install_sigint ();
  begin 
    try
      forward_bfs init env st_inits init.t_automaton;
    with Exit -> ()
  end ;
  (* if clusterize then ( *)
  (*   let clu = Kmeans.kmeans ~md:md env.fringe in *)
  (*   if verbose > 0 then  *)
  (*     List.iter (fun (st, _) -> *)
  (*       Format.eprintf "Cluster %a@." (print_state env) st) clu; *)
  (*   let clu = List.map (fun (st, _) -> st) clu *)
  (*   env.states <- List.rev_append clu env.states *)
  (* ); *)
  finalize_search env
                  

let check_first_and_filter_rest = function
  | [] -> []
  | s :: rs ->
      try
        let nl =
          List.fold_left (fun acc c ->
              let cl = one_resist_on_trace_size s c in
              List.rev_append acc cl) [] !global_envs in
        raise (Sustainable (s ,(if interpolate_cands then nl else [s])))
      with
        | ECantSay -> rs
        | EBad (st, env) ->
            List.filter (state_impossible env st) rs
                        


let rec check_remaining_aux cpt progress_inc ls =
  if not quiet && cpt mod progress_inc = 0 then one_step ();
  match check_first_and_filter_rest ls with
    | [] -> []
    | rs -> check_remaining_aux (cpt+1) progress_inc rs

let check_remaining progress_inc ls = check_remaining_aux 0 progress_inc ls

let fast_resist_on_trace ls =
  let progress_inc = (List.length ls) / Pretty.vt_width + 1 in
  if not quiet then eprintf "@{<fg_black_b>@{<i>";
  (* will be forgotten by flushs *)
  TimeCheckCand.start ();
  try
    assert (check_remaining progress_inc ls = []);
    TimeCheckCand.pause ();
    if not quiet then eprintf "@{</i>@}@{<bg_default>@}@{<fg_red>X@}@.";
    []
  with Sustainable (cand, candl) ->
       TimeCheckCand.pause ();
       if not quiet then
         begin
           eprintf "@{</i>@}@{<bg_default>@}@{<fg_green>!@}@.";
           if not (SAtom.equal (Node.litterals cand)
                     (Node.litterals (List.hd candl))) then
             Format.eprintf "Candidate was : %a@\nNew candidates are now\
                             : @[<hov>%a@]@."
               Node.print cand Node.print_list candl;
         end;
       candl



(******************************************************)
(* TODO Extract unsat cores to find minimal candidate *)
(******************************************************)


module SCand =
  Set.Make (struct
      type t = st_req * Atom.t
      let compare (t,_) (t',_) = Pervasives.compare t t'
    end)


let unsat_cand_core env state cand =
  List.fold_left
    (fun uc ((l,_) as la) ->
      if not (check_req env state (neg_req env l)) then
        SCand.add la uc
      else uc)
    SCand.empty cand


(*-------------- interface -------------*)


let init ?(bwd=[]) system =
  set_liberal_gc ();
  List.iter (fun (b, f) ->
      let procs = Variable.give_procs b in
      if not quiet then
        Pretty.print_title std_formatter
          ("STATEFULL ENUMERATIVE FORWARD ["^(string_of_int b)^" procs]\
                                                                [fwd depth : "^(string_of_int f)^"]");
      forward_depth := f;
      limit_forward_depth := !forward_depth <> -1;
      search bwd procs system;
      if not quiet then printf "%a@." Pretty.print_double_line ();
    ) brab_fwd_depth;
  reset_gc_params ()
                  

let first_good_candidate candidates =
  match fast_resist_on_trace candidates with
    | c :: _ -> Some c
    | [] -> None

let mk_env nbprocs sys =
  (* create mappings but don't allocate hashtable *)
  let procs = Variable.give_procs nbprocs in
  let env = init_tables ~alloc:false procs sys in
  global_envs := env :: !global_envs;
  env

let int_of_term env t =
  (* if Term.type_of t == Smt.Type.type_int then *)
  HT.find env.id_terms t

let next_id env = env.pinf_int_abstr + 1

let empty_state = [||]

let new_undef_state env =
  Array.make env.nb_vars (-1)
(* env.states <- st :: env.states; *)
(* eprintf "nb states : %d@." (List.length env.states); *)
(* st *)

(* let register_state env st = env.states <- {st; from=[]} :: env.states *)
(* let register_state env st = env.states <- st :: env.states *)

let size_of_env env = env.table_size

let print_last env =
  match env.states with
    | {st} :: _ -> eprintf "--- @[<hov>%a@]@." SAtom.print (state_to_cube env st)
    | _ -> ()


(*----------------- For FAR ----------------*)

let all_good_candidates candidates = fast_resist_on_trace candidates
                                       
