(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon, Universite Paris-Sud 11              *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

open Format
open Options
open Ast
open Atom


module AE = AltErgo
module S = Set.Make(Hstring) 
let hempty = Hstring.make ""

  (* changer la fonction compare pour avoir dans l'ordre #1<#2<..<#9<#10 etc. *)

module TimeFix = Search.TimeFix

module TimeRP = Search.TimeRP

module TimePre = Search.TimePre

module TimeSort = Search.TimeSort

exception Unsafe

module Debug = struct

  let fixpoint = 
    if not debug then fun _ -> () else 
      fun ls ->
	eprintf "\nAfter simplification, subsumption and fixpoint check : @.";
	match ls with
	  | [] -> eprintf "No new branches@."
	  | _ -> 
	      List.iter (eprintf "@.New branch : %a@." Pretty.print_system) ls

  let unsafe = 
    if not debug then fun _ -> () else 
      fun s ->
	eprintf "    %a@." Pretty.print_unsafe s

  let invariant = 
      fun s ->
	eprintf "Invariant ?@. %a@." Pretty.print_cube s

  let pre = 
    if not debug then fun _ _ -> () else 
      fun tr p ->
	eprintf "\nResult of the pre for transition %s:@.%a@." 
	  (Hstring.view tr.tr_name) Pretty.print_cube p

  let pre_cubes = 
    if not debug then fun _ -> () else 
      fun p ->
	eprintf "Cubes:%a@." Pretty.print_cube p

end

module SS = Set.Make
  (struct 
     type t = Hstring.t * Hstring.t
    let compare (s1, s2) (t1, t2) = 
      let c = Hstring.compare s1 t1 in
      if c <> 0 then c
      else Hstring.compare s2 t2
   end)
  
let rec m_number env a s = 
  match a with
    | True | False -> s
    | Comp (Elem x, Eq, Elem y) ->
	begin
	  let s1 = sort_of env x in
	  let s2 = sort_of env y in
	  match s1, s2 with
	    | Glob, Constr | Constr, Glob -> SS.add (x,y) s
	    | _ -> s
	end
    | Comp (Access (a, _), _, Elem x) -> 
	let xs = sort_of env x in
	if xs = Glob || xs = Constr then
	  SS.add (a, x) s 
	else SS.add (a, hempty) s
    | Comp (_, _, Access (a, _)) -> SS.add (a, hempty) s
    | Comp _ ->  s
    | Ite (sa, a1, a2) -> 
	SAtom.fold (m_number env) sa (m_number env a1 (m_number env a2 s))

let magic_number env sa = SAtom.fold (m_number env) sa SS.empty

let magic_number_arr env aa = 
  Array.fold_left 
    (fun s a -> m_number env a s) 
    SS.empty aa

let print_magic fmt ss = 
  SS.iter (fun (a,b) -> 
    fprintf fmt "(%s,%s) " (Hstring.view a) (Hstring.view b)) ss;
  fprintf fmt "@."


let apply_subst p ss = subst_atoms ss p

let memo_apply_subst =
  let cache = Hashtbl.create 17 in
  fun p ss ->
    let k = p,ss in
    try Hashtbl.find cache k
    with Not_found ->
      let v = apply_subst p ss in
      Hashtbl.add cache k v;
      v



(* Simplifcation of atoms in a cube based on the hypothesis that
   indices #i are distinct and the type of elements is an
   enumeration *)

(* simplify comparison atoms, according to the assumption that
   variables are all disctincts *)


let redondant env others = function
  | True -> true
  | Comp (t1, Neq, (Elem x as t2))
  | Comp ((Elem x as t2), Neq, t1) ->
    let s = sort_of env x in
    (match s with
      | Var | Constr ->
	(try 
	   (SAtom.iter (function 
	     | Comp (t1', Eq, t2') 
		 when (t1' = t1 && t2' <> t2)  ->
	       raise Exit
	     | _ -> ()) others); false
	 with Exit -> true)
      | _ -> false)
  | _ -> false

let simplify_comp env i op j =  
  let si = sort_of env i in
  let sj = sort_of env j in
  match op, (si, sj) with
    | Eq, (Var, Var | Constr, Constr) -> if i=j then True else False
    | Neq, (Var, Var | Constr, Constr) -> if i<>j then True else False
    | Le, _ when i = j -> True
    | Lt, _ when i=j -> False
    | _ -> Comp (Elem i, op, Elem j)

let rec simplification np env a =
  if redondant env (SAtom.remove a np) a then True
  else match a with
    | True | False -> a 
    | Comp (Elem i, op , Elem j) -> simplify_comp env i op j
    | Comp (Arith (i, opai, xi), op, (Arith (j, opaj, xj)))
      when opai = opaj && xi = xj -> simplify_comp env i op j
    | Comp (x, Eq, y) when compare_term x y = 0 -> True
    | Comp _ -> a
    | Ite (sa, a1, a2) -> 
	let sa = 
	  SAtom.fold 
	    (fun a -> add (simplification np env a)) sa SAtom.empty
	in
	let a1 = simplification np env a1 in
	let a2 = simplification np env a2 in
	if SAtom.is_empty sa || SAtom.subset sa np then a1
	else if SAtom.mem False sa then a2
	else Ite(sa, a1, a2)
	  
(* Pre-image of an atom w.r.t a transition, simply represented here by
   a function tau *)

let rec pre_atom tau a = 
  match a with
    | True | False -> a
    | Comp (x, op, y) -> tau x op y
    | Ite (sa, a1, a2) -> 
	let pre_sa = 
	  SAtom.fold (fun a -> add (pre_atom tau a)) sa SAtom.empty 
	in
	let pre_a1 = pre_atom tau a1 in 
	let pre_a2 = pre_atom tau a2 in 
	Ite(pre_sa, pre_a1, pre_a2)

(* Convert a transition into a function *)

type assign = Single of term | Branch of update

let fresh_nondet = 
  let cpt = ref 0 in fun () -> incr cpt; Hstring.make ("*"^(string_of_int !cpt))

let rec find_update a i = function
  | [] -> raise Not_found
  | { up_arr = a'; up_arg = j; up_swts = ls,t} :: _ when a=a' -> 
      let ls = 
	List.map 
	  (fun (ci, ti) -> subst_atoms [j, i] ci, subst_term [j, i] ti) ls in
      let t = subst_term [j, i] t in
      Branch { up_arr = a'; up_arg = i; up_swts = ls,t}
  | _ :: l -> find_update a i l
      
let make_arith x op1 i1 op2 i2 = 
  match op1, op2 with
    | Plus, Plus -> Arith (x, Plus, i1+i2)
    | Plus, Minus -> Arith (x, Plus, i1 - i2)
    | Minus, Plus -> Arith (x, Plus, i2 - i1)
    | Minus, Minus -> Arith (x, Plus, - i1 -i2)

let find_assign tr = function
  | Elem x -> 
      let t = 
	if Hstring.list_mem x tr.tr_nondets then Elem (fresh_nondet ())
	else try Hstring.list_assoc x tr.tr_assigns with Not_found -> Elem x
      in 
      Single t

  | Const i as a -> Single a

  | Arith (x, op1, i1) ->
      begin
	let t = 
	  try Hstring.list_assoc x tr.tr_assigns with Not_found -> Elem x
	in 
	match t with
	  | Const i2 -> 
	      let c = 
		Const (match op1 with Plus -> i2 + i1 | Minus -> i2 - i1)
	      in
	      Single c
	  | Elem x -> Single (Arith (x, op1, i1))
	  | Arith (y, op2, i2) -> Single (make_arith y op1 i1 op2 i2)
	  | Access _ -> assert false
      end
  | Access (a, i ) -> 
      let ni = 
	if Hstring.list_mem i tr.tr_nondets then fresh_nondet ()
	else 
	  try (match Hstring.list_assoc i tr.tr_assigns with
		 | Elem ni -> ni
		 | Const _ | Arith _ | Access _ -> assert false)
	  with Not_found -> i
      in
      try find_update a ni tr.tr_upds
      with Not_found -> 
	let na = 
	  try (match Hstring.list_assoc a tr.tr_assigns with
		 | Elem na -> na
		 | Const _ | Arith _ | Access _ -> assert false)
	  with Not_found -> a
	in
	Single (Access (na, ni))

let make_tau tr x op y =
  match find_assign tr x, find_assign tr y with
    | Single tx, Single ty -> Comp (tx, op, ty)
    | Single tx, Branch {up_arr=a; up_arg=j; up_swts=(ls, t)} ->
	List.fold_right
	  (fun (ci, ti) f -> Ite(ci, Comp(tx, op, ti), f))
	  ls (Comp(tx, op, t))
    | Branch {up_arr=a; up_arg=j; up_swts=(ls, t)}, Single tx ->
	List.fold_right
	  (fun (ci, ti) f -> Ite(ci, Comp(ti, op, tx), f))
	  ls (Comp(t, op, tx))
    | Branch {up_arr=a1; up_arg=j1; up_swts=(ls1, t1)},
	Branch {up_arr=a2; up_arg=j2; up_swts=(ls2, t2)} ->
	assert false


(* cheap check of inconsitant cube *)

let rec list_assoc_term t = function
  | [] -> raise Not_found
  | (u, v)::l -> if compare_term t u = 0 then v else list_assoc_term t l

let assoc_neq t1 l t2 =
  try list_assoc_term t1 l <> t2 with Not_found -> false

let assoc_eq t1 l t2 =
  try list_assoc_term t1 l = t2 with Not_found -> false

let inconsistent_list env l = 
  let rec check values eqs neqs = function
    | [] -> ()
    | True :: l -> check values eqs neqs l
    | False :: _ -> raise Exit
    | Comp (t1, Eq, (Elem x as t2)) :: l 
    | Comp ((Elem x as t2), Eq, t1) :: l ->
      let s = sort_of env x in
      (match s with
	| Var | Constr ->
	  if assoc_neq t1 values t2 
	    || assoc_eq t1 neqs t2 || assoc_eq t2 neqs t1 
	  then raise Exit
	  else check ((t1, t2)::values) eqs neqs l
	| _ ->
	  if assoc_eq t1 neqs t2 || assoc_eq t2 neqs t1 
	  then raise Exit
	  else check values ((t1, t2)::eqs) neqs l)
    | Comp (t1, Eq, t2) :: l ->
      if assoc_eq t1 neqs t2 || assoc_eq t2 neqs t1 
      then raise Exit
      else check values ((t1, t2)::eqs) neqs l
    | Comp (t1, Neq, t2) :: l ->
      if assoc_eq t1 values t2 || assoc_eq t2 values t1
	|| assoc_eq t1 eqs t2 || assoc_eq t2 eqs t1
      then raise Exit
      else check values eqs ((t1, t2)::(t2, t1)::neqs) l
    | _ :: l -> check values eqs neqs l
  in
  try check [] [] []l; false with Exit -> true


let inconsistent env sa = 
  let l = SAtom.elements sa in
  inconsistent_list env l

let inconsistent_array env a =
  let l = Array.to_list a in
  inconsistent_list env l


let obviously_safe { t_unsafe = _, unsa; t_init = _, inisa; t_env = env } =
  inconsistent_list env 
    (List.rev_append (SAtom.elements inisa) (SAtom.elements unsa))


 
let number_of s = 
  if s.[0] = '#' then 
    int_of_string (String.sub s 1 (String.length s - 1))
  else 1

let add_arg args = function
  | Elem s | Access (_, s) | Arith (s, _, _) ->
      let s' = Hstring.view s in
      if s'.[0] = '#' || s'.[0] = '$' then S.add s args else args
  | Const _ -> args

let args_of_atoms sa = 
  let rec args_rec sa args = 
    SAtom.fold 
      (fun a args -> 
	 match a with 
	   | True | False -> args
	   | Comp (x, _, y) -> add_arg (add_arg args x) y
	   | Ite (sa, a1, a2) -> 
	       args_rec (SAtom.add a1 (SAtom.add a2 sa)) args) 
      sa args
  in 
  S.elements (args_rec sa S.empty)

(* Good renaming of a cube's variables *)

let proper_cube sa = 
  let args = args_of_atoms sa in
  let cpt = ref 1 in
  let sa = 
    List.fold_left 
      (fun sa arg -> 
	 let n = number_of (Hstring.view arg) in
	 if n = !cpt then (incr cpt; sa)
	 else 
	   let sa = 
	     subst_atoms [arg, Hstring.make ("#"^(string_of_int !cpt))] sa in 
	   incr cpt; sa)
      sa args
  in
  let l = ref [] in
  for n = !cpt - 1 downto 1 do 
    l := (Hstring.make ("#"^(string_of_int n))) :: !l
  done;
  sa, (!l, Hstring.make ("#"^(string_of_int !cpt)))


(* Find relevant quantifier instantiation for 
   \exists z_1,...,z_n. np => \exists x_1,...,x_m p *)

let rec all_permutations l1 l2 = 
  assert (List.length l1 <= List.length l2);
  match l1 with
    | [] -> [[]]
    | x::l -> cross l [] x l2
and cross l pr x st =
  match st with
    | [] -> []
    | y::p -> 
	let acc = all_permutations l (pr@p) in
	let acc = List.map (fun ds -> (x, y)::ds) acc in
	acc@(cross l (y::pr) x p)


(* Extract global variables/values and accesses from a cube *)

let globals_accesses env np =
  Array.fold_left (fun ((globv, accsv) as acc) a -> match a with
    | Comp (Elem i, Eq, Elem j) ->
      let si = sort_of env i in
      let sj = sort_of env j in
      (match si, sj with
	| Glob, Var -> (i, j) :: globv, accsv
	| Var, Glob -> (j, i) :: globv, accsv
	| _ -> acc)
    | Comp (Access (a, i), ((Eq | Neq) as op), Elem j) ->
      let si = sort_of env i in
      let sj = sort_of env j in
      (match si, sj with
	| Var, (Glob | Constr) -> globv, (a, i, op, j) :: accsv
	| _ -> acc)
    | _ -> acc) ([], []) np

let obvious_permutations env globv p l1 l2 =
  let obvs = Array.fold_left (fun acc a -> match a with
    | Comp (Elem i, Eq, Elem j) ->
      let si = sort_of env i in
      let sj = sort_of env j in
      (try 
	 (match si, sj with
	   | Glob, Var -> 
	     if Hstring.list_mem_assoc j acc then acc
	     else (j, Hstring.list_assoc i globv) :: acc
	   | Var, Glob -> 
	     if Hstring.list_mem_assoc i acc then acc
	     else (i, Hstring.list_assoc j globv) :: acc
	   | _ -> acc)
       with Not_found -> acc)
    | _ -> acc) [] p in
  let obvl1, obvl2 = List.split obvs in
  let l1 = List.filter (fun b -> not (Hstring.list_mem b obvl1)) l1 in
  let l2 = List.filter (fun b -> not (Hstring.list_mem b obvl2)) l2 in
  obvs, l1, l2

let impossible_access env p a i op j acc =
  Array.fold_left (fun acc at -> match at, op with
    | Comp (Access (a', i'), Eq, Elem j'), Eq 
      when not (Hstring.equal j j') && Hstring.equal a a' ->
      let sj' = sort_of env j' in
      (match  sj' with
	| Glob | Constr -> (i', i)::acc
	| _ -> acc)
    | Comp (Access (a', i'), Eq, Elem j'), Neq 
    | Comp (Access (a', i'), Neq, Elem j'), Eq  
      when Hstring.equal j j' && Hstring.equal a a' ->
      let sj' = sort_of env j' in
      (match sj' with
	| Glob | Constr -> (i', i)::acc
	| _ -> acc)
    | _ -> acc) acc p

let impossible_accesses env accesses p =
  List.fold_left 
    (fun acc (a, i, op, j) -> impossible_access env p a i op j acc) 
    [] accesses


(* Relevant permuations for fixpoint check *)

let relevant_permutations env globals accesses p l1 l2 =
  TimeRP.start ();
  let obvs, l1, l2 = obvious_permutations env globals p l1 l2 in
  let perm = all_permutations l1 l2 in
  let impos = impossible_accesses env accesses p in
  let perm = List.filter 
    (List.for_all (fun s -> not (Hstring.list_mem_couple s impos))) perm 
  in
  let r = List.map (List.rev_append obvs) perm in
  TimeRP.pause ();
  r


let possible_imply env anp ap =
  SS.subset (magic_number_arr env ap) (magic_number_arr env anp)  


let closeness env anp ap =
  SS.cardinal (SS.diff (magic_number_arr env anp) (magic_number_arr env ap))

(* Safety check : s /\ init must be inconsistent *)

let check_safety s =
  (*Debug.unsafe s;*)
  try
    if not (obviously_safe s) then
      begin
	Prover.unsafe s;
	raise Unsafe
      end
  with
    | AE.Sat.Sat _ -> raise Unsafe
    | AE.Sat.I_dont_know -> exit 2
    | AE.Sat.Unsat _ -> ()


(* Incremental fixpoint check : s => \/_{p \in nodes} p *)

exception Fixpoint

let check_fixpoint
    ({t_unsafe = (nargs, _(*np*)); t_arru = anp; t_env = env } as s) visited =
 
  Prover.add_goal s;
  let nb_nargs = List.length nargs in
  let globv, accsv = globals_accesses env anp in
  let nodes = List.fold_left
    (fun nodes { t_alpha = args, ap; t_env = env } ->
      if List.length args > nb_nargs then nodes
      else
	let d = relevant_permutations env globv accsv ap args nargs in
	List.fold_left
	  (fun nodes ss ->
	    let pp = ArrayAtom.apply_subst ss ap in
	    if ArrayAtom.subset pp anp then raise Fixpoint
	    (* Heruristic : throw away nodes too much different *)
	    (* else if ArrayAtom.nb_diff pp anp > 2 then nodes *)
	    else if (inconsistent_array env (ArrayAtom.union pp anp)) then
	      nodes
	    else if ArrayAtom.nb_diff pp anp > 1 then pp::nodes
	    else (Prover.add_node env pp; nodes)
	) nodes d
    ) [] visited
  in
  TimeSort.start ();
  let nodes = 
    List.fast_sort
      (fun p1 p2 ->
	 Pervasives.compare 
      	  (ArrayAtom.nb_diff p1 anp)
      	  (ArrayAtom.nb_diff p2 anp)
	(* if c <> 0 then c *)
	(* else  *)
	(*   Pervasives.compare (closeness env anp p1) (closeness env anp p2) *)
      )
      nodes in
  TimeSort.pause ();
  List.iter (fun p -> Prover.add_node env p) nodes

let is_fixpoint ({t_unsafe = _, np; t_arru = npa } as s) nodes = 
  List.exists (fun { t_arru = pa } -> ArrayAtom.subset pa npa) nodes
  ||
    try
      check_fixpoint s nodes;
      false
    with 
      | Fixpoint -> true
      | Exit -> false
      | AE.Sat.Sat _ | AE.Sat.I_dont_know -> false
      | AE.Sat.Unsat _ -> true

let has_deleted_ancestor s =
  List.exists (fun (_, a) -> a.t_deleted) s.t_from

let fixpoint ~invariants ~visited ({ t_unsafe = (_,np); t_env = env } as s) =
  let f = if delete then s.t_deleted || (has_deleted_ancestor s) else false in
  f || 
    (TimeFix.start ();
     let f = is_fixpoint s (List.rev_append invariants visited) in
     TimeFix.pause ();
     f)



let neg x op y = 
  match op with
    | Eq -> Comp (x, Neq, y)
    | Lt -> Comp (y, Le, x)
    | Le -> Comp (y, Lt, x)
    | Neq -> Comp (x, Eq, y)

let simplification_atoms base env sa = 
  try 
    SAtom.fold (fun a base ->
      let na = simplification base env a in
      match na with
	| True -> base
	| False -> raise Exit
	| _ -> add na base)
      sa SAtom.empty
  with Exit -> SAtom.singleton False
      
let rec break a =
  match a with
    | True | False | Comp _ -> [SAtom.singleton a]
    | Ite (sa, a1, a2) -> 
	begin
	  match SAtom.elements sa with
	    | [] -> assert false
	    | [Comp(x, op, y) as z] ->
		let nz = neg x op y in
		let l = break a2 in
		(SAtom.add z (SAtom.singleton a1))::
		  (List.map (SAtom.add nz) l)@(List.map (SAtom.add a1) l)
	    | _ -> [SAtom.singleton a]
	end

let simplify_atoms env np =
  let ites, base = SAtom.partition (function Ite _ -> true | _ -> false) np in
  let base = simplification_atoms SAtom.empty env base in
  let ites = simplification_atoms base env ites in
  SAtom.fold 
    (fun ite cubes ->
       List.fold_left
	 (fun cubes sa -> 
	    List.map (fun cube -> SAtom.union sa cube) cubes)
	 cubes
	 (break ite)
    ) 
    ites
    [base]


(* Postponed Formulas *)

let has_args_term args = function
  | Elem x | Access (_, x) | Arith (x, _, _) -> Hstring.list_mem x args
  | Const _ -> false

let rec has_args args = function
  | True | False -> false
  | Comp (x, _, y) -> has_args_term args x || has_args_term args y
  | Ite (sa, a1, a2) -> 
      SAtom.exists (has_args args) sa || has_args args a1 || has_args args a2

let postpone args p np = 
  let sa1 = SAtom.filter (has_args args) p in
  let sa2 = SAtom.filter (has_args args) np in
  SAtom.equal sa2 sa1

let uguard args = function
  | None -> SAtom.empty
  | Some (j, sa) -> 
      List.fold_left 
	(fun u z -> SAtom.union u (subst_atoms [j, z] sa)) SAtom.empty args

let make_cubes (ls, post) (args, rargs) 
    ({ t_unsafe = (uargs, p); t_env=env } as s) tr np =
  let nb_uargs = List.length uargs in
  let cube acc sigma = 
    let lnp = simplify_atoms env (subst_atoms sigma np) in
    List.fold_left
      (fun (ls, post) np ->
	 let np, (nargs, _) = proper_cube np in
	 let ureq = uguard nargs tr.tr_ureq in
	 let np = SAtom.union ureq np in 
	 if debug && !verbose > 0 then Debug.pre_cubes np;
	 if inconsistent s.t_env np then (ls, post) 
	 else
	   let arr_np = ArrayAtom.of_satom np in
	   let new_s = { s with 
	     t_unsafe = nargs, np;
	     t_arru = arr_np;
	     t_alpha = ArrayAtom.alpha arr_np nargs } in 
	   if (alwayspost && List.length nargs > nb_uargs) ||
	     (not alwayspost && 
		(not (SAtom.is_empty ureq) || postpone args p np)) then
	     ls, new_s::post
	   else new_s :: ls, post ) acc lnp
  in
  if List.length tr.tr_args > List.length rargs then (ls, post)
  else
    let d = all_permutations tr.tr_args rargs in
    List.fold_left cube (ls, post) d


let fresh_var_list =
  [ Hstring.make "?1";
    Hstring.make "?2";
    Hstring.make "?3";
    Hstring.make "?4";
    Hstring.make "?5";
    Hstring.make "?6";
    Hstring.make "?7";
    Hstring.make "?8";
    Hstring.make "?9" ]


let fresh_args ({ tr_args = args; tr_upds = upds} as tr) = 
  if args = [] then tr
  else
    let sigma = build_subst args fresh_var_list in
    { tr with 
	tr_args = List.map snd sigma; 
	tr_reqs = subst_atoms sigma tr.tr_reqs;
	tr_ureq = (match tr.tr_ureq with
	  | None -> None
	  | Some (s, sa) -> Some (s, subst_atoms sigma sa));
	tr_assigns = 
	List.map (fun (x, t) -> x, subst_term sigma t) 
	  tr.tr_assigns;
	tr_upds = 
	List.map 
	  (fun ({up_swts = swts, t} as up) -> 
	     let swts = 
	       List.map 
		 (fun (sa, t) -> subst_atoms sigma sa, subst_term sigma t) swts
	     in
	     { up with up_swts = swts, subst_term sigma t }) 
	  upds}


(* Pre-image of an unsafe formula w.r.t a transition *)

let pre tr unsafe =
  let tr = fresh_args tr in
  let tau = make_tau tr in
  let pre_unsafe = 
    SAtom.union tr.tr_reqs 
      (SAtom.fold (fun a -> add (pre_atom tau a)) unsafe SAtom.empty)
  in
  if debug && !verbose>0 then Debug.pre tr pre_unsafe;
  let pre_unsafe, (args, m) = proper_cube pre_unsafe in
  if tr.tr_args = [] then tr, pre_unsafe, (args, args)
  else tr, pre_unsafe, (args, m::args)


(* Pre-image of a system s : computing the cubes gives a list of new
   systems *)

let pre_system ({ t_unsafe = uargs, u; t_trans = trs} as s) =
  TimePre.start ();
  Debug.unsafe s;
  let ls, post = 
    List.fold_left
    (fun acc tr ->
       let tr, pre_u, info_args = pre tr u in
       let s = 
	 { s with 
	     t_from = (tr.tr_name, s (* snd s.t_unsafe *))::s.t_from;
	     (* t_deleted = false; *)
	 } in
       make_cubes acc info_args s tr pre_u) 
    ([], []) 
    trs 
  in
  TimePre.pause ();
  ls, post


(* Renames the parameters of the initial unsafe formula *)

let init_atoms args sa = 
  let cpt = ref 0 in
  let sigma = 
    List.map 
      (fun z -> incr cpt; z, Hstring.make ("#"^(string_of_int !cpt))) args in
  let sa = apply_subst sa sigma in
  let args = List.map snd sigma in
  args, sa

let init_parameters ({t_unsafe = (args, sa); t_arru = a; t_invs = invs } as s) =
  let args, sa = init_atoms args sa in
  let a = ArrayAtom.of_satom sa in
  let invs = List.map (fun (argsi, sai) -> init_atoms argsi sai) invs in
  { s with t_unsafe = (args, sa); t_arru = a; 
    t_alpha = ArrayAtom.alpha a args; t_invs = invs }


(* Invariant generation stuff... *)

let same_number env z = function 
  | Const _ -> true
  | Elem s | Access (_, s) | Arith (s, _, _) -> 
      s = z || 
  let v = sort_of env s in
  (* v = Glob || *) v = Constr

let rec contains_only env z = function
  | True | False -> true
  | Comp (i, _ , j) -> same_number env z i && same_number env z j
  | Ite (sa, a1, a2) -> 
      contains_only env z a1 && contains_only env z a2 
      && SAtom.for_all (contains_only env z) sa

let partition ({ t_unsafe = (args, sa) } as s) = 
  List.fold_left 
    (fun l z -> 
       let sa', _ = SAtom.partition (contains_only s.t_env z) sa in
       if SAtom.cardinal sa' < 2 then l 
       else 
	 let ar' = ArrayAtom.of_satom sa' in
	 { s with
	   t_unsafe = [z], sa';
	   t_arru = ar';
	   t_alpha = ArrayAtom.alpha ar' [z];
	 } :: l)
    [] args

let impossible_inv { t_arru = p } not_invs =
  List.exists (fun { t_arru = ni } -> ArrayAtom.subset p ni) not_invs
  

let gen_inv search ~invariants not_invs s = 
  List.fold_left 
    (fun (invs, not_invs) p -> 
       try
	 let invariants = invs@invariants in
	 (* if fixpoint ~invariants:invariants ~visited:[] p then invs  *)
	 (* else *)
	 if impossible_inv p not_invs then invs, not_invs
	 else begin  
	   search ~invariants:invariants ~visited:[] p; 
	   eprintf "Good! We found an invariant :-) \n %a @." 
	     Pretty.print_system p;
	   p::invs, not_invs
	 end
       with | Unsafe | Search.ReachBound -> invs, p::not_invs) 
    ([], not_invs) (partition s)


(* node deletion : experimental *)

let delete_nodes s nodes = 
  nodes := List.filter
  (fun n -> 
     if (not n.t_deleted) && 
       not (List.mem n (List.map snd s.t_from)) &&
       ArrayAtom.subset s.t_arru n.t_arru then 
       begin
	 (* eprintf "deleted node@."; *)
	 n.t_deleted <- true;
	 false
       end
     else true)
  !nodes


(* ----------------- Search strategy selection -------------------*)

module T = struct
  type t = t_system

  let invariants s = 
    List.map (fun ((a,u) as i) -> 
      let ar = ArrayAtom.of_satom u in
      { s with 
	t_unsafe = i; 
	t_arru = ar;
	t_alpha = ArrayAtom.alpha ar a
      }) s.t_invs
  let size s = List.length (fst s.t_unsafe)
  let maxrounds = maxrounds
  let maxnodes = maxnodes
  let gen_inv = gen_inv

  let delete_nodes = delete_nodes

  let fixpoint = fixpoint
  let safety = check_safety
  let pre = pre_system
  let print = Pretty.print_node
  let sort = List.stable_sort (fun {t_unsafe=args1,_} {t_unsafe=args2,_} ->
    Pervasives.compare (List.length args1) (List.length args2))
end

module StratDFS = Search.DFS(T)
module StratDFSL = Search.DFSL(T)
module StratDFSH = Search.DFSH(T)
module StratBFS = Search.BFS(T)
module StratDFSHL = Search.DFSHL(T)

let search = 
  match !mode with
    | Dfs -> StratDFS.search
    | DfsL -> StratDFSL.search
    | DfsH -> StratDFSH.search
    | Bfs -> StratBFS.search
    | DfsHL -> StratDFSHL.search

let system s =
  Hstring.TimeHS.start ();
  let s = init_parameters s in
  Hstring.TimeHS.pause ();

  search ~invariants:(T.invariants s) ~visited:[] s
