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
module S = Set.Make(String) 
  (* changer la fonction compare pour avoir dans l'ordre #1<#2<..<#9<#10 etc. *)

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
	eprintf "Unsafe check :@.%a@." Pretty.print_system s

  let invariant = 
      fun s ->
	eprintf "Invariant ?@. %a@." Pretty.print_system s

  let pre = 
    if not debug then fun _ _ -> () else 
      fun tr p ->
	eprintf "\nResult of the pre for transition %s:@.%a@." 
	  tr.tr_name Pretty.print_unsafe p

  let pre_cubes = 
    if not debug then fun _ -> () else 
      fun p ->
	eprintf "Cubes:%a@." Pretty.print_unsafe p

end

module SS = Set.Make
  (struct 
     type t = string * string
    let compare (s1, s2) (t1, t2) = 
      Pervasives.compare (s1, s2) (t1, t2) 
   end)
  
let rec m_number env a s = 
  match a with
    | True | False -> s
    | Comp (Elem x, Eq, Elem y) ->
	begin
	  let s1 = 
	    try let s, _, _ = Hashtbl.find env x in s with Not_found -> Var in
	  let s2 = 
	    try let s, _, _ = Hashtbl.find env y in s with Not_found -> Var in
	  match s1, s2 with
	    | Glob, Constr | Constr, Glob -> SS.add (x,y) s
	    | _ -> s
	end
    | Comp (Access (a, _), _, Elem x) -> 
	let xs = 
	  try let s, _, _ = Hashtbl.find env x in s with Not_found -> Var in
	if xs = Glob || xs = Constr then SS.add (a, x) s else SS.add (a, "") s
    | Comp (_, _, Access (a, _)) -> SS.add (a, "") s
    | Comp _ ->  s
    | Ite (sa, a1, a2) -> 
	SAtom.fold (m_number env) sa (m_number env a1 (m_number env a2 s))

let magic_number s sa = SAtom.fold (m_number s.t_env) sa SS.empty

let print_magic fmt ss = 
  SS.iter (fun (a,b) -> fprintf fmt "(%s,%s) " a b) ss;
  fprintf fmt "@."

(* Simplifcation of atoms in a cube based on the hypothesis that
   indices #i are distinct and the type of elements is an
   enumeration *)

(* simplify comparison atoms, according to the assumption that
   variables are all disctincts *)


let redondant env others = function
  | True -> true
  | Comp (t1, Neq, (Elem x as t2))
  | Comp ((Elem x as t2), Neq, t1) ->
    let s = try let s, _, _ = Hashtbl.find env x in s with Not_found -> Var in
    (match s with
      | Var | Constr ->
	(try 
	   (SAtom.iter (function 
	     | Comp (t1', Eq, t2') 
		 when (t1' = t1 && t2' <> t2) || (t1' <> t1 && t2' = t2) ->
	       raise Exit
	     | _ -> ()) others); false
	 with Exit -> true)
      | _ -> false)
  | _ -> false

let simplify_comp env i op j =  
  let si = try let s, _, _ = Hashtbl.find env i in s with Not_found -> Var in
  let sj = try let s, _, _ = Hashtbl.find env j in s with Not_found -> Var in
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
  let cpt = ref 0 in fun () -> incr cpt; "*"^(string_of_int !cpt)

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
	if List.mem x tr.tr_nondets then Elem (fresh_nondet ())
	else try List.assoc x tr.tr_assigns with Not_found -> Elem x
      in 
      Single t

  | Const i as a -> Single a

  | Arith (x, op1, i1) ->
      begin
	let t = 
	  try List.assoc x tr.tr_assigns with Not_found -> Elem x
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
	if List.mem i tr.tr_nondets then fresh_nondet ()
	else 
	  try (match List.assoc i tr.tr_assigns with
		 | Elem ni -> ni
		 | Const _ | Arith _ | Access _ -> assert false)
	  with Not_found -> i
      in
      try find_update a ni tr.tr_upds
      with Not_found -> 
	let na = 
	  try (match List.assoc a tr.tr_assigns with
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


let assoc_neq t1 l t2 =
  try List.assoc t1 l <> t2 with Not_found -> false

let assoc_eq t1 l t2 =
  try List.assoc t1 l = t2 with Not_found -> false

let inconsistent env sa = 
  let l = SAtom.elements sa in
  let rec check values eqs neqs = function
    | [] -> ()
    | True :: l -> check values eqs neqs l
    | False :: _ -> raise Exit
    | Comp (t1, Eq, (Elem x as t2)) :: l 
    | Comp ((Elem x as t2), Eq, t1) :: l ->
      let s = try let s, _, _ = Hashtbl.find env x in s with Not_found -> Var in
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

let obviously_safe { t_unsafe = _, unsa; t_init = _, inisa; t_env = env } =
  inconsistent env (SAtom.union inisa unsa)

let check_safety s = 
  (*Debug.unsafe s;*)
  try
    if not (obviously_safe s) then
      let f = Prover.unsafe s in
      let gf = { AE.Sat.f = f; age = 0; name = None; mf = false; gf = true} in
      ignore (AE.Sat.unsat AE.Sat.empty gf)
  with 
    | AE.Sat.Sat _ -> raise Unsafe
    | AE.Sat.I_dont_know -> exit 2
    | AE.Sat.Unsat _ -> ()
 
let number_of s = 
  if s.[0] = '#' then 
    int_of_string (String.sub s 1 (String.length s - 1))
  else 1

let add_arg args = function
  | Elem s | Access (_, s) | Arith (s, _, _) ->
      if s.[0] = '#' || s.[0] = '$' then S.add s args else args
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
	 let n = number_of arg in
	 if n = !cpt then (incr cpt; sa)
	 else 
	   let sa =  subst_atoms [arg, "#"^(string_of_int !cpt)] sa in 
	   incr cpt; sa) sa args
  in
  let l = ref [] in
  for n = !cpt - 1 downto 1 do l := ("#"^(string_of_int n)) :: !l  done;
  sa, (!l, "#"^(string_of_int !cpt))

let smt_fixpoint_check f = 
  try
    let gf = { AE.Sat.f = f; age = 0; name = None; mf=false; gf=true} in
    ignore (AE.Sat.unsat AE.Sat.empty gf);
    true
  with 
    | AE.Sat.Sat _ | AE.Sat.I_dont_know -> false
    | AE.Sat.Unsat _ -> true
	
let rec alpha_atoms np = 
  SAtom.fold (fun a -> add (alpha_atom a)) np SAtom.empty
and alpha_atom a = 
  match a with
    | False | True -> a
    | Ite (la, a1, a2) -> 
	Ite(alpha_atoms la, alpha_atom a1, alpha_atom a2)
    | Comp (x, op, y) -> Comp(alpha_var x, op, alpha_var y)
and alpha_var = function
  | Elem s when s.[0] = '#' -> Elem ("$"^(string_of_int (number_of s)))
  | Access (a, s) when s.[0] = '#' ->
      Access (a, "$"^(string_of_int (number_of s)))
  | t -> t


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

let obvious_subst env p np l1 l2 =
  let globv = SAtom.fold (fun a acc -> match a with
    | Comp (Elem i, Eq, Elem j) ->
      let si = 
	try let s, _, _ = Hashtbl.find env i in s with Not_found -> Var in
      let sj = 
	try let s, _, _ = Hashtbl.find env j in s with Not_found -> Var in
      (match si, sj with
	| Glob, Var -> (i, j) :: acc
	| Var, Glob -> (j, i) :: acc
	| _ -> acc)
    | _ -> acc) np [] in
  let obvs = SAtom.fold (fun a acc -> match a with
    | Comp (Elem i, Eq, Elem j) ->
      let si = 
	try let s, _, _ = Hashtbl.find env i in s with Not_found -> Var in
      let sj = 
	try let s, _, _ = Hashtbl.find env j in s with Not_found -> Var in
      (try 
	 (match si, sj with
	   | Glob, Var -> 
	     if List.mem_assoc j acc then acc
	     else (j, List.assoc i globv) :: acc
	   | Var, Glob -> 
	     if List.mem_assoc i acc then acc
	     else (i, List.assoc j globv) :: acc
	   | _ -> acc)
       with Not_found -> acc)
    | _ -> acc) p [] in
  let obvl1, obvl2 = List.split obvs in
  let l1 = List.filter (fun b -> not (List.mem b obvl1)) l1 in
  let l2 = List.filter (fun b -> not (List.mem b obvl2)) l2 in
  obvs, l1, l2


let impossible_access env np a i op j acc =
  SAtom.fold (fun at acc -> match at, op with
    | Comp (Access (a', i'), Eq, Elem j'), Eq when j <> j' && a = a' ->
      let si' = 
	try let s, _, _ = Hashtbl.find env i' in s with Not_found -> Var in
      let sj' = 
	try let s, _, _ = Hashtbl.find env j' in s with Not_found -> Var in
      (match si', sj' with
	| Var ,(Glob | Constr) -> (i, i')::acc
	| _ -> acc)
    | Comp (Access (a', i'), Eq, Elem j'), Neq 
    | Comp (Access (a', i'), Neq, Elem j'), Eq  when j = j' && a = a' ->
      let si' = 
	try let s, _, _ = Hashtbl.find env i' in s with Not_found -> Var in
      let sj' = 
	try let s, _, _ = Hashtbl.find env j' in s with Not_found -> Var in
      (match si', sj' with
	| Var ,(Glob | Constr) -> (i, i')::acc
	| _ -> acc)
    | _ -> acc) np acc
    
let impossible_permutations_atom env np at acc = match at with
  | Comp (Access (a, i), ((Eq | Neq) as op), Elem j) ->
    let si = 
      try let s, _, _ = Hashtbl.find env i in s with Not_found -> Var in
    let sj = 
      try let s, _, _ = Hashtbl.find env j in s with Not_found -> Var in
    (match si, sj with
      | Var, (Glob | Constr) -> impossible_access env np a i op j acc
      | _ -> acc)
  | _ -> acc

let impossible_permutations env p np =
  SAtom.fold (impossible_permutations_atom env np) p []


let relevant_permutations env p np l1 l2 =
  let obvs, l1, l2 = obvious_subst env p np l1 l2 in
  let perm = all_permutations l1 l2 in
  let perm = List.map (List.append obvs) perm in
  let impos = impossible_permutations env p np in
  List.filter (List.for_all (fun s -> not (List.mem s impos))) perm

let possible_imply s np p =
  SS.subset (magic_number s p) (magic_number s np)  

let check_fixpoint s visited np = 
  (* let cpt = ref 0 in *)
  (* let fix = *)
  List.exists
    (fun { t_unsafe = (args, p); t_env = env } ->
       (* incr cpt; *)
       (let f = Prover.fixpoint s args np p in smt_fixpoint_check f )
       ||
	 let p = alpha_atoms p in
	 let args = args_of_atoms p in
	 let nargs = args_of_atoms np in
	 ( List.length args <= List.length nargs &&
	     (* let d = all_permutations args nargs in *)
	     (* eprintf "len:%d@." (List.length d); *)
	     let d = relevant_permutations env p np args nargs in
	     (* eprintf "d2:%d\n@." (List.length d); *)
	     List.exists 
	       (fun ss ->
		  let pp = 
		    List.fold_left 
		      (fun pp (x, y) -> subst_atoms [x, y] pp) p ss in
		  SAtom.subset pp np 
		  ||
		    ((possible_imply s np pp) && 
		      (not (inconsistent s.t_env pp)) &&
		       let f = Prover.extended_fixpoint s nargs ss np pp in
		       let res = smt_fixpoint_check f in
		       (* if not res then *)
		       (*   eprintf "not a fixpoint : %a -> %a\n@." *)
		       (*     Pretty.print_unsafe np Pretty.print_unsafe pp; *)
		       res
		    )  ) d)
    ) visited
  (* in *)
  (* if fix then eprintf "\t\t\t\tFixpoint after %d checks / %d@." *)
  (*   !cpt (List.length visited); *)
  (* fix *)

let is_fixpoint s nodes np = 
  List.exists (fun { t_unsafe = (_, p) } -> SAtom.subset p np) nodes
  ||
    let mn = magic_number s np in
    let nodes = 
      List.filter 
	(fun { t_unsafe = (_, p) } -> 
	   let mp = (magic_number s p) in
	   SS.subset mp mn 
	) nodes
    in
    check_fixpoint s nodes np


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

(* Postponed Formulas*)

let has_args_term args = function
  | Elem x | Access (_, x) | Arith (x, _, _) -> List.mem x args
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

let fixpoint ~invariants ~visited ({ t_unsafe = (_,np); t_env = env } as s) = 
  SAtom.mem False np
  || inconsistent env np
  || is_fixpoint s invariants np 
  || is_fixpoint s visited np

let make_cubes (ls, post) (args, rargs) 
    ({ t_unsafe = (_, p); t_env=env } as s) tr np = 
  (* let ureq = uguard rargs tr.tr_ureq in *)
  let cube acc sigma = 
    (* let ureq = subst_atoms sigma ureq in *)
    let lnp = simplify_atoms env (subst_atoms sigma np) in
    List.fold_left
      (fun (ls, post) np ->
	 let np, (nargs, _) = proper_cube np in
	 let ureq = uguard nargs tr.tr_ureq in
	 let np = SAtom.union ureq np in 
	 (* let nargs = args_of_atoms np in *)
	 if debug && !verbose > 0 then Debug.pre_cubes np;
	 if inconsistent s.t_env np then (ls, post) 
	 else if not (SAtom.is_empty ureq) || postpone args p np then 
	   ls, { s with t_unsafe = nargs, np }::post
	 else { s with t_unsafe = nargs, np } :: ls, post ) acc lnp
  in
  if List.length tr.tr_args > List.length rargs then (ls, post)
  else
    let d = all_permutations tr.tr_args rargs in
    List.fold_left cube (ls, post) d

let fresh_args ({ tr_args = args; tr_upds = upds} as tr) = 
  if args = [] then tr
  else
    let cpt = ref 0 in
    let sigma = 
      List.map (fun x -> incr cpt; x, "?"^(string_of_int !cpt)) args 
    in
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

let pre_system ({ t_unsafe = _, u; t_trans = trs} as s) = 
  Debug.unsafe s;
  let ls, post = 
    List.fold_left
    (fun acc tr -> 
       let s = { s with t_from = (tr.tr_name, snd s.t_unsafe)::s.t_from } in
       let tr, pre_u, info_args = pre tr u in
       make_cubes acc info_args s tr pre_u) 
    ([], []) 
    trs 
  in
  Debug.fixpoint ls; ls, post

(* Renames the parameters of the initial unsafe formula *)

let init_atoms args sa = 
  let cpt = ref 0 in
  let sigma = List.map (fun z -> incr cpt; z, "#"^(string_of_int !cpt)) args in
  let sa = List.fold_left (fun sa (i, z) -> subst_atoms [i, z] sa) sa sigma in
  let args = List.map snd sigma in
  args, sa

let init_parameters ({t_unsafe = (args, sa); t_invs = invs } as s) = 
  let args, sa = init_atoms args sa in
  let invs = List.map (fun (argsi, sai) -> init_atoms argsi sai) invs in
  { s with t_unsafe = (args, sa); t_invs = invs }


(* Invariant generation stuff... *)

let same_number env z = function 
  | Const _ -> true
  | Elem s | Access (_, s) | Arith (s, _, _) -> 
      s = z || 
  let v = try let v, _, _ = Hashtbl.find env s in v with Not_found -> Var in
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
       else { s with t_unsafe = [z],sa'} :: l)
    [] args

let impossible_inv { t_unsafe = (_, p) } not_invs =
  List.exists (fun { t_unsafe = (_, ni) } -> SAtom.subset p ni) not_invs
  

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


(* ----------------- Search strategy selection -------------------*)

module T = struct
  type t = t_system

  let invariants s = List.map (fun i -> { s with t_unsafe = i }) s.t_invs
  let size s = List.length (fst s.t_unsafe)
  let maxrounds = 100
  let gen_inv = gen_inv

  let fixpoint = fixpoint
  let safety = check_safety
  let pre = pre_system
  let print = Pretty.print_system
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
  let s = init_parameters s in
  search ~invariants:(T.invariants s) ~visited:[] s
