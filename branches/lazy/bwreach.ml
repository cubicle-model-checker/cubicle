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

open Format
open Options
open Ast
open Atom

exception BUnsafe of t_system

module H = Hstring
module S = Set.Make(H) 
let hempty = H.make ""

  (* changer la fonction compare pour avoir dans l'ordre #1<#2<..<#9<#10 etc. *)

module TimeFix = Search.TimeFix

module TimeRP = Search.TimeRP

module TimePre = Search.TimePre

module TimeSort = Search.TimeSort

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
	eprintf "\nResult of the pre for transition %s (%a):@.%a@."
	  (H.view tr.tr_name)
	  Pretty.print_args tr.tr_args
	  Pretty.print_cube p

  let pre_cubes = 
    if not debug then fun _ _ -> () else 
      fun p args ->
	eprintf "Cubes (%a) :%a@." Pretty.print_args args Pretty.print_cube p

end

module SS = Set.Make
  (struct 
     type t = H.t * H.t
    let compare (s1, s2) (t1, t2) = 
      let c = H.compare s1 t1 in
      if c <> 0 then c
      else H.compare s2 t2
   end)
  
let rec m_number a s = 
  match a with
    | True | False -> s
    | Comp (Elem (x, Glob), Eq, Elem (y, Constr)) 
    | Comp (Elem (x, Constr), Eq, Elem (y, Glob)) -> SS.add (x,y) s
    | Comp (Access (a, _), _, Elem (x, xs)) -> 
	if xs = Glob || xs = Constr then
	  SS.add (a, x) s 
	else SS.add (a, hempty) s
    | Comp (_, _, Access (a, _)) -> SS.add (a, hempty) s
    | Comp _ ->  s
    | Ite (sa, a1, a2) -> 
	SAtom.fold m_number sa (m_number a1 (m_number a2 s))

let magic_number sa = SAtom.fold m_number sa SS.empty

let magic_number_arr aa = 
  Array.fold_left 
    (fun s a -> m_number a s) 
    SS.empty aa

let print_magic fmt ss = 
  SS.iter (fun (a,b) -> 
    fprintf fmt "(%s,%s) " (H.view a) (H.view b)) ss;
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


  
(*****************************************************************)
(* Simplifcation of atoms in a cube based on the hypothesis that *)
(* indices #i are distinct and the type of elements is an	 *)
(* enumeration							 *)
(* 								 *)
(* simplify comparison atoms, according to the assumption that	 *)
(* variables are all disctincts					 *)
(*****************************************************************)

let num_of_const = function
  | ConstInt n | ConstReal n -> n
  | _ -> assert false

let add_constnum c i num =
  match c, num with
    | ConstInt n, ConstInt m -> 
	ConstInt (Num.add_num (Num.mult_num (Num.Int i) n) m)
    | (ConstInt n | ConstReal n), (ConstInt m | ConstReal m) ->
	ConstReal (Num.add_num (Num.mult_num (Num.Int i) n) m)
    | _ -> assert false

let split_num_consts cs =
  MConst.fold
    (fun c i (cs, num) -> match c, num with
       | ConstName _, _ -> MConst.add c i cs, num
       | _ -> cs, add_constnum c i num)
    cs (MConst.empty, ConstInt (Num.Int 0))

let add_constant c i cs =
  match c with
    | ConstInt _ | ConstReal _ ->
	let cs, num = split_num_consts cs in
	let num = add_constnum c i num in
	if Num.compare_num (num_of_const num) (Num.Int 0) = 0 then cs
	else MConst.add num 1 cs
    | _ ->
	let i' = try MConst.find c cs with Not_found -> 0 in
	let i = i + i' in
	if i = 0 then MConst.remove c cs
	else MConst.add c i cs

let is_int_const = function
  | ConstInt _ -> true
  | ConstReal _ -> false
  | ConstName n -> Hstring.equal (snd (Smt.Typing.find n)) Smt.Typing.type_int

let add_constants cs1 cs2 =
  let m = MConst.fold add_constant cs2 cs1 in
  if MConst.is_empty m then 
    let c0 = 
      if is_int_const (fst (MConst.choose cs1)) then 
	ConstInt (Num.Int 0) 
      else ConstReal (Num.Int 0)
    in
    MConst.add c0 1 m
  else m

let mult_const a =
  MConst.map (fun i -> i * a)

let redondant_or_false others a = match a with
  | True -> True
  | Comp (t1, Neq, (Elem (x, (Var | Constr)) as t2))
  | Comp ((Elem (x, (Var | Constr)) as t2), Neq, t1) ->
      (try 
	 (SAtom.iter (function 
	   | Comp (t1', Eq, (Elem (x', (Var | Constr)) as t2'))
	   | Comp ((Elem (x', (Var | Constr)) as t2'), Eq, t1') 
	     when (compare_term t1' t1 = 0 && compare_term t2' t2 = 0) ->
	     raise Exit
	   | Comp (t1', Eq, (Elem (x', (Var | Constr)) as t2'))
	   | Comp ((Elem (x', (Var | Constr)) as t2'), Eq, t1') 
	     when (compare_term t1' t1 = 0 && compare_term t2' t2 <> 0) ->
	     raise Not_found
	   | _ -> ()) others);
	 a
       with Not_found -> True | Exit -> False)
  | Comp (t1, Eq, (Elem (x, (Var | Constr)) as t2))
  | Comp ((Elem (x, (Var | Constr)) as t2), Eq, t1) ->
      (try 
	 (SAtom.iter (function
	   | Comp (t1', Neq, (Elem (x', (Var | Constr)) as t2'))
	   | Comp ((Elem (x', (Var | Constr)) as t2'), Neq, t1') 
	     when (compare_term t1' t1 = 0 && compare_term t2' t2 = 0) ->
	     raise Exit
	   | Comp (t1', Eq, (Elem (x', (Var | Constr)) as t2'))
	   | Comp ((Elem (x', (Var | Constr)) as t2'), Eq, t1') 
	     when (compare_term t1' t1 = 0 && compare_term t2' t2 <> 0) ->
	     raise Exit
	   | _ -> ()) others); a
       with Not_found -> True | Exit -> False)
  | Comp (t1, Neq, t2) ->
      (try 
	 (SAtom.iter (function 
	   | Comp (t1', Eq, t2') 
	       when (compare_term t1' t1 = 0 && compare_term t2' t2 = 0) 
		 || (compare_term t1' t2 = 0 && compare_term t2' t1 = 0) ->
	     raise Exit
	   | _ -> ()) others); a
       with Exit -> False)
  | Comp (t1, Eq, t2) ->
      (try 
	 (SAtom.iter (function 
	   | Comp (t1', Neq, t2') 
	       when (compare_term t1' t1 = 0 && compare_term t2' t2 = 0) 
		 || (compare_term t1' t2 = 0 && compare_term t2' t1 = 0)  ->
	     raise Exit
	   | _ -> ()) others); a
       with Exit -> False)
  | _ -> a

let simplify_comp i si op j sj =  
  match op, (si, sj) with
    | Eq, _ when H.equal i j -> True
    | Neq, _ when H.equal i j -> False
    | Eq, (Var, Var | Constr, Constr) -> 
	if H.equal i j then True else False
    | Neq, (Var, Var | Constr, Constr) -> 
	if not (H.equal i j) then True else False
    | Le, _ when H.equal i j -> True
    | Lt, _ when H.equal i j -> False
    | _ -> Comp (Elem (i, si), op, Elem (j, sj))

let rec simplification np a =
  let a = redondant_or_false (SAtom.remove a np) a in
  match a with
    | True | False -> a 
    | Comp (Elem (i, si), op , Elem (j, sj)) -> simplify_comp i si op j sj
    | Comp (Arith (i, si, csi), op, (Arith (j, sj, csj)))
      when compare_constants csi csj = 0 -> simplify_comp i si op j sj
    (* | Comp (Const cx, op, Arith (y, sy, cy)) -> *)
    (* 	Comp (Const (add_constants (mult_const (-1) cx) cx), op, *)
    (* 	      Arith (y, sy , (add_constants (mult_const (-1) cx) cy))) *)
    (* | Comp ( Arith (x, sx, cx), op, Const cy) -> *)
    (* 	Comp (Arith (x, sx , (add_constants (mult_const (-1) cy) cx)), op, *)
    (* 	      Const (add_constants (mult_const (-1) cy) cy)) *)
    | Comp (Elem (x, sx), op, Arith (y, sy, cy)) when Hstring.equal x y ->
        let cx = add_constants (mult_const (-1) cy) cy in
	let c, i = MConst.choose cy in
	let my = MConst.remove c cy in
	let cy = 
	  if MConst.is_empty my then MConst.add c (i/(abs i)) my else cy in 
        Comp (Const cx, op, Const cy)
    | Comp (Arith (y, sy, cy), op, Elem (x, sx)) when Hstring.equal x y ->
        let cx = add_constants (mult_const (-1) cy) cy in
	let c, i = MConst.choose cy in
	let my = MConst.remove c cy in
	let cy = 
	  if MConst.is_empty my then MConst.add c (i/(abs i)) my else cy in 
        Comp (Const cy, op, Const cx)
    | Comp (Const _ as c, Eq, y) -> Comp (y, Eq, c)
    | Comp (x, Eq, y) when compare_term x y = 0 -> True
    | Comp _ -> a
    | Ite (sa, a1, a2) -> 
	let sa = 
	  SAtom.fold 
	    (fun a -> add (simplification np a)) sa SAtom.empty
	in
	let a1 = simplification np a1 in
	let a2 = simplification np a2 in
	if SAtom.is_empty sa || SAtom.subset sa np then a1
	else if SAtom.mem False sa then a2
	else Ite(sa, a1, a2)
	  
(***********************************************************************)
(* Pre-image of an atom w.r.t a transition, simply represented here by *)
(* a function tau						       *)
(***********************************************************************)

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

(****************************************)
(* Convert a transition into a function *)
(****************************************)

type assign = Single of term | Branch of update

let fresh_nondet = 
  let cpt = ref 0 in 
  fun (args, ret) -> 
    incr cpt; 
    let s = H.make ("*"^(string_of_int !cpt)) in
    Smt.Typing.declare_name s args ret;
    s

let rec find_update a i = function
  | [] -> raise Not_found
  | { up_arr = a'; up_arg = j; up_swts = ls} :: _ when a=a' -> 
      let ls = 
	List.map 
	  (fun (ci, ti) -> subst_atoms [j, i] ci, subst_term [j, i] ti) ls in
      Branch { up_arr = a'; up_arg = i; up_swts = ls}
  | _ :: l -> find_update a i l


let find_assign tr = function
  | Elem (x, sx) -> 
      let t = 
	if H.list_mem x tr.tr_nondets then 
	  Elem (fresh_nondet (Smt.Typing.find x), sx)
	else 
	  try H.list_assoc x tr.tr_assigns with Not_found -> Elem (x, sx)
      in 
      Single t

  | Const i as a -> Single a

  | Arith (x, sx, cs1) ->
      begin
	let t = 
	  try H.list_assoc x tr.tr_assigns with Not_found -> Elem (x, sx)
	in 
	match t with
	  | Const cs2 -> 
	      let c = 
		Const (add_constants cs1 cs2)
	      in
	      Single c
	  | Elem (x, sx) -> Single (Arith (x, sx, cs1))
	  | Arith (y, sy, cs2) -> Single (Arith (y, sy, add_constants cs1 cs2))
	  | Access _ -> assert false
      end
  | Access (a, i ) -> 
      let ni = 
	if H.list_mem i tr.tr_nondets then 
	  fresh_nondet (Smt.Typing.find i)
	else 
	  try (match H.list_assoc i tr.tr_assigns with
		 | Elem (ni, _) -> ni
		 | Const _ | Arith _ | Access _ -> assert false)
	  with Not_found -> i
      in
      try find_update a ni tr.tr_upds
      with Not_found -> 
	let na = 
	  try (match H.list_assoc a tr.tr_assigns with
		 | Elem (na, _) -> na
		 | Const _ | Arith _ | Access _ -> assert false)
	  with Not_found -> a
	in
	Single (Access (na, ni))

let make_tau tr x op y =
  match find_assign tr x, find_assign tr y with
    | Single tx, Single ty -> Comp (tx, op, ty)
    | Single tx, Branch {up_arr=a; up_arg=j; up_swts=ls} ->
	List.fold_right
	  (fun (ci, ti) f -> Ite(ci, Comp(tx, op, ti), f))
	  ls True
    | Branch {up_arr=a; up_arg=j; up_swts=ls}, Single tx ->
	List.fold_right
	  (fun (ci, ti) f -> Ite(ci, Comp(ti, op, tx), f))
	  ls True
    | Branch {up_arr=a1; up_arg=j1; up_swts = ls1 },
	Branch {up_arr=a2; up_arg=j2; up_swts= ls2 } ->
	List.fold_right
	  (fun (ci, ti) f -> 
	     List.fold_right 
	       (fun (cj, tj) f ->
		  Ite(SAtom.union ci cj, Comp(ti, op, tj), f)) ls2 f)
	  ls1 True


(***********************************)
(* Cheap check of inconsitant cube *)
(***********************************)

let rec list_assoc_term t = function
  | [] -> raise Not_found
  | (u, v)::l -> if compare_term t u = 0 then v else list_assoc_term t l

let assoc_neq t1 l t2 =
  try compare_term (list_assoc_term t1 l) t2 <> 0 with Not_found -> false

let assoc_eq t1 l t2 =
  try compare_term (list_assoc_term t1 l) t2 = 0 with Not_found -> false

let inconsistent_list l = 
  let rec check values eqs neqs les lts ges gts = function
    | [] -> ()
    | True :: l -> check values eqs neqs les lts ges gts l
    | False :: _ -> raise Exit
    | Comp (t1, Eq, (Elem (x, s) as t2)) :: l 
    | Comp ((Elem (x, s) as t2), Eq, t1) :: l ->
      (match s with
	| Var | Constr ->
	  if assoc_neq t1 values t2 
	    || assoc_eq t1 neqs t2 || assoc_eq t2 neqs t1 
	  then raise Exit
	  else check ((t1, t2)::values) eqs neqs les lts ges gts l
	| _ ->
	  if assoc_eq t1 neqs t2 || assoc_eq t2 neqs t1 
	  then raise Exit
	  else check values ((t1, t2)::eqs) neqs les lts ges gts l)
    | Comp (t1, Eq, t2) :: l ->
      if assoc_eq t1 neqs t2 || assoc_eq t2 neqs t1 
      then raise Exit
      else check values ((t1, t2)::eqs) neqs les lts ges gts l
    | Comp (t1, Neq, t2) :: l ->
      if assoc_eq t1 values t2 || assoc_eq t2 values t1
	|| assoc_eq t1 eqs t2 || assoc_eq t2 eqs t1
      then raise Exit
      else check values eqs ((t1, t2)::(t2, t1)::neqs) les lts ges gts l
    | Comp (t1, Lt, t2) :: l ->
      if assoc_eq t1 values t2 || assoc_eq t2 values t1
	|| assoc_eq t1 eqs t2 || assoc_eq t2 eqs t1
	|| assoc_eq t1 ges t2 || assoc_eq t2 les t1
	|| assoc_eq t1 gts t2 || assoc_eq t2 lts t1
      then raise Exit
      else check values eqs neqs les ((t1, t2)::lts) ges ((t2, t1)::gts) l
    | Comp (t1, Le, t2) :: l ->
      if assoc_eq t1 gts t2 || assoc_eq t2 lts t1
      then raise Exit
      else check values eqs neqs ((t1, t2)::les) lts ((t2, t1)::ges) gts l
    | _ :: l -> check values eqs neqs les lts ges gts l
  in
  try check [] [] [] [] [] [] [] l; false with Exit -> true


let inconsistent_aux ((values, eqs, neqs, les, lts, ges, gts) as acc) = function
    | True  -> acc
    | False -> raise Exit
    | Comp (t1, Eq, (Elem (x, s) as t2)) 
    | Comp ((Elem (x, s) as t2), Eq, t1) ->
      (match s with
	| Var | Constr ->
	  if assoc_neq t1 values t2 
	    || assoc_eq t1 neqs t2 || assoc_eq t2 neqs t1 
	  then raise Exit
	  else ((t1, t2)::values), eqs, neqs, les, lts, ges, gts
	| _ ->
	  if assoc_eq t1 neqs t2 || assoc_eq t2 neqs t1 
	  then raise Exit
	  else values, ((t1, t2)::eqs), neqs, les, lts, ges, gts)
    | Comp (t1, Eq, t2) ->
      if assoc_eq t1 neqs t2 || assoc_eq t2 neqs t1 
      then raise Exit
      else values, ((t1, t2)::eqs), neqs, les, lts, ges, gts
    | Comp (t1, Neq, t2) ->
      if assoc_eq t1 values t2 || assoc_eq t2 values t1
	|| assoc_eq t1 eqs t2 || assoc_eq t2 eqs t1
      then raise Exit
      else values, eqs, ((t1, t2)::(t2, t1)::neqs), les, lts, ges, gts
    | Comp (t1, Lt, t2) ->
      if assoc_eq t1 values t2 || assoc_eq t2 values t1
	|| assoc_eq t1 eqs t2 || assoc_eq t2 eqs t1
	|| assoc_eq t1 ges t2 || assoc_eq t2 les t1
	|| assoc_eq t1 gts t2 || assoc_eq t2 lts t1
      then raise Exit
      else values, eqs, neqs, les, ((t1, t2)::lts), ges, ((t2, t1)::gts)
    | Comp (t1, Le, t2) ->
      if assoc_eq t1 gts t2 || assoc_eq t2 lts t1
      then raise Exit
      else values, eqs, neqs, ((t1, t2)::les), lts, ((t2, t1)::ges), gts
    | _  -> acc

let inconsistent sa = 
  let l = SAtom.elements sa in
  inconsistent_list l

let inconsistent_array a =
  let l = Array.to_list a in
  inconsistent_list l


let inconsistent sa =
  try
    let _ = 
      SAtom.fold (fun a acc -> inconsistent_aux acc a) 
	sa ([], [], [], [], [], [], []) in
    false
  with Exit -> true


let inconsistent_array ar =
  try
    let _ = Array.fold_left inconsistent_aux ([], [], [], [], [], [], []) ar in
    false
  with Exit -> true

let inconsistent_2arrays ar1 ar2 =
  try
    let acc = 
      Array.fold_left inconsistent_aux ([], [], [], [], [], [], []) ar1 in
    let _ = Array.fold_left inconsistent_aux acc ar2 in
    false
  with Exit -> true

(*************************************************)
(* Safety check : s /\ init must be inconsistent *)
(*************************************************)

let obviously_safe 
    { t_unsafe = args, _; t_arru = ua; t_init = iargs, inisa } =
  let init_conj = match iargs with
    | None -> inisa
    | Some a ->
      List.fold_left (fun acc ss ->
	SAtom.union (apply_subst inisa ss) acc)
	SAtom.empty
	(List.map (fun b -> [a, b]) args)
  in 
  inconsistent_list
    (List.rev_append (Array.to_list ua) (SAtom.elements init_conj))

 
let check_safety s =
  (*Debug.unsafe s;*)
  try
    if not (obviously_safe s) then
      begin
	Prover.unsafe s;
	if not quiet then printf "\nUnsafe trace: @[%a@]@." Pretty.print_node s;
	raise (BUnsafe s)
      end
  with
    | Smt.Sat ->
      if not quiet then printf "\nUnsafe trace: @[%a@]@." Pretty.print_node s;
      raise (BUnsafe s)
    | Smt.IDontknow -> exit 2
    | Smt.Unsat _ -> ()



(**********************************************************************)
(* Use unsat cores from fixpoints check to close nodes : experimental *)
(**********************************************************************)

module MArgs = Map.Make (struct 
  type t = H.t list 
  let compare = H.compare_list 
end)

let closed = H.H.create (if simpl_by_uc then 8191 else 0)

let already_closed s tr args =
  let sa = s.t_arru in
  try
    let tr_margs = H.H.find closed tr.tr_name in
    let ls = MArgs.find args tr_margs in
    let rec find = function
      | [] -> None
      | (na, fix) :: r -> 
	if ArrayAtom.subset na sa then Some fix
	else find r
    in find ls
  with Not_found -> None

let suitable_for_closing simpl s (*fix_from tr args*) =
  try
    if Array.length simpl <> 0 then begin
      check_safety {s with t_arru = simpl};
      true
    end
    else false
  with Search.Unsafe -> false
  (* && not ( List.exists (fun (tr', args', f) -> *)
  (*   H.equal tr tr' && H.compare_list args args' = 0 && *)
  (*     ArrayAtom.subset simpl f.t_arru) fix_from) *)

let has_alredy_closed_ancestor s =
  let rec has acc = function
    | [] -> false
    | (tr, args, f) :: r ->
      match already_closed f tr args with
	| None -> has (f :: acc) r
	| Some fix -> 
	  not (List.exists (fun f -> ArrayAtom.equal f.t_arru fix.t_arru) acc)
  in
  has [] s.t_from

(* let has_alredy_closed_father s = *)
(*   match s.t_from with  *)
(*     | [] -> false *)
(*     | (tr, args, f)::_ -> already_closed f tr args *)

let add_to_closed s fixa fix =
  match s.t_from with
    | [] -> ()
    | (tr, args, f)::_ ->
      let fa = f.t_arru in
      let sa = s.t_arru in
      let simpl = ArrayAtom.diff fa (ArrayAtom.diff sa fixa) in
      let tr_margs = 
	try H.H.find closed tr.tr_name with Not_found -> MArgs.empty in
      let ls = try MArgs.find args tr_margs with Not_found -> [] in
      H.H.add closed tr.tr_name (MArgs.add args ((simpl, fix) :: ls) tr_margs)

(**********************************************************************)



let number_of s = 
  if s.[0] = '#' then 
    int_of_string (String.sub s 1 (String.length s - 1))
  else 1

let add_arg args = function
  | Elem (s, _) | Access (_, s) | Arith (s, _, _) ->
      let s' = H.view s in
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

(***************************************)
(* Good renaming of a cube's variables *)
(***************************************)

let proper_cube sa = 
  if profiling then TimerApply.start ();
  let args = args_of_atoms sa in
  let cpt = ref 1 in
  let sa = 
    List.fold_left 
      (fun sa arg -> 
	 let n = number_of (H.view arg) in
	 if n = !cpt then (incr cpt; sa)
	 else 
	   let sa = 
	     subst_atoms [arg, H.make ("#"^(string_of_int !cpt))] sa in 
	   incr cpt; sa)
      sa args
  in
  let l = ref [] in
  for n = !cpt - 1 downto 1 do 
    l := (H.make ("#"^(string_of_int n))) :: !l
  done;
  if profiling then TimerApply.pause ();
  sa, (!l, H.make ("#"^(string_of_int !cpt)))


(****************************************************)
(* Find relevant quantifier instantiation for 	    *)
(* \exists z_1,...,z_n. np => \exists x_1,...,x_m p *)
(****************************************************)

let rec all_permutations l1 l2 = 
  (*assert (List.length l1 <= List.length l2);*)
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


(*********************************************)
(* all permutations excepted impossible ones *)
(*********************************************)

let rec all_permutations_impos l1 l2 impos = 
  assert (List.length l1 <= List.length l2);
  match l1 with
    | [] -> [[]]
    | x::l -> cross_impos impos l [] x l2
and cross_impos impos l pr x st =
  match st with
    | [] -> []
    | y::p -> 
	if H.list_mem_couple (x,y) impos then 
	  cross_impos impos l (y::pr) x p
	else
	  let acc = all_permutations_impos l (pr@p) impos in
	  let acc = List.map (fun ds -> (x, y)::ds) acc in
	  acc@(cross_impos impos l (y::pr) x p)


(****************************************************)
(* Improved relevant permutations (still quadratic) *)
(****************************************************)

exception NoPermutations

let find_impossible a1 x1 op c1 i2 a2 n2 impos obvs =
  let i2 = ref i2 in
  while !i2 < n2 do
    let a2i = a2.(!i2) in
    (match a2i, op with
      | Comp (Access (a2, _), _, _), _ when not (H.equal a1 a2) ->
	  i2 := n2

      | Comp (Access (a2, x2), Eq,
	      (Elem (_, Constr) | Elem (_, Glob) | Arith _ as c2)), (Neq | Lt)
	  when compare_term c1 c2 = 0 ->
	  
	  if H.list_mem_couple (x1, x2) obvs then raise NoPermutations;
	  impos := (x1, x2) :: !impos
	    
      | Comp (Access (a2, x2), (Neq | Lt),
	      (Elem (_, Constr) | Elem (_, Glob) | Arith _ as c2)), Eq
	  when compare_term c1 c2 = 0 ->
	  
	  if H.list_mem_couple (x1,x2) obvs then raise NoPermutations;
	  impos := (x1, x2) :: !impos

      | Comp (Access (a2, x2), Eq, (Elem (_, Constr) as c2)), Eq 
	  when compare_term c1 c2 <> 0 ->
	  
	  if H.list_mem_couple (x1,x2) obvs then raise NoPermutations;
	  impos := (x1, x2) :: !impos
	    
      | _ -> ());
    incr i2
  done

let add_obv ((x,y) as p) obvs =
  begin
    try if not (H.equal (H.list_assoc x !obvs) y) then 
	raise NoPermutations
    with Not_found -> ()
  end;
  obvs := p :: !obvs

let obvious_impossible a1 a2 =
  let n1 = Array.length a1 in
  let n2 = Array.length a2 in
  let obvs = ref [] in
  let impos = ref [] in
  let i1 = ref 0 in
  let i2 = ref 0 in
  while !i1 < n1 && !i2 < n2 do
    let a1i = a1.(!i1) in
    let a2i = a2.(!i2) in
    (match a1i, a2i with
       | Comp (Elem (x1, sx1), Eq, Elem (y1, sy1)), 
	 Comp (Elem (x2, sx2), Eq, Elem (y2, sy2)) ->
	   begin
    	     match sx1, sy1, sx2, sy2 with
    	       | Glob, Constr, Glob, Constr 
		   when H.equal x1 x2 && not (H.equal y1 y2) ->
    		   raise NoPermutations
    	       | Glob, Var, Glob, Var when H.equal x1 x2 ->
		   add_obv (y1,y2) obvs
    	       | Glob, Var, Var, Glob when H.equal x1 y2 ->
    		   add_obv (y1,x2) obvs
    	       | Var, Glob, Glob, Var when H.equal y1 x2 ->
    		   add_obv (x1,y2) obvs
    	       | Var, Glob, Var, Glob when H.equal y1 y2 ->
    		   add_obv (x1,x2) obvs
    	       | _ -> ()
    	   end
       | Comp (Elem (x1, sx1), Eq, Elem (y1, sy1)), 
	 Comp (Elem (x2, sx2), (Neq | Lt), Elem (y2, sy2)) ->
    	   begin
	     match sx1, sy1, sx2, sy2 with
    	       | Glob, Constr, Glob, Constr 
		   when H.equal x1 x2 && H.equal y1 y2 ->
    		   raise NoPermutations
    	       | _ -> ()
	   end
       | Comp (Access (a1, x1), op, 
	       (Elem (_, Constr) | Elem (_, Glob) | Arith _ as c1)), 
	 Comp (Access (a, _), _, (Elem (_, Constr) | Elem (_, Glob) | Arith _ ))
    	   when H.equal a1 a ->
	   find_impossible a1 x1 op c1 !i2 a2 n2 impos !obvs
       | _ -> ());
    if Atom.compare a1i a2i <= 0 then incr i1 else incr i2
  done;
  !obvs, !impos

(*******************************************)
(* Relevant permuations for fixpoint check *)
(*******************************************)

let relevant_permutations np p l1 l2 =
  if profiling then TimeRP.start ();
  try
    let obvs, impos = obvious_impossible p np in
    let obvl1, obvl2 = List.split obvs in
    let l1 = List.filter (fun b -> not (H.list_mem b obvl1)) l1 in
    let l2 = List.filter (fun b -> not (H.list_mem b obvl2)) l2 in
    let perm = all_permutations_impos l1 l2 impos in
    let r = List.map (List.rev_append obvs) perm in
    if profiling then TimeRP.pause ();
    r
  with NoPermutations -> if profiling then TimeRP.pause (); []


let possible_imply anp ap =
  SS.subset (magic_number_arr ap) (magic_number_arr anp)  


let closeness anp ap =
  SS.cardinal (SS.diff (magic_number_arr anp) (magic_number_arr ap))

(********************************************************)
(* Incremental fixpoint check : s => \/_{p \in nodes} p *)
(********************************************************)


let extra_args args nargs =
  let rec aux dif args nargs = match args, nargs with
    | [], [] -> dif
    | _::_, [] -> args
    | [], _::_ -> dif
    | a::ra, b::rb -> aux dif ra rb
  in
  aux [] args nargs


exception Fixpoint

let check_fixpoint ({t_unsafe = (nargs, _); t_arru = anp} as s) visited =
  
  Prover.assume_goal s;
  (* let nb_nargs = List.length nargs in *)
  let nodes = List.fold_left
    (fun nodes ({ t_alpha = args, ap; t_unsafe = real_args, _ } as sp)->
      let dif = extra_args real_args nargs in
      (* if List.length args > nb_nargs then nodes *)
      (* else *)
      let nargs = if dif = [] then nargs else nargs@dif in
      let d = relevant_permutations anp ap args nargs in
      List.fold_left
	(fun nodes ss ->
	  let pp = ArrayAtom.apply_subst ss ap in
	  if ArrayAtom.subset pp anp then begin
	    if simpl_by_uc then add_to_closed s pp sp ;
	    raise Fixpoint
	  end
	  (* Heruristic : throw away nodes too much different *)
	  (* else if ArrayAtom.nb_diff pp anp > 2 then nodes *)
	  (* line below useful for arith : ricart *)
	  else if inconsistent_array (ArrayAtom.union pp anp) then nodes
	  else if ArrayAtom.nb_diff pp anp > 1 then pp::nodes
	  else (Prover.assume_node pp; nodes)
	) nodes d
    ) [] visited
  in
  if profiling then TimeSort.start ();
  let nodes = 
    List.fast_sort
      (fun p1 p2 ->
	 Pervasives.compare 
      	   (ArrayAtom.nb_diff p1 anp)
      	   (ArrayAtom.nb_diff p2 anp)
      (* Better sorting but more expensive *)
      (* if c <> 0 then c *)
      (* else  *)
      (*   Pervasives.compare (closeness anp p1) (closeness anp p2) *)
      )
      nodes in
  if profiling then TimeSort.pause ();
  List.iter (fun p -> Prover.assume_node p) nodes
  

let has_deleted_ancestor s =
  let rec has acc = function
    | [] -> false, acc
    | (_, _, a) :: r ->
      if a.t_deleted then true, acc
      else has (a :: acc) r
  in
  let del, children = has [] s.t_from in
  if del then List.iter (fun a -> a.t_deleted <- true) children;
  del
  
let has_deleted_ancestor s =
  List.exists (fun (_, _, a) -> a.t_deleted) s.t_from


let easy_fixpoint ({t_unsafe = _, np; t_arru = npa } as s) nodes =
  (delete && (s.t_deleted || has_deleted_ancestor s))
  ||
    (simpl_by_uc && has_alredy_closed_ancestor s)
  ||
    List.exists (fun ({ t_arru = pa } as sp) -> 
      if ArrayAtom.subset pa npa then begin
	if simpl_by_uc then add_to_closed s pa sp;
	true
      end
      else false
    ) nodes


let hard_fixpoint ({t_unsafe = _, np; t_arru = npa } as s) nodes =
  try
    check_fixpoint s nodes;
    false
  with 
    | Fixpoint -> true
    | Exit -> false
    | Smt.Sat | Smt.IDontknow -> false
    | Smt.Unsat _ -> true
  

let fixpoint ~invariants ~visited ({ t_unsafe = (_,np) } as s) =
  Debug.unsafe s;
  if profiling then TimeFix.start ();
  let nodes = (List.rev_append invariants visited) in
  let f = easy_fixpoint s nodes || hard_fixpoint s nodes in
  if profiling then TimeFix.pause ();
  f

let neg = function
  | True -> False
  | False -> True
  | Comp (x, Eq, y) -> Comp (x, Neq, y)
  | Comp (x, Lt, y) -> Comp (y, Le, x)
  | Comp (x, Le, y) -> Comp (y, Lt, x)
  | Comp (x, Neq, y) -> Comp (x, Eq, y)
  | _ -> assert false


let const_nul c =
  try
    let n = ref (Num.Int 0) in
    MConst.iter (fun c i -> if i <> 0 then 
		   match c with
		     | ConstName _ -> raise Exit
		     | ConstInt a | ConstReal a -> 
			 n := Num.add_num (Num.mult_num (Num.Int i) a) !n) c;
    Num.compare_num !n (Num.Int 0) = 0
  with Exit -> false


let tick_pos sa = 
  let ticks = ref [] in 
  SAtom.iter
    (fun a -> match a with
       | Comp(Const c,Lt, Const m) when const_nul c -> 
	  begin
	    try
	      let n = ref None in
	      MConst.iter 
		(fun c i -> 
		   if i > 0 then 
		     match c with
		       | ConstName t -> 
			   if !n = None then n := Some c else raise Not_found
		       | _ -> raise Not_found )
		m;
	      match !n with Some c -> ticks := (c,a) :: !ticks | _ -> ()
	    with Not_found -> ()
	  end
       | _-> ()
    ) 
    sa;
  !ticks
 
let remove_tick tick e op x = 
  match e with
    | Const m ->
	begin
	  try
	    let c = MConst.find tick m in
	    if c > 0 then 
	      let m = MConst.remove tick m in
	      let m = 
		if MConst.is_empty m then 
		  MConst.add (ConstReal (Num.Int 0)) 1 m
		else m
	      in
	      simplification SAtom.empty (Comp (Const m, Lt, x))
	    else raise Not_found
	  with Not_found -> Comp (e, op, x)
	end
    | Arith (v, sv, m ) ->
	begin
	  try
	    let c = MConst.find tick m in
	    if c > 0 then 
	      let m = MConst.remove tick m in
	      let e = 
		if MConst.is_empty m then Elem (v, sv) else Arith(v, sv, m)
	      in
	      simplification SAtom.empty (Comp (e, Lt, x))
	    else raise Not_found
	  with Not_found -> Comp (e, op, x)
	end	
    | _ -> assert false
      

let contains_tick_term tick = function
  | Const m | Arith (_, _, m) ->
      (try MConst.find tick m <> 0 with Not_found -> false)
  | _ -> false

let contains_tick_atom tick = function
  | Comp (t1, _, t2) -> 
      contains_tick_term tick t1 || contains_tick_term tick t2
  | _ -> false

let remove_tick_atom sa (tick, at) = 
  let sa = SAtom.remove at sa in
  (* let flag = ref false in *)
  let remove a sa = 
    let a = match a with
      | Comp ((Const _ | Arith (_, _, _) as e), (Le|Lt|Eq as op), x)
      | Comp (x, (Eq as op), (Const _ | Arith (_, _, _) as e))  ->
	  remove_tick tick e op x
      | _ -> a 
    in
    (* flag := !flag || contains_tick_atom tick a; *)
    if contains_tick_atom tick a then sa else
    SAtom.add a sa
  in
  SAtom.fold remove sa SAtom.empty
  (* if !flag then SAtom.add at sa else sa *)

let const_simplification sa = 
  try
    let ticks = tick_pos sa in
    List.fold_left remove_tick_atom sa ticks
  with Not_found -> sa

let simplification_atoms base sa =
  SAtom.fold 
    (fun a sa ->
       let a = simplification base a in
       let a = simplification sa a in
       match a with
	 | True -> sa
	 | False -> raise Exit
	 | _ -> add a sa)
    sa SAtom.empty

let rec break a =
  match a with
    | True | False | Comp _ -> [SAtom.singleton a]
    | Ite (sa, a1, a2) ->
  	begin
  	  match SAtom.elements sa with
  	    | [] -> assert false
  	    | c ->
  	        let nc = List.map neg c in
  		let l = break a2 in
  		let a1_and_c = SAtom.add a1 sa in
  		let a1_and_a2 = List.map (SAtom.add a1) l in
  		let a2_and_nc_r = 
		  List.fold_left 
		    (fun acc c' ->
  		       List.fold_left 
			 (fun acc li -> SAtom.add c' li :: acc) acc l)
  		    a1_and_a2 nc 
		in
  		a1_and_c :: a2_and_nc_r
  	end

let add_without_redondancy sa l =
  if List.exists (fun sa' -> SAtom.subset sa' sa) l then l
  else
    let l =
      if true || delete then 
	List.filter (fun sa' -> not (SAtom.subset sa sa')) l
      else l
    in
    sa :: l

let simplify_atoms np =
  try
    let ites, base = SAtom.partition (function Ite _ -> true | _ -> false) np in
    let base = simplification_atoms SAtom.empty base in
    let ites = simplification_atoms base ites in
    let lsa = 
      SAtom.fold 
	(fun ite cubes ->
	   List.fold_left
	     (fun acc sa ->
		List.fold_left 
		  (fun sa_cubes cube ->
		     try
		       let sa = simplification_atoms cube sa in
		       let sa = SAtom.union sa cube in
		       if inconsistent sa then sa_cubes else 
			 add_without_redondancy sa sa_cubes
		     with Exit -> sa_cubes
		  )
		  acc cubes
	     )
	     []
	     (break ite)
	) 
	ites
	[base]
    in
    List.rev (List.rev_map const_simplification lsa)
  with Exit -> []


let contain_arg z = function
  | Elem (x, _) | Arith (x, _, _) -> Hstring.equal x z
  | Access (x, y) -> Hstring.equal y z
  | Const _ -> false

let has_var z = function
  | True | False -> false
  | Comp (t1, _, t2) -> (contain_arg z t1) || (contain_arg z t2)
  | Ite _ -> assert false

(********************)
(* Lazy Abstraction *)
(********************)

let abstract sign np =
  let in_sign = function
    | True | False -> true
    | Comp (t1, _, t2) -> STerm.mem t1 sign || STerm.mem t2 sign
    | Ite _ -> assert false
  in
  SAtom.filter in_sign np


let prime_h h level =
  Hstring.make ((Hstring.view h)^"@"^(string_of_int level))

let prime_term level t = match t with
  | Elem (e, Glob) -> Elem (prime_h e level, Glob)
  | Arith (a, Glob, c) -> Arith (prime_h a level, Glob, c)
  | Access (a, x) -> Access (prime_h a level, x)
  | _ -> t

let rec prime_atom level a = match a with
  | True | False -> a
  | Comp (t1, op, t2) -> Comp (prime_term level t1, op, prime_term level t2)
  | Ite (sa, a1, a2) -> 
    Ite (prime_satom level sa, prime_atom level a1, prime_atom level a2)
  
and prime_satom level sa =
  SAtom.fold (fun a acc -> SAtom.add (prime_atom level a) acc) sa SAtom.empty

let unprime_h h =
  let s = Hstring.view h in
  Hstring.make (String.sub s 0 (String.index s '@'))

let unprime_term t = match t with
  | Elem (e, Glob) -> Elem (unprime_h e, Glob)
  | Arith (a, Glob, c) -> Arith (unprime_h a, Glob, c)
  | Access (a, x) -> Access (unprime_h a, x)
  | _ -> t

let variables_term t acc = match t with
  | Elem (a, Glob) | Access (a, _) -> STerm.add t acc
  | Arith (a, Glob, _) -> STerm.add (Elem (a, Glob)) acc
  | _ -> acc

let rec variables_atom a acc = match a with
  | True | False -> acc
  | Comp (t1, _, t2) -> variables_term t1 (variables_term t2 acc) 
  | Ite (sa, a1, a2) -> 
    STerm.union (variables_of sa) (variables_atom a1 (variables_atom a2 acc))

and variables_of sa = SAtom.fold variables_atom sa STerm.empty


let apply_assigns assigns sigma level =
  List.fold_left 
    (fun (nsa, terms) (h, t) ->
      let nt = Elem (h, Glob) in
      let t = subst_term sigma t in
      SAtom.add (Comp (prime_term (level+1) nt, Eq, prime_term level t)) nsa,
      STerm.add nt terms)
    (SAtom.empty, STerm.empty) assigns


let add_update (sa, st) {up_arr=a; up_arg=j; up_swts=swts} procs sigma level =
  let rec sd acc = function
    | [] -> assert false
    | [d] -> List.rev acc, d
    | s::r -> sd (s::acc) r in
  let swts, (d, t) = sd [] swts in
  assert (d = SAtom.singleton True);
  let at = prime_term (level+1) (Access (a, j)) in
  let t = prime_term level t in
  let default = Comp (at, Eq, t) in
  let ites = 
    List.fold_left (fun ites (sa, t) ->
      let sa = prime_satom level sa in
      let t = prime_term level t in
      Ite (sa, Comp (at, Eq, t), ites)) default swts
  in
  List.fold_left (fun (sa, st) i ->
    SAtom.add (subst_atom [j, i] ites) sa,
    STerm.add (Access (a, j)) st
  ) (sa, st) procs

let apply_updates upds procs sigma level =
  List.fold_left 
    (fun acc up -> add_update acc up procs sigma level)
    (SAtom.empty, STerm.empty) upds

let preserve_terms upd_terms sa level =
  let vsa = STerm.fold 
    (fun t acc -> STerm.add (unprime_term t) acc) (variables_of sa) STerm.empty
  in
  let unc = STerm.diff vsa upd_terms in
  STerm.fold (fun t acc ->
    SAtom.add (Comp (prime_term (level+1) t, Eq, prime_term level t)) acc)
    unc SAtom.empty


let uguard_dnf sigma args tr_args level = function
  | [] -> []
  | [j, dnf] ->
      let uargs = List.filter (fun a -> not (H.list_mem a tr_args)) args in
      List.map (fun i ->
	List.map (fun sa ->
	  prime_satom level (subst_atoms ((j, i)::sigma) sa)) dnf) uargs
  | _ -> assert false


exception UnsatGuard of int * Literal.LT.t list list
  
let post sa tr args procs level =
  let sigma = List.combine tr.tr_args args in
  let guard = prime_satom level (subst_atoms sigma tr.tr_reqs) in
  let udnf = uguard_dnf sigma procs args level tr.tr_ureq in
  begin 
    try
      Prover.check_guard procs sa guard udnf
    with
      | Smt.Sat | Smt.IDontknow -> ()
      | Smt.Unsat uc -> raise (UnsatGuard (level, uc))
  end;
  let assi, assi_terms = apply_assigns tr.tr_assigns sigma level in
  let upd, upd_terms = apply_updates tr.tr_upds procs sigma level in
  let unchaged = preserve_terms (STerm.union assi_terms upd_terms) sa level in
  SAtom.union unchaged (SAtom.union assi (SAtom.union upd sa)) 


let mkinit arg init args =
  let init = prime_satom 0 init in
  match arg with
    | None -> init
    | Some z ->
	let sa, cst = SAtom.partition (has_var z) init in
	List.fold_left (fun acc h ->
	  SAtom.union (subst_atoms [z, h] sa) acc) cst args

exception Impos_trans of transition * Hstring.t list


let rec procs_from_trace trace =
  let procs = 
    List.fold_left (fun acc (_, args, {t_unsafe = nargs, unsafe}) ->
      List.fold_left (fun acc x -> S.add x acc) acc (args@nargs))
      S.empty trace in
  S.elements procs



let check_trace ({ t_unsafe = procs, un; t_from = from; t_init = ia, init} as s) =
  try
    Smt.Typing.declare_primed 0;
    
    let procs = procs_from_trace from in

    let sinit = mkinit ia init procs in
    eprintf "sinit:%a@." Pretty.print_cube sinit;
    let nsa, level, unsafe = 
      List.fold_left (fun (sa, level, _) (tr, args, {t_unsafe = _, unsafe}) ->
	Smt.Typing.declare_primed (level + 1);
	let nsa = post sa tr args procs level in
	nsa, level + 1, unsafe) (sinit, 0, un) from
    in
    begin 
      try
	Prover.check_guard procs nsa (prime_satom level unsafe) []
      with
	| Smt.Sat | Smt.IDontknow -> ()
	| Smt.Unsat uc -> raise (UnsatGuard (level, uc))
    end;
    raise (BUnsafe s)
  with (UnsatGuard (level, uc)) ->
    let signature = 
      List.fold_left (fun acc t -> STerm.add t acc) 
	STerm.empty (Prover.terms_from_unsat level uc) in
    eprintf "New signature:@.";
    STerm.iter (fun t -> eprintf ">> %a@." Pretty.print_term t) signature;
    exit 1
	


(**********************)
(* Postponed Formulas *)
(**********************)

let has_args_term args = function
  | Elem (x, Var) | Access (_, x) | Arith (x, Var, _) -> H.list_mem x args
  | _ -> false

let rec has_args args = function
  | True | False -> false
  | Comp (x, _, y) -> has_args_term args x || has_args_term args y
  | Ite (sa, a1, a2) -> 
      SAtom.exists (has_args args) sa || has_args args a1 || has_args args a2

let postpone args p np = 
  let sa1 = SAtom.filter (has_args args) p in
  let sa2 = SAtom.filter (has_args args) np in
  SAtom.equal sa2 sa1

let uguard sigma args tr_args = function
  | [] -> [SAtom.empty]
  | [j, dnf] ->
      let uargs = List.filter (fun a -> not (H.list_mem a tr_args)) args in
      List.fold_left 
	(fun lureq z ->
	   let m = List.map (subst_atoms ((j, z)::sigma)) dnf in
	   List.fold_left 
	     (fun acc sa -> 
		(List.map (fun zy-> SAtom.union zy sa) m) @ acc ) [] lureq
	)
	[SAtom.empty]
	uargs

  | _ -> assert false

let add_list n l = 
  if List.exists (fun n' -> ArrayAtom.subset n'.t_arru n.t_arru) l then l
  else
    let l =
      if true || delete then
  	List.filter (fun n' -> not (ArrayAtom.subset n.t_arru n'.t_arru)) l
      else l
    in
      n :: l

let make_cubes =
  let cpt = ref 0 in
  fun (ls, post) (args, rargs) 
    ({ t_unsafe = (uargs, p); t_nb = nb; 
       t_abstract_signature = sign} as s) tr np ->
      let nb_uargs = List.length uargs in
      let cube acc sigma =
	let lnp = simplify_atoms (subst_atoms sigma np) in
	let tr_args = List.map (svar sigma) tr.tr_args in
	List.fold_left
	  (fun (ls, post) np ->
	     let np, (nargs, _) = proper_cube np in
	     let lureq = uguard sigma nargs tr_args tr.tr_ureq in
	     List.fold_left 
	       (fun (ls, post) ureq ->
		 try
		  let ureq = simplification_atoms np ureq in
		  let np = SAtom.union ureq np in
		  let real_np = np in
		  let real_nargs = nargs in
		  let np = if lazy_abs then abstract sign np else np in
		  let np, nargs = 
		    if lazy_abs then let np, (nargs, _) = proper_cube np in np, nargs 
		    else np, nargs in
		  if debug && !verbose > 0 then Debug.pre_cubes np nargs;
		  if inconsistent np then begin
		    if debug && !verbose > 0 then eprintf "(inconsistent)@.";
		    (ls, post)
		  end
		  else
		    if simpl_by_uc && 
		      already_closed s tr tr_args <> None 
		    then ls, post
		    else
		      let arr_np = ArrayAtom.of_satom np in
		      incr cpt;
		      let new_s = 
			{ s with
			    t_from = (tr, tr_args, s)::s.t_from;
			    t_unsafe = nargs, np;
			    t_real = real_nargs, real_np;
			    t_arru = arr_np;
			    t_alpha = ArrayAtom.alpha arr_np nargs;
			    t_nb = !cpt;
			    t_nb_father = nb;
			} in
		      match post_strategy with
			| 0 -> add_list new_s ls, post
			| 1 -> 
			    if List.length nargs > nb_uargs then
			      ls, add_list new_s post
			    else add_list new_s ls, post
			| 2 -> 
			    if not (SAtom.is_empty ureq) || postpone args p np 
			    then ls, add_list new_s post
			    else add_list new_s ls, post
			| _ -> assert false
		 with Exit -> ls, post
	       ) (ls, post) lureq ) acc lnp
      in
      if List.length tr.tr_args > List.length rargs then (ls, post)
      else
	let d = all_permutations tr.tr_args rargs in
	List.fold_left cube (ls, post) d


let fresh_args ({ tr_args = args; tr_upds = upds} as tr) = 
  if args = [] then tr
  else
    let sigma = build_subst args fresh_vars in
    { tr with 
	tr_args = List.map (svar sigma) tr.tr_args; 
	tr_reqs = subst_atoms sigma tr.tr_reqs;
	tr_ureq = 
	List.map 
	  (fun (s, dnf) -> s, List.map (subst_atoms sigma) dnf) tr.tr_ureq;
	tr_assigns = 
	List.map (fun (x, t) -> x, subst_term sigma t) 
	  tr.tr_assigns;
	tr_upds = 
	List.map 
	  (fun ({up_swts = swts} as up) -> 
	     let swts = 
	       List.map 
		 (fun (sa, t) -> subst_atoms sigma sa, subst_term sigma t) swts
	     in
	     { up with up_swts = swts }) 
	  upds}


(*****************************************************)
(* Pre-image of an unsafe formula w.r.t a transition *)
(*****************************************************)

let pre tr unsafe =
  let tr = fresh_args tr in
  let tau = make_tau tr in
  let pre_unsafe = 
    SAtom.union tr.tr_reqs 
      (SAtom.fold (fun a -> add (pre_atom tau a)) unsafe SAtom.empty)
  in
  if debug && !verbose > 0 then Debug.pre tr pre_unsafe;
  let pre_unsafe, (args, m) = proper_cube pre_unsafe in
  if tr.tr_args = [] then tr, pre_unsafe, (args, args)
  else tr, pre_unsafe, (args, m::args)


(*********************************************************************)
(* Pre-image of a system s : computing the cubes gives a list of new *)
(* systems							     *)
(*********************************************************************)

let pre_system ({ t_unsafe = uargs, u; t_trans = trs} as s) =
  if profiling then TimePre.start (); 
  Debug.unsafe s;
  let ls, post = 
    List.fold_left
    (fun acc tr ->
       let tr, pre_u, info_args = pre tr u in
       make_cubes acc info_args s tr pre_u) 
    ([], []) 
    trs 
  in
  if profiling then TimePre.pause ();
  ls, post


(********************************************************)
(* Renames the parameters of the initial unsafe formula *)
(********************************************************)

let init_atoms args sa = 
  let cpt = ref 0 in
  let sigma = 
    List.map 
      (fun z -> incr cpt; z, H.make ("#"^(string_of_int !cpt))) args in
  let sa = apply_subst sa sigma in
  let args = List.map snd sigma in
  args, sa

let init_parameters ({t_unsafe = (args, sa); t_arru = a; t_invs = invs } as s) =
  let args, sa = init_atoms args sa in
  let a = ArrayAtom.of_satom sa in
  let invs = List.map (fun (argsi, sai) -> init_atoms argsi sai) invs in
  { s with t_unsafe = (args, sa); t_arru = a; 
    t_alpha = ArrayAtom.alpha a args; t_invs = invs }



(******************************************************)
(* Backward deletion of subsumed nodes : experimental *)
(******************************************************)

let filter_rev p =
  let rec find accu = function
  | [] -> accu
  | x :: l -> if p x then find (x :: accu) l else find accu l in
  find []

let is_deleted s = s.t_deleted || has_deleted_ancestor s

let delete_nodes s nodes nb_del inc =
  (* if (not s.t_deleted) && not (has_deleted_ancestor s) then *)
    nodes := filter_rev
      (fun n -> 
	if (not n.t_deleted) &&
	  (* not (List.exists (fun (_,anc) -> n == anc) s.t_from) && *)
	  not (List.exists (fun (_,_,anc) -> 
	      ArrayAtom.equal n.t_arru anc.t_arru)
       		 s.t_from) &&
	  (ArrayAtom.subset s.t_arru n.t_arru
	   || has_deleted_ancestor n ) then 
	  begin
	    (* eprintf "deleted node@."; *)
	    n.t_deleted <- true;
	    if inc 
	    (* && not (List.exists (fun (_,_,anc) -> anc.t_deleted) n.t_from) *)
	    then incr nb_del;
	    false
	  end
	else true)
      (List.rev !nodes)


let delete_nodes_inv inv nodes = 
  nodes := List.filter
  (fun n -> 
     if (not n.t_deleted) &&
       List.exists (fun i -> ArrayAtom.subset i.t_arru n.t_arru) inv then 
       begin
	 n.t_deleted <- true;
	 false
       end
     else true)
  !nodes

let delete_node s = s.t_deleted <- true

(**********************************)
(* Invariant generation stuff...  *)
(**********************************)

let same_number z = function 
  | Const _ -> true
  | Elem (s, v) | Arith (s, v, _) -> 
      H.equal s z || v = Glob || v = Constr
  | Access (_, s) -> H.equal s z

let rec contains_only z = function
  | True | False -> true
  | Comp (i, _ , j) -> same_number z i && same_number z j
  | Ite (sa, a1, a2) -> 
      contains_only z a1 && contains_only z a2 
      && SAtom.for_all (contains_only z) sa

let partition ({ t_unsafe = (args, sa) } as s) = 
  List.fold_left 
    (fun l z -> 
       let sa', _ = SAtom.partition (contains_only z) sa in
       if SAtom.cardinal sa' < 2 then l 
       else 
	 let ar' = ArrayAtom.of_satom sa' in
	 { s with
	   t_from = [];
	   t_unsafe = [z], sa';
	   t_arru = ar';
	   t_alpha = ArrayAtom.alpha ar' [z];
	   t_deleted = false;
	   t_nb = 0;
	   t_nb_father = -1;
	 } :: l)
    [] args

let impossible_inv { t_arru = p } not_invs =
  List.exists (fun { t_arru = ni } -> ArrayAtom.subset p ni) not_invs

type inv_result =  Inv | NotInv | Nothing

let worker_inv search invariants not_invs p =
  try 
    if impossible_inv p !not_invs then Nothing
    else begin  
      search ~invariants:!invariants ~visited:[] [p]; 
      if not quiet then eprintf "Good! We found an invariant :-) \n %a @." 
	Pretty.print_system p;
      Inv
    end
  with | Search.Unsafe | Search.ReachBound -> NotInv

let init_thread search invariants not_invs visited postponed candidates =
  
  let master_inv (p, s) res =
    (match res with
      | Inv ->
	invariants := p :: !invariants;
	s.t_deleted <- true;
	if delete then delete_nodes_inv [p] visited;
	if delete then delete_nodes_inv [p] postponed;
      | NotInv -> not_invs := p :: !not_invs
      | Nothing -> ());
    []
  in

  Thread.create (fun () ->
    while true do
      try 
	(* let candidate = Queue.pop candidates in *)
	let candidatel = Queue.fold (fun acc c -> c::acc) [] candidates in
	let cand = List.fold_left
	  (fun acc cs ->
	    (List.map (fun x -> x, cs) (partition cs)) @ acc) [] candidatel in
	Queue.clear candidates;
	if debug then eprintf "(Thread inv) Got something to do !@.";
	Functory.Cores.compute ~worker:(worker_inv search invariants not_invs)
	  ~master:master_inv 
	  (* (List.map (fun x -> x,candidate) (partition candidate));  *)
	  cand;
	Thread.yield ();
      with Queue.Empty -> 
	Thread.yield (); eprintf "(Thread inv) Nothing to do ...@."
    done;
  ) ()



      
let gen_inv search ~invariants not_invs s = 
  List.fold_left 
    (fun (invs, not_invs) p -> 
       try
	 let invariants = invs@invariants in
	 (* if fixpoint ~invariants:invariants ~visited:[] p then invs  *)
	 (* else *)
	 if impossible_inv p not_invs then invs, not_invs
	 else begin  
	   search ~invariants:invariants ~visited:[] [p]; 
	   if not quiet then eprintf "Good! We found an invariant :-) \n %a @." 
	     Pretty.print_system p;
	   p::invs, not_invs
	 end
       with | Search.Unsafe | Search.ReachBound -> invs, p::not_invs) 
    ([], not_invs) (partition s)



let gen_inv_proc search invs not_invs s = 
  let new_invs, _, new_not_invs, _ =
    List.fold_left 
      (fun ((new_invs, invs, new_not_invs, not_invs) as acc) p -> 
	try
	  if impossible_inv p not_invs then acc
	  else begin
	    search ~invariants:invs ~visited:[] [p]; 
	    if not quiet then 
	      eprintf "Good! We found an invariant :-) \n %a @." 
		Pretty.print_system p;
	    p::new_invs, p::invs, new_not_invs, not_invs
	  end
	with Search.Unsafe | Search.ReachBound ->
	  new_invs, invs, p::new_not_invs, p::not_invs) 
      ([], invs, [], not_invs) (partition s)
  in
  new_invs, new_not_invs


let extract_candidates s not_invs =
  List.filter (fun p -> not (impossible_inv p not_invs)) (partition s)

let is_inv search p invs =
  try
    search ~invariants:invs ~visited:[] [p]; 
    if not quiet then 
      eprintf "Good! We found an invariant :-) \n %a @." Pretty.print_system p;
    true
  with Search.Unsafe | Search.ReachBound -> false

(* ----------------- Search strategy selection -------------------*)

module T = struct
  type t = t_system

  exception Unsafe of t


  let invariants s = 
    List.map (fun ((a,u) as i) -> 
      let ar = ArrayAtom.of_satom u in
      { s with 
	t_unsafe = i; 
	t_real = i;
	t_arru = ar;
	t_alpha = ArrayAtom.alpha ar a
      }) s.t_invs
  let size s = List.length (fst s.t_unsafe)
  let maxrounds = maxrounds
  let maxnodes = maxnodes
  let gen_inv = gen_inv
  let gen_inv_proc = gen_inv_proc
  let extract_candidates = extract_candidates
  let is_inv = is_inv

  let init_thread = init_thread

  let delete_nodes = delete_nodes
  let delete_nodes_inv = delete_nodes_inv
  let delete_node = delete_node
  let is_deleted = is_deleted

  let fixpoint = fixpoint
  let easy_fixpoint = easy_fixpoint
  let hard_fixpoint = hard_fixpoint

  let safety s = 
    try check_safety s 
    with BUnsafe s -> 
      try check_trace s 
      with BUnsafe s -> raise (Unsafe s)


  let pre = pre_system
  let has_deleted_ancestor = has_deleted_ancestor
  let print = Pretty.print_node
  let sort = List.stable_sort (fun {t_unsafe=args1,_} {t_unsafe=args2,_} ->
    Pervasives.compare (List.length args1) (List.length args2))
  let nb_father s = s.t_nb_father
end

module StratDFS = Search.DFS(T)
module StratDFSL = Search.DFSL(T)
module StratDFSH = Search.DFSH(T)
module StratBFS = Search.BFS(T)
module StratBFS_dist = Search.BFS_dist(T)
module StratBFSinvp = Search.BFSinvp(T)
module StratDFSHL = Search.DFSHL(T)

let search = 
  match mode with
    | Dfs -> StratDFS.search
    | DfsL -> StratDFSL.search
    | DfsH -> StratDFSH.search
    | Bfs -> StratBFS.search
    | BfsDist -> StratBFS_dist.search
    | Bfsinvp -> StratBFSinvp.search
    | DfsHL -> StratDFSHL.search

let system uns =
  let uns = List.map init_parameters uns in
  let invariants = match uns with
    | s::_ -> T.invariants s
    | [] -> assert false
  in
  search ~invariants ~visited:[] uns
