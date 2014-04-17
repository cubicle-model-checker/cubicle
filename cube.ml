(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2013                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

open Format
open Options
open Ast
open Util
open Term.Type
open Atom.Type

module H = Hstring
module S = H.HSet
let hempty = H.empty

module SS = Set.Make
  (struct 
     type t = H.t * H.t
    let compare (s1, s2) (t1, t2) = 
      let c = H.compare s1 t1 in
      if c <> 0 then c
      else H.compare s2 t2
   end)

type t =
 private {
   vars : Variable.t list;
   litterals : Atom.Set.t;
   array : Atom.Array.t;
 }


let create vars sa =
  {
    vars = vars;
    litterals = sa;
    array = Atom.Array.of_satom sa;
  }


let cube_false =
{
  vars = [];
  litterals = Atom.Set.singleton False;
  array = Array.of_list [False];
}

(***************************************)
(* Good renaming of a cube's variables *)
(***************************************)

let normal_form { litterals = sa; array = ar } =
  let vars = Atom.Set.variables sa in
  if !size_proc <> 0 && List.length vars > !size_proc then
    cube_false
  else
  let sigma = Variables.build_subst vars Variables.procs in
  let new_vars = List.map snd sigma in
  let new_ar = Atom.Array.apply_subst sigma ar in
  let new_sa = Atom.Array.to_satom ar in
  {
    vars = new_vars;
    litterals = new_sa;
    array = new_ar;
  }


let create_normal sa = normal_form (create [] sa)




let size c = List.length c.vars
let card c = Array.length c.array



(*****************************************************************)
(* Simplifcation of atoms in a cube based on the hypothesis that *)
(* indices #i are distinct and the type of elements is an	 *)
(* enumeration							 *)
(* 								 *)
(* simplify comparison atoms, according to the assumption that	 *)
(* variables are all disctincts					 *)
(*****************************************************************)

let redondant_or_false others a = match a with
  | True -> True
  | Comp (t1, Neq, (Elem (x, (Var | Constr)) as t2))
  | Comp ((Elem (x, (Var | Constr)) as t2), Neq, t1) ->
      (try 
	 (Atom.Set.iter (function 
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
	 (Atom.Set.iter (function
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
	 (Atom.Set.iter (function 
	   | Comp (t1', Eq, t2') 
	       when (compare_term t1' t1 = 0 && compare_term t2' t2 = 0) 
		 || (compare_term t1' t2 = 0 && compare_term t2' t1 = 0) ->
	     raise Exit
	   | _ -> ()) others); a
       with Exit -> False)
  | Comp (t1, Eq, t2) ->
      (try 
	 (Atom.Set.iter (function 
	   | Comp (t1', Neq, t2') 
	       when (compare_term t1' t1 = 0 && compare_term t2' t2 = 0) 
		 || (compare_term t1' t2 = 0 && compare_term t2' t1 = 0)  ->
	     raise Exit
	   | _ -> ()) others); a
       with Exit -> False)
  | _ -> a

	   
let rec simplify_term = function
  | Arith (Arith (x, c1), c2) -> simplify_term (Arith (x, add_constants c1 c2))
  | t -> t
	   

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
    | (Eq | Neq) , _ ->
        if si = Glob && (H.view i).[0] = '*' then True
        else
          let ti = Elem (i, si) in
	  let tj = Elem (j, sj) in 
	  if compare_term ti tj < 0 then Comp (tj, op, ti)
	  else Comp (ti, op, tj)
    | _ -> 
        if si = Glob && (H.view i).[0] = '*' then True
        else Comp (Elem (i, si), op, Elem (j, sj))
		  
let rec simplification np a =
  let a = redondant_or_false (Atom.Set.remove a np) a in
  match a with
    | True | False -> a 
    | Comp (Elem (i, si), op , Elem (j, sj)) -> simplify_comp i si op j sj
    | Comp (Arith (i, csi), op, (Arith (j, csj)))
      when compare_constants csi csj = 0 -> simplification np (Comp (i, op, j))
    | Comp (Arith (i, csi), op, (Arith (j, csj))) ->
        let cs = add_constants (mult_const (-1) csi) csj in
	if MConst.is_empty cs then Comp (i, op, j)
	else Comp (i, op, (Arith (j, cs)))
    (* | Comp (Const cx, op, Arith (y, sy, cy)) -> *)
    (* 	Comp (Const (add_constants (mult_const (-1) cx) cx), op, *)
    (* 	      Arith (y, sy , (add_constants (mult_const (-1) cx) cy))) *)
    (* | Comp ( Arith (x, sx, cx), op, Const cy) -> *)
    (* 	Comp (Arith (x, sx , (add_constants (mult_const (-1) cy) cx)), op, *)
    (* 	      Const (add_constants (mult_const (-1) cy) cy)) *)
    | Comp (Arith (x, cx), op, Const cy) ->
       let mcx = mult_const (-1) cx in
       Comp (x, op, Const (add_constants cy mcx))
    | Comp (Const cx, op, Arith (y, cy)) ->
       let mcy = mult_const (-1) cy in
       Comp (Const (add_constants cx mcy), op, y)
       
    | Comp (x, op, Arith (y, cy)) when compare_term x y = 0 ->
        let cx = add_constants (mult_const (-1) cy) cy in
	let c, i = MConst.choose cy in
	let my = MConst.remove c cy in
	let cy = 
	  if MConst.is_empty my then MConst.add c (i/(abs i)) my else cy in 
        Comp (Const cx, op, Const cy)
    | Comp (Arith (y, cy), op, x) when compare_term x y = 0 ->
        let cx = add_constants (mult_const (-1) cy) cy in
	let c, i = MConst.choose cy in
	let my = MConst.remove c cy in
	let cy = 
	  if MConst.is_empty my then MConst.add c (i/(abs i)) my else cy in 
        Comp (Const cy, op, Const cx)
    | Comp (Const c1, (Eq | Le), Const c2) when compare_constants c1 c2 = 0 ->
       True 
    | Comp (Const c1, Le, Const c2) ->
       begin
	 match MConst.is_num c1, MConst.is_num c2 with
	 | Some n1, Some n2 -> if Num.le_num n1 n2 then True else False
	 | _ -> a
       end
    | Comp (Const c1, Lt, Const c2) ->
       begin
	 match MConst.is_num c1, MConst.is_num c2 with
	 | Some n1, Some n2 -> if Num.lt_num n1 n2 then True else False
	 | _ -> a
       end
    | Comp (Const _ as c, Eq, y) -> Comp (y, Eq, c)
    | Comp (x, Eq, y) when compare_term x y = 0 -> True
    | Comp (x, (Eq | Neq as op), y) when compare_term x y < 0 -> Comp (y, op, x)
    | Comp _ -> a
    | Ite (sa, a1, a2) -> 
	let sa = 
	  Atom.Set.fold 
	    (fun a -> add (simplification np a)) sa Atom.Set.empty
	in
	let a1 = simplification np a1 in
	let a2 = simplification np a2 in
	if Atom.Set.is_empty sa || Atom.Set.subset sa np then a1
	else if Atom.Set.mem False sa then a2
	else Ite(sa, a1, a2)



let rec simplification_terms a = match a with
    | True | False -> a
    | Comp (t1, op, t2) -> Comp (simplify_term t1, op, simplify_term t2)
    | Ite (sa, a1, a2) ->
       Ite (Atom.Set.fold (fun a -> Atom.Set.add (simplification_terms a)) sa Atom.Set.empty,
	    simplification_terms a1, simplification_terms a2)


(***********************************)
(* Cheap check of inconsitent cube *)
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
  let l = Atom.Set.elements sa in
  inconsistent_list l

let inconsistent_array a =
  let l = Array.to_list a in
  inconsistent_list l


let inconsistent_set sa =
  try
    let _ = 
      Atom.Set.fold (fun a acc -> inconsistent_aux acc a) 
	sa ([], [], [], [], [], [], []) in
    false
  with Exit -> true


let inconsistent_array ar =
  try
    Prover.TimeF.start ();
    let _ = Array.fold_left inconsistent_aux ([], [], [], [], [], [], []) ar in
    Prover.TimeF.pause ();
    false
  with Exit -> Prover.TimeF.pause (); true

let inconsistent_2arrays ar1 ar2 =
  try
    let acc = 
      Array.fold_left inconsistent_aux ([], [], [], [], [], [], []) ar1 in
    let _ = Array.fold_left inconsistent_aux acc ar2 in
    false
  with Exit -> true


let inconsistent_2sets sa1 sa2 =
  try
    let acc = Atom.Set.fold 
      (fun a acc -> inconsistent_aux acc a) 
      sa1 ([], [], [], [], [], [], []) in
    let _ = Atom.Set.fold 
      (fun a acc -> inconsistent_aux acc a) 
      sa2 acc in
    false
  with Exit -> true

let inconsistent ?(use_sets:false) { litterals: sa; array: ar } =
  if use_sets then inconsistent_set sa
  else inconsistent_array ar

let inconsistent_2 ?(use_sets:false)
    { litterals: sa1; array: ar1 } { litterals: sa2; array: ar2 } =
  if use_sets then inconsistent_2sets sa1 sa2
  else inconsistent_2arrays ar1 ar2



(* ---------- TODO : doublon avec Atom.Set.variables -----------*)

let rec add_arg args = function
  | Elem (s, _) ->
      let s' = H.view s in
      if s'.[0] = '#' || s'.[0] = '$' then S.add s args else args
  | Access (_, ls) ->
      List.fold_left (fun args s ->
        let s' = H.view s in
        if s'.[0] = '#' || s'.[0] = '$' then S.add s args else args)
        args ls        
  | Arith (t, _) -> add_arg args t
  | Const _ -> args

let args_of_atoms sa = 
  let rec args_rec sa args = 
    Atom.Set.fold 
      (fun a args -> 
	 match a with 
	   | True | False -> args
	   | Comp (x, _, y) -> add_arg (add_arg args x) y
	   | Ite (sa, a1, a2) -> 
	       args_rec (Atom.Set.add a1 (Atom.Set.add a2 sa)) args) 
      sa args
  in 
  S.elements (args_rec sa S.empty)

(* --------------------------------------------------------------*)

let const_sign c =
  try
    let n = ref (Num.Int 0) in
    MConst.iter (fun c i -> if i <> 0 then 
		   match c with
		     | ConstName _ -> raise Exit
		     | ConstInt a | ConstReal a -> 
			 n := Num.add_num (Num.mult_num (Num.Int i) a) !n) c;
    Some (Num.compare_num !n (Num.Int 0))
  with Exit -> None

let const_nul c = const_sign c = Some 0

let tick_pos sa = 
  let ticks = ref [] in 
  Atom.Set.iter
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
	      simplification Atom.Set.empty (Comp (Const m, Lt, x))
	    else raise Not_found
	  with Not_found -> Comp (e, op, x)
	end
    | Arith (v, m) ->
	begin
	  try
	    let c = MConst.find tick m in
	    if c > 0 then 
	      let m = MConst.remove tick m in
	      let e = 
		if MConst.is_empty m then v else Arith(v, m)
	      in
	      simplification Atom.Set.empty (Comp (e, Lt, x))
	    else raise Not_found
	  with Not_found -> Comp (e, op, x)
	end	
    | _ -> assert false
      

let contains_tick_term tick = function
  | Const m | Arith (_, m) ->
      (try MConst.find tick m <> 0 with Not_found -> false)
  | _ -> false

let rec contains_tick_atom tick = function
  | Comp (t1, _, t2) -> 
      contains_tick_term tick t1 || contains_tick_term tick t2
  (* | Ite (sa, a1, a2) -> *)
  (*     contains_tick_atom tick a1 || contains_tick_atom tick a2 || *)
  (*       Atom.Set.exists (contains_tick_atom tick) sa *)
  | _ -> false

let remove_tick_atom sa (tick, at) = 
  let sa = Atom.Set.remove at sa in
  (* let flag = ref false in *)
  let remove a sa = 
    let a = match a with
      | Comp ((Const _ | Arith (_, _) as e), (Le|Lt|Eq as op), x)
      | Comp (x, (Eq as op), (Const _ | Arith (_, _) as e))  ->
	  remove_tick tick e op x
      | _ -> a 
    in
    (* flag := !flag || contains_tick_atom tick a; *)
    if contains_tick_atom tick a then sa else
    Atom.Set.add a sa
  in
  Atom.Set.fold remove sa Atom.Set.empty
  (* if !flag then Atom.Set.add at sa else sa *)

let const_simplification sa = 
  try
    let ticks = tick_pos sa in
    List.fold_left remove_tick_atom sa ticks
  with Not_found -> sa

let simplification_atoms base sa =
  Atom.Set.fold 
    (fun a sa ->
       let a = simplification_terms a in
       let a = simplification base a in
       let a = simplification sa a in
       match a with
	 | True -> sa
	 | False -> raise Exit
	 | _ -> add a sa)
    sa Atom.Set.empty

let rec break a =
  match a with
    | True | False | Comp _ -> [Atom.Set.singleton a]
    | Ite (sa, a1, a2) ->
  	begin
  	  match Atom.Set.elements sa with
  	    | [] -> assert false
  	    | c ->
  	        let nc = List.map Atom.neg c in
  		let l = break a2 in
  		let a1_and_c = Atom.Set.add a1 sa in
  		let a1_and_a2 = List.map (Atom.Set.add a1) l in
  		let a2_and_nc_r = 
		  List.fold_left 
		    (fun acc c' ->
  		       List.fold_left 
			 (fun acc li -> Atom.Set.add c' li :: acc) acc l)
  		    a1_and_a2 nc 
		in
  		a1_and_c :: a2_and_nc_r
  	end

let add_without_redondancy sa l =
  if List.exists (fun sa' -> Atom.Set.subset sa' sa) l then l
  else
    let l =
      if true || delete then 
	List.filter (fun sa' -> not (Atom.Set.subset sa sa')) l
      else l
    in
    sa :: l

let elim_ite_atoms np =
  try
    let ites, base = Atom.Set.partition (function Ite _ -> true | _ -> false) np in
    let base = simplification_atoms Atom.Set.empty base in
    let ites = simplification_atoms base ites in
    let lsa = 
      Atom.Set.fold 
	(fun ite cubes ->
	   List.fold_left
	     (fun acc sa ->
		List.fold_left 
		  (fun sa_cubes cube ->
		     try
		       let sa = simplification_atoms cube sa in
		       let sa = Atom.Set.union sa cube in
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


let simplify { litterals = sa; } =
  create_normal (simplification_atoms Atom.Set.empty sa)

let elim_ite_simplify { litterals = sa; } =
  create_normal (elim_ite_atoms sa)

(* TODO ici *)

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
	if Atom.Array.subset na sa then Some fix
	else find r
    in find ls
  with Not_found -> None

let has_alredy_closed_ancestor s =
  let rec has acc = function
    | [] -> false
    | (tr, args, f) :: r ->
      match already_closed f tr args with
	| None -> has (f :: acc) r
	| Some fix -> 
	  not (List.exists (fun f -> Atom.Array.equal f.t_arru fix.t_arru) acc)
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
      let simpl = Atom.Array.diff fa (Atom.Array.diff sa fixa) in
      let tr_margs = 
	try H.H.find closed tr.tr_name with Not_found -> MArgs.empty in
      let ls = try MArgs.find args tr_margs with Not_found -> [] in
      H.H.add closed tr.tr_name (MArgs.add args ((simpl, fix) :: ls) tr_margs)

(**********************************************************************)

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


exception Fixpoint of int list

let check_fixpoint ?(pure_smt=false) ({t_unsafe = (nargs, _); t_arru = anp} as s) visited =
  Prover.assume_goal s;
  (* let nb_nargs = List.length nargs in *)
  let nodes = List.fold_left
    (fun nodes ({ t_alpha = args, ap; t_unsafe = real_args, _ } as sp) ->
      let dif = extra_args real_args nargs in
      (* if List.length args > List.length nargs then nodes *)
      (* else *)
      let nargs = if dif = [] then nargs else nargs@dif in
      let d = relevant_permutations anp ap args nargs in
      List.fold_left
	(fun nodes ss ->
	  let pp = Atom.Array.apply_subst ss ap in
	  if not pure_smt && Atom.Array.subset pp anp then begin
	    if simpl_by_uc then add_to_closed s pp sp ;
	    raise (Fixpoint [sp.t_nb])
	  end
	  (* Heuristic : throw away nodes too much different *)
	  (* else if Atom.Array.nb_diff pp anp > 2 then nodes *)
	  (* line below useful for arith : ricart *)
	  else if not pure_smt &&
                  inconsistent_array (Atom.Array.union pp anp) then nodes
	  else if Atom.Array.nb_diff pp anp > 1 then (pp,sp.t_nb)::nodes
	  else (Prover.assume_node pp ~id:sp.t_nb; nodes)
	) nodes d
    ) [] visited
  in
  TimeSort.start ();
  let nodes = 
    List.fast_sort 
      (fun (a1, n1) (a2, n2) -> Atom.Array.compare_nb_common anp a1 a2) 
      nodes 
  in
  TimeSort.pause ();
  List.iter (fun (p, cnum) -> Prover.assume_node p ~id:cnum) nodes
  

let easy_fixpoint ({t_unsafe = _, np; t_arru = npa } as s) nodes =
  if (delete && (s.t_deleted || has_deleted_ancestor s))
    ||
    (simpl_by_uc && has_alredy_closed_ancestor s)
  then Some []
  else
    let db = ref None in
    ignore (List.exists 
	      (fun ({ t_arru = pa } as sp) -> 
		 if Atom.Array.subset pa npa then
		   (db := Some [sp.t_nb];
		    if simpl_by_uc then add_to_closed s pa sp; true)
		 else false) nodes);
    !db

let hard_fixpoint ({t_unsafe = _, np; t_arru = npa } as s) nodes =
  try
    check_fixpoint s nodes;
    None
  with 
    | Fixpoint db -> Some db
    | Exit -> None
    | Smt.Unsat db -> Some db
  


let pure_smt_fixpoint ({t_unsafe = _, np; t_arru = npa } as s) nodes =
  try
    check_fixpoint ~pure_smt:true s nodes;
    None
  with 
    | Fixpoint db -> Some db
    | Exit -> None
    | Smt.Unsat db -> Some db
  


let fixpoint ~invariants ~visited ({ t_unsafe = (_,np) } as s) =
  Debug.unsafe s;
  TimeFix.start ();
  let nodes = (List.rev_append invariants visited) in
  let r = 
    match easy_fixpoint s nodes with
      | None -> hard_fixpoint s nodes
      | r -> r
  in
  TimeFix.pause ();
  r

(*************** Operations with tries () *******************)

let invert_subst = List.map (fun (x,y) -> y,x)

let medium_fixpoint_trie {t_unsafe = (nargs,_); 
                          t_alpha = args, ap; 
                          t_arru = anp} visited learnt =
  TimeEasyFix.start ();
  let substs = all_permutations args nargs in
  let substs = List.tl substs in (* Drop 'identity' permutation. 
                                    Already checked in easy_fixpoint. *)
  try
    List.iter (fun ss -> 
      let u = Atom.Array.apply_subst ss ap in
      let lstu = Array.to_list u in
      match Cubetrie.mem lstu !visited with
        | Some uc -> raise (Fixpoint uc)
        | None -> match Cubetrie.mem lstu !learnt with
            | Some uc -> raise (Fixpoint uc)
            | None -> ()
    ) substs;
    TimeEasyFix.pause ();
    None
  with Fixpoint uc -> 
    TimeEasyFix.pause ();
    Some uc

let hard_fixpoint_trie s visited learnt =
  TimeHardFix.start (); 
  let anp = s.t_arru in
  let nargs = fst s.t_unsafe in
  let substs = all_permutations nargs nargs in
  let relevant ss =
    let u = Atom.Array.apply_subst ss anp in
    let lstu = Array.to_list u in
    let nodes = Cubetrie.consistent lstu !visited in
    let nodes = List.filter (fun s -> not (s.t_deleted)) nodes in
    let ss' = invert_subst ss in
    List.map (fun n -> 
      let p = Atom.Array.apply_subst ss' n.t_arru in
      (p, n.t_nb), Atom.Array.nb_diff p u
    ) nodes
  in
  let cubes = List.flatten (List.map relevant substs) in
  let res = 
    if cubes = [] then None
    else begin
      TimeSort.start ();
      let cubes =
        List.fast_sort
          (fun c1 c2 -> Pervasives.compare (snd c1) (snd c2))
          cubes
      in
        TimeSort.pause ();
        try
          Prover.assume_goal s;
          List.iter (fun ((p, id), _) -> Prover.assume_node p ~id) cubes;
          None
        with
          | Exit -> None
          | Smt.Unsat uc -> 
              learnt := Cubetrie.add (Array.to_list anp) s !learnt;
              Some uc
    end
  in
  TimeHardFix.pause ();
  res


let delete_node s  = s.t_deleted <- true


let fixpoint_trie s lstu visited learnt postponed =
  TimeFix.start ();
  TimeEasyFix.start ();
  let res = 
    match Cubetrie.mem lstu !visited with
      | (Some _) as r -> r
      | None -> match Cubetrie.mem lstu !learnt with
          | (Some _) as r -> r
          | None ->
              if delete then
                if s.t_deleted then begin
                  (* Node was postponed earlier, now visit it.*)
                  s.t_deleted <- false;
                  None
                end
                else if has_deleted_ancestor s then begin
                  (* Postpone the node. *)
                  delete_node s;
                  postponed := s::!postponed;
                  Some []
                end
                else None
              else None
  in
  TimeEasyFix.pause ();
  let res = 
    match res with 
      | Some _ -> res
      | None -> match medium_fixpoint_trie s visited learnt with
          | (Some _) as r -> r
          | None -> hard_fixpoint_trie s visited learnt
  in
  TimeFix.pause ();
  res





(*************** Other version with tries *******************)

let check_and_add nargs anp nodes
    ({ t_alpha = args, ap; t_unsafe = real_args, _ } as sp) =
  let dif = extra_args real_args nargs in
  (* if List.length args > nb_nargs then nodes *)
  (* else *)
  let nargs = if dif = [] then nargs else nargs@dif in
  let d = relevant_permutations anp ap args nargs in
  List.fold_left
    (fun nodes ss ->
      let pp = Atom.Array.apply_subst ss ap in
      (* if Atom.Array.subset pp anp then begin *)
      (*   if simpl_by_uc then add_to_closed s pp sp ; *)
      (*   raise (Fixpoint [sp.t_nb]) *)
      (* end *)
      (* Heuristic : throw away nodes too much different *)
      (* else if Atom.Array.nb_diff pp anp > 2 then nodes *)
      (* line below useful for arith : ricart *)
      if inconsistent_array (Atom.Array.union pp anp) then nodes
      else if Atom.Array.nb_diff pp anp > 1 then (pp,sp.t_nb)::nodes
      else (Prover.assume_node pp ~id:sp.t_nb; nodes)
    ) nodes d
  

let check_fixpoint_trie2 ({t_unsafe = (nargs, _); t_arru = anp} as s) visited =
  Prover.assume_goal s;
  (* let nb_nargs = List.length nargs in *)
  let unprioritize_cands = false (* lazyinv *) in
  let nodes, cands = Cubetrie.fold
    (fun (nodes, cands) sp ->
      if unprioritize_cands && sp.t_nb < 0 then nodes, sp :: cands
      else check_and_add nargs anp nodes sp, cands
    ) ([], []) visited in
  let nodes = List.fold_left (check_and_add nargs anp) nodes cands in
  TimeSort.start ();
  let nodes = 
    List.fast_sort 
      (fun (a1, n1) (a2, n2) ->
        if unprioritize_cands && n1 < 0 && n2 >= 0 then 1 
        (* a1 is a candidate *)
        else if unprioritize_cands && n2 < 0 && n1 >= 0 then -1
        (* a2 is a candidate *)
        else Atom.Array.compare_nb_common anp a1 a2) 
      nodes 
  in
  TimeSort.pause ();
  List.iter (fun (p, cnum) -> Prover.assume_node p ~id:cnum) nodes
  
let easy_fixpoint_trie2 ({t_unsafe = _, np; t_arru = npa } as s) nodes =
  if (delete && (s.t_deleted || has_deleted_ancestor s))
    ||
    (simpl_by_uc && has_alredy_closed_ancestor s)
  then Some []
  else Cubetrie.mem_array npa nodes

let medium_fixpoint_trie2 {t_unsafe = (nargs,_); 
                          t_alpha = args, ap; 
                          t_arru = anp} visited  =
  let substs = all_permutations args nargs in
  let substs = List.tl substs in (* Drop 'identity' permutation. 
                                    Already checked in easy_fixpoint. *)
  try
    List.iter (fun ss -> 
      let u = Atom.Array.apply_subst ss ap in
      match Cubetrie.mem_array u visited with
        | Some uc -> raise (Fixpoint uc)
        | None -> ()
    ) substs;
    None
  with Fixpoint uc -> Some uc

let hard_fixpoint_trie2 ({t_unsafe = _, np; t_arru = npa } as s) nodes =
  try
    check_fixpoint_trie2 s nodes;
    None
  with 
    | Fixpoint db -> Some db
    | Exit -> None
    | Smt.Unsat db -> Some db
  

let fixpoint_trie2 nodes ({ t_unsafe = (_,np) } as s) =
  Debug.unsafe s;
  TimeFix.start ();
  let r =
    match easy_fixpoint_trie2 s nodes with
    | None ->
       (match medium_fixpoint_trie2 s nodes with
        | None -> hard_fixpoint_trie2 s nodes
        | r -> r)
    | r -> r
  in
  TimeFix.pause ();
  r



(* Experimental expansion of cubes to dnf : depreciated *)

let values_of_type ty =
  let vals =
    if Hstring.equal ty Smt.Type.type_proc then proc_vars
    else Smt.Type.constructors ty in
  List.fold_left (fun acc v -> S.add v acc) S.empty vals      

let values_of_term = function
  | Elem (x, Glob) | Access (x, _) ->
      values_of_type (snd (Smt.Symbol.type_of x))
  | Elem (x, (Var | Constr)) -> S.singleton x
  | _ -> assert false

let sort_of_term = function
  | Elem (x, Glob) | Access (x, _) ->
      let ty = (snd (Smt.Symbol.type_of x)) in
      if Hstring.equal  ty Smt.Type.type_proc then Var
      else if Smt.Symbol.has_abstract_type x then raise Not_found
      else Constr
  | Elem (x, (Var | Constr as s)) -> s
  | _ -> assert false

let expand_cube c =
  Atom.Set.fold (fun a acc -> match a with
    | True | False -> assert false
    | Comp (x, Eq, Elem (y, (Constr|Var)))
    | Comp (Elem (y, (Constr|Var)), Eq, x) ->
        List.rev_map (Atom.Set.add a) acc
    | Comp (x, Neq, Elem (y, (Constr|Var as s)))
    | Comp (Elem (y, (Constr|Var as s)), Neq, x) ->
        (try
           let la = S.fold
             (fun v acc ->
               if Hstring.equal v y then acc
               else (Comp (x, Eq, Elem (v, s)))::acc)
             (values_of_term x) [] in
           List.fold_left (fun acc' a1 -> List.rev_append
             (List.rev_map
                (fun sa -> Atom.Set.add a1 sa) acc) acc') [] la
         with Not_found -> List.rev_map (Atom.Set.add a) acc)
        (* List.rev_map (Atom.Set.add a) acc *)
    | Comp(x, Eq, y) ->
        (try
           let s = sort_of_term x in
           let la = S.fold
             (fun v acc -> 
               (Comp (x, Eq, Elem (v, s)), Comp (y, Eq, Elem (v, s)))::acc)
             (values_of_term x) [] in
           List.fold_left (fun acc' (a1, a2) -> List.rev_append
             (List.rev_map
                (fun sa -> Atom.Set.add a2 (Atom.Set.add a1 sa)) acc) acc') [] la
         with Not_found -> List.rev_map (Atom.Set.add a) acc)
    | Comp(x, Neq, y) ->
        (try
           let s = sort_of_term x in
           let la = S.fold
             (fun v acc -> 
               (Comp (x, Neq, Elem (v, s)), Comp (y, Eq, Elem (v, s)))::acc)
             (values_of_term y) [] in
           List.fold_left (fun acc' (a1, a2) -> List.rev_append
             (List.rev_map
                (fun sa -> Atom.Set.add a2 (Atom.Set.add a1 sa)) acc) acc') [] la
         with Not_found -> List.rev_map (Atom.Set.add a) acc)           
    | _ ->  List.rev_map (Atom.Set.add a) acc
  ) c [Atom.Set.empty]


let expand_cube c = List.rev_map proper_cube (expand_cube c)



let resolve_two ar1 ar2 =
  let n1 = Array.length ar1 in
  let n2 = Array.length ar2 in
  if n1 <> n2 then None
  else
    let nb_eq = ref 0 in
    let unsat_i = ref None in
    try
      for i = 0 to n1 - 1 do
        let a1 = ar1.(i) in
        let a2 = ar2.(i) in
        if Atom.equal a1 a2 then incr nb_eq
        else if inconsistent_list [Atom.neg a1;Atom.neg  a2] then match !unsat_i with
          | Some _ -> raise Exit
          | None -> unsat_i := Some i
        else raise Exit
      done;
      match !unsat_i with
        | None -> None
        | Some i -> 
            if !nb_eq <> n1 - 1 then raise Exit;
            let ar = Array.make !nb_eq True in
            for j = 0 to !nb_eq - 1 do
              if j < i then ar.(j) <- ar1.(j)
              else ar.(j) <- ar1.(j+1)
            done;
            Some ar
    with Exit -> None

let rec add_and_resolve s visited =
  let visited =
    Cubetrie.fold (fun visited sv ->
      match resolve_two s.t_arru sv.t_arru with
        | None -> visited
        | Some ar ->
            let sa, (args, _) = proper_cube (Atom.Array.to_satom ar) in
            let ar = Atom.Array.of_satom sa in
            let aar = Atom.Array.alpha ar args in
            let s = { s with
              t_unsafe = args, sa;
              t_arru = ar;
              t_alpha = aar;
	      t_nb = new_cube_id () } in
            add_and_resolve s visited
    ) visited visited in
  Cubetrie.add_array s.t_arru s visited
