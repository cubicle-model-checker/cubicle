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

module H = Hstring
module S = H.HSet
let hempty = H.make ""


module TimeRP = Search.TimeRP

module TimeFix = Search.TimeFix
module TimeEasyFix = Search.TimeEasyFix
module TimeHardFix = Search.TimeHardFix

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
    | Comp (Access (a, _, _), _, Elem (x, xs)) -> 
	if xs = Glob || xs = Constr then
	  SS.add (a, x) s 
	else SS.add (a, hempty) s
    | Comp (_, _, Access (a, _, _)) -> SS.add (a, hempty) s
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
  | ConstName n -> 
    Hstring.equal (snd (Smt.Symbol.type_of n)) Smt.Type.type_int

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
    | (Eq | Neq) , _ -> 
        let ti = Elem (i, si) in
	let tj = Elem (j, sj) in 
	if compare_term ti tj < 0 then Comp (tj, op, ti)
	else Comp (ti, op, tj)
    | _ -> Comp (Elem (i, si), op, Elem (j, sj))

let rec simplification np a =
  let a = redondant_or_false (SAtom.remove a np) a in
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
    | Comp (Const _ as c, Eq, y) -> Comp (y, Eq, c)
    | Comp (x, Eq, y) when compare_term x y = 0 -> True
    | Comp (x, (Eq | Neq as op), y) when compare_term x y < 0 -> Comp (y, op, x)
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
    if profiling then Prover.TimeF.start ();
    let _ = Array.fold_left inconsistent_aux ([], [], [], [], [], [], []) ar in
    if profiling then Prover.TimeF.pause ();
    false
  with Exit -> if profiling then Prover.TimeF.pause (); true

let inconsistent_2arrays ar1 ar2 =
  try
    let acc = 
      Array.fold_left inconsistent_aux ([], [], [], [], [], [], []) ar1 in
    let _ = Array.fold_left inconsistent_aux acc ar2 in
    false
  with Exit -> true


let inconsistent_2cubes sa1 sa2 =
  try
    let acc = SAtom.fold 
      (fun a acc -> inconsistent_aux acc a) 
      sa1 ([], [], [], [], [], [], []) in
    let _ = SAtom.fold 
      (fun a acc -> inconsistent_aux acc a) 
      sa2 acc in
    false
  with Exit -> true



(*----------------------------------------------------------------*)

let inconsistencies ap other =
  if inconsistent_2arrays ap other then
    Array.fold_left (fun acc a ->
      let sa = SAtom.singleton a in
      Array.fold_left (fun acc o -> 
	let so = SAtom.singleton o in
	if inconsistent_2cubes sa so then a :: acc
	else acc) acc other
    ) [] ap
  else []

let distrib_one l acc x =
  List.fold_left (fun acc y ->
    let n = SAtom.add y x in 
    if List.mem n acc then acc else n :: acc) acc l

let distrib_cand l1 l2 =
  List.fold_left (distrib_one l1) [] l2


let rec fold_candidates_rec acc ap = function
  | [] -> List.sort SAtom.compare acc
  | fp :: fs ->
      (* XXX *)
      let incs = inconsistencies ap fp in
      (* eprintf "inconsistencies %a >>> %a === @." *)
      (* 	Pretty.print_array ap Pretty.print_array fp; *)
      (* List.iter (fun a -> eprintf "%a\n----@." *)
      (* 	Pretty.print_atom a) incs; *)
      if incs = [] then raise Exit;
      (* let sfp = ArrayAtom.to_satom fp in *)
      (* List.rev_append  *)
      (* 	(List.rev_map (fun inc -> SAtom.add inc acc) incs) *)
      (* 	(fold_candidates ap fs) *)
      fold_candidates_rec (distrib_cand incs acc) ap fs

let fold_candidates = fold_candidates_rec [SAtom.empty]

let simple_extract_candidates ap forward_nodes =
  List.fold_left (fun acc fs ->
    try
      let cs = 
	List.fold_left (fun acc c ->
	  (* eprintf "fold_cand %a @." Pretty.print_cube c; *)
	  if SAtom.cardinal c > 1 then c :: acc else acc
	) [] (fold_candidates ap fs) in
      cs @ acc
    with Exit -> acc)
    [] forward_nodes

(*----------------------------------------------------------------*)



let number_of s = 
  if s.[0] = '#' then 
    int_of_string (String.sub s 1 (String.length s - 1))
  else 1

let rec add_arg args = function
  | Elem (s, _) | Access (_, s ,_) ->
      let s' = H.view s in
      if s'.[0] = '#' || s'.[0] = '$' then S.add s args else args
  | Arith (t, _) -> add_arg args t
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
	     subst_atoms [arg, List.nth proc_vars (!cpt - 1)] sa in 
	   incr cpt; sa)
      sa args
  in
  let l = ref [] in
  for n = !cpt - 1 downto 1 do 
    l := (List.nth proc_vars (n - 1)) :: !l
  done;
  if profiling then TimerApply.pause ();
  sa, (!l, List.nth proc_vars (!cpt - 1))


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
	let acc = 
	  if acc = [] then [[x,y]]
	  else List.map (fun ds -> (x, y)::ds) acc in
	acc@(cross l (y::pr) x p)

let rec all_parts l = match l with
  | [] -> []
  | x::r -> let pr = all_parts r in
	    [x]::pr@(List.map (fun p -> x::p) pr)

let all_parts_elem l = List.map (fun x -> [x]) l

let rec all_partial_permutations l1 l2 =
  List.flatten (
    List.fold_left (fun acc l -> (all_permutations l l2)::acc) [] (all_parts l1)
  )


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
      | Comp (Access (a2, _, _), _, _), _ when not (H.equal a1 a2) ->
	  i2 := n2

      | Comp (Access (a2, x2, _), Eq,
	      (Elem (_, Constr) | Elem (_, Glob) | Arith _ as c2)), (Neq | Lt)
	  when compare_term c1 c2 = 0 ->
	  
	  if H.list_mem_couple (x1, x2) obvs then raise NoPermutations;
	  impos := (x1, x2) :: !impos
	    
      | Comp (Access (a2, x2, _), (Neq | Lt),
	      (Elem (_, Constr) | Elem (_, Glob) | Arith _ as c2)), Eq
	  when compare_term c1 c2 = 0 ->
	  
	  if H.list_mem_couple (x1,x2) obvs then raise NoPermutations;
	  impos := (x1, x2) :: !impos

      | Comp (Access (a2, x2, _), Eq, (Elem (_, Constr) as c2)), Eq 
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
       | Comp (Access (a1, x1, Var), op, 
	       (Elem (_, Constr) | Elem (_, Glob) | Arith _ as c1)), 
	 Comp (Access (a, _,Var), _, (Elem (_, Constr) | Elem (_, Glob) | Arith _ ))
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
    | Arith (v, m) ->
	begin
	  try
	    let c = MConst.find tick m in
	    if c > 0 then 
	      let m = MConst.remove tick m in
	      let e = 
		if MConst.is_empty m then v else Arith(v, m)
	      in
	      simplification SAtom.empty (Comp (e, Lt, x))
	    else raise Not_found
	  with Not_found -> Comp (e, op, x)
	end	
    | _ -> assert false
      

let contains_tick_term tick = function
  | Const m | Arith (_, m) ->
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
      | Comp ((Const _ | Arith (_, _) as e), (Le|Lt|Eq as op), x)
      | Comp (x, (Eq as op), (Const _ | Arith (_, _) as e))  ->
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
  	        let nc = List.map Atom.neg c in
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
	if not quiet then eprintf "\nUnsafe trace: @[%a@]@." 
	  Pretty.print_verbose_node s;
	raise (Search.Unsafe s)
      end
  with
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
    let tr_margs = H.H.find closed tr in
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
  with Search.Unsafe _ -> false
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
	try H.H.find closed tr with Not_found -> MArgs.empty in
      let ls = try MArgs.find args tr_margs with Not_found -> [] in
      H.H.add closed tr (MArgs.add args ((simpl, fix) :: ls) tr_margs)

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

let check_fixpoint ({t_unsafe = (nargs, _); t_arru = anp} as s) visited =
  Prover.assume_goal s;
  (* let nb_nargs = List.length nargs in *)
  let nodes = List.fold_left
    (fun nodes ({ t_alpha = args, ap; t_unsafe = real_args, _ } as sp) ->
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
	    raise (Fixpoint [sp.t_nb])
	  end
	  (* Heuristic : throw away nodes too much different *)
	  (* else if ArrayAtom.nb_diff pp anp > 2 then nodes *)
	  (* line below useful for arith : ricart *)
	  else if inconsistent_array (ArrayAtom.union pp anp) then nodes
	  else if ArrayAtom.nb_diff pp anp > 1 then (pp,sp.t_nb)::nodes
	  else (Prover.assume_node pp ~id:sp.t_nb; nodes)
	) nodes d
    ) [] visited
  in
  if profiling then TimeSort.start ();
  let nodes = 
    List.fast_sort 
      (fun (a1, n1) (a2, n2) -> ArrayAtom.compare_nb_common anp a1 a2) 
      nodes 
  in
  if profiling then TimeSort.pause ();
  List.iter (fun (p, cnum) -> Prover.assume_node p ~id:cnum) nodes
  

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
  if (delete && (s.t_deleted || has_deleted_ancestor s))
    ||
    (simpl_by_uc && has_alredy_closed_ancestor s)
  then Some []
  else
    let db = ref None in
    ignore (List.exists 
	      (fun ({ t_arru = pa } as sp) -> 
		 if ArrayAtom.subset pa npa then
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
  

let fixpoint ~invariants ~visited ({ t_unsafe = (_,np) } as s) =
  Debug.unsafe s;
  if profiling then TimeFix.start ();
  let nodes = (List.rev_append invariants visited) in
  let r = 
    match easy_fixpoint s nodes with
      | None -> hard_fixpoint s nodes
      | r -> r
  in
  if profiling then TimeFix.pause ();
  r



let size_system s = List.length (fst s.t_unsafe)
let card_system s = SAtom.cardinal (snd s.t_unsafe)


  

let all_var_terms procs {t_globals = globals; t_arrays = arrays} =
  let acc, gp = 
    List.fold_left 
      (fun (acc, gp) g -> 
	STerm.add (Elem (g, Glob)) acc,
	(* if Smt.Typing.has_type_proc g && Hstring.view g = "Home" then g :: gp *)
	(* else *) gp
      ) (STerm.empty, []) globals
  in
  List.fold_left (fun acc p ->
    List.fold_left (fun acc a ->
      STerm.add (Access (a, p, Var)) acc)
      acc arrays)
    acc (procs@gp)



(*************** Things with tries *******************)

let invert_subst = List.map (fun (x,y) -> y,x)

let medium_fixpoint_trie {t_unsafe = (nargs,_); 
                          t_alpha = args, ap; 
                          t_arru = anp} visited learnt =
  if profiling then TimeEasyFix.start ();
  let substs = all_permutations args nargs in
  let substs = List.tl substs in (* Drop 'identity' permutation. 
                                    Already checked in easy_fixpoint. *)
  try
    List.iter (fun ss -> 
      let u = ArrayAtom.apply_subst ss ap in
      let lstu = Array.to_list u in
      match Cubetrie.mem lstu !visited with
        | Some uc -> raise (Fixpoint uc)
        | None -> match Cubetrie.mem lstu !learnt with
            | Some uc -> raise (Fixpoint uc)
            | None -> ()
    ) substs;
    if profiling then TimeEasyFix.pause ();
    None
  with Fixpoint uc -> 
    if profiling then TimeEasyFix.pause ();
    Some uc

let hard_fixpoint_trie s visited learnt =
  if profiling then TimeHardFix.start (); 
  let anp = s.t_arru in
  let nargs = fst s.t_unsafe in
  let substs = all_permutations nargs nargs in
  let relevant ss =
    let u = ArrayAtom.apply_subst ss anp in
    let lstu = Array.to_list u in
    let nodes = Cubetrie.consistent lstu !visited in
    let nodes = List.filter (fun s -> not (s.t_deleted)) nodes in
    let ss' = invert_subst ss in
    List.map (fun n -> 
      let p = ArrayAtom.apply_subst ss' n.t_arru in
      (p, n.t_nb), ArrayAtom.nb_diff p u
    ) nodes
  in
  let cubes = List.flatten (List.map relevant substs) in
  let res = 
    if cubes = [] then None
    else begin
      if profiling then TimeSort.start ();
      let cubes =
        List.fast_sort
          (fun c1 c2 -> Pervasives.compare (snd c1) (snd c2))
          cubes
      in
        if profiling then TimeSort.pause ();
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
  if profiling then TimeHardFix.pause ();
  res


let delete_node s  = s.t_deleted <- true


let fixpoint_trie s lstu visited learnt postponed =
  if profiling then begin TimeFix.start (); TimeEasyFix.start () end;
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
  if profiling then TimeEasyFix.pause ();
  let res = 
    match res with 
      | Some _ -> res
      | None -> match medium_fixpoint_trie s visited learnt with
          | (Some _) as r -> r
          | None -> hard_fixpoint_trie s visited learnt
  in
  if profiling then TimeFix.pause ();
  res
