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

open Format
open Options
open Util
open Types


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
 {
   vars : Variable.t list;
   litterals : SAtom.t;
   array : ArrayAtom.t;
 }


let create vars sa =
  {
    vars = vars;
    litterals = sa;
    array = ArrayAtom.of_satom sa;
  }


let create_array vars ar =
  {
    vars = vars;
    litterals = ArrayAtom.to_satom ar;
    array = ar;
  }


let cube_false =
{
  vars = [];
  litterals = SAtom.singleton Atom.False;
  array = Array.of_list [Atom.False];
}

let subst sigma { vars = vs; array = ar } =
  let nar = ArrayAtom.apply_subst sigma ar in
  {
    vars = List.map (Variable.subst sigma) vs;
    litterals = ArrayAtom.to_satom nar;
    array = nar;
  }

(***************************************)
(* Good renaming of a cube's variables *)
(***************************************)



let normal_form ({ litterals = sa; array = ar } as c) =
  let vars = Variable.Set.elements (SAtom.variables_proc sa) in
  if !size_proc <> 0 && List.length vars > !size_proc then
    cube_false
  else
  let sigma = Variable.build_subst vars Variable.procs in
  if Variable.is_subst_identity sigma then c
  else
    let new_vars = List.map snd sigma in
    let new_ar = ArrayAtom.apply_subst sigma ar in
    let new_sa = ArrayAtom.to_satom new_ar in
    {
      vars = new_vars;
      litterals = new_sa;
      array = new_ar;
    }


let create_norma_sa_ar sa ar =
  let vars = Variable.Set.elements (SAtom.variables_proc sa) in
  if !size_proc <> 0 && List.length vars > !size_proc then
    cube_false
  else
  let sigma = Variable.build_subst vars Variable.procs in
  let new_vars = List.map snd sigma in
  let new_ar = ArrayAtom.apply_subst sigma ar in
  let new_sa = ArrayAtom.to_satom new_ar in
  {
    vars = new_vars;
    litterals = new_sa;
    array = new_ar;
  }

let create_normal sa = create_norma_sa_ar sa (ArrayAtom.of_satom sa)

let create_normal_array ar = create_norma_sa_ar (ArrayAtom.to_satom ar) ar

let dim c = List.length c.vars
let size c = Array.length c.array



(******************************************************************)
(* Simplifcation of atoms in a cube based on the hypothesis that  *)
(* indices #i are distinct and the type of elements is an	        *)
(* enumeration							                                      *)
(* 								                                                *)
(* simplify comparison atoms, according to the assumption that	  *)
(* variables are all disctincts					                          *)
(******************************************************************)

let redondant_or_false others a = match a with
  | Atom.Comp (t1, Neq, (Vea(Elem (x, (Var | Constr))) as t2))
  | Atom.Comp ((Vea(Elem (x, (Var | Constr))) as t2), Neq, t1) ->
      (try
       (SAtom.iter (function
       | Atom.Comp (t1', Eq, (Vea(Elem (x', (Var | Constr))) as t2'))
       | Atom.Comp ((Vea(Elem (x', (Var | Constr))) as t2'), Eq, t1') ->
           if Term.compare t1' t1 = 0 then
               if Term.compare t2' t2 = 0 then raise Exit
               else raise Not_found
       | _ -> ()) 
       others);
       a
       with Not_found -> Atom.True | Exit -> Atom.False)
  | Atom.Comp (t1, Eq, (Vea(Elem (x, (Var | Constr))) as t2))
  | Atom.Comp ((Vea(Elem (x, (Var | Constr))) as t2), Eq, t1) ->
      (try
       (SAtom.iter (function
       | Atom.Comp (t1', Neq, (Vea(Elem (x', (Var | Constr))) as t2'))
       | Atom.Comp ((Vea(Elem (x', (Var | Constr))) as t2'), Neq, t1') ->
         if Term.compare t1' t1 = 0 && Term.compare t2' t2 = 0 then
         raise Exit
       | Atom.Comp (t1', Eq, (Vea(Elem (x', (Var | Constr))) as t2'))
       | Atom.Comp ((Vea(Elem (x', (Var | Constr))) as t2'), Eq, t1') ->
         if Term.compare t1' t1 = 0 && Term.compare t2' t2 <> 0 then
         raise Exit
       | _ -> ()) 
       others);
       a
       with Not_found -> Atom.True | Exit -> Atom.False)
  | Atom.Comp (t1, Neq, t2) ->
      (try
       (SAtom.iter (function
         | Atom.Comp (t1', Eq, t2')
             when (Term.compare t1' t1 = 0 && Term.compare t2' t2 = 0)
               || (Term.compare t1' t2 = 0 && Term.compare t2' t1 = 0) ->
           raise Exit
         | _ -> ()) 
        others); 
        a
      with Exit -> Atom.False)
  | Atom.Comp (t1, Eq, t2) ->
      (try
       (SAtom.iter (function
         | Atom.Comp (t1', Neq, t2')
             when (Term.compare t1' t1 = 0 && Term.compare t2' t2 = 0)
               || (Term.compare t1' t2 = 0 && Term.compare t2' t1 = 0) ->
           raise Exit
         | _ -> ()) others);
        a
      with Exit -> Atom.False)
  | _ -> a

let simplify_comp i si op j sj =
  match op, (si, sj) with
    | Eq,  _ when H.equal i j -> Atom.True
    | Neq, _ when H.equal i j -> Atom.False
    | Eq, (Var, Var | Constr, Constr) ->
        if H.equal i j then Atom.True else Atom.False
    | Neq, (Var, Var | Constr, Constr) ->
        if not (H.equal i j) then Atom.True else Atom.False
    | Le, _ when H.equal i j -> Atom.True
    | Lt, _ when H.equal i j -> Atom.False
    | (Eq | Neq) , _ ->
       let ti = Vea(Elem (i, si)) in
       let tj = Vea(Elem (j, sj)) in
       if Term.compare ti tj < 0 then Atom.Comp (tj, op, ti)
       else Atom.Comp (ti, op, tj)
    | _ ->
        Atom.Comp (Vea(Elem (i, si)), op, Vea(Elem (j, sj)))

let simplify_poly cs ts =
  (* 1. Remove every null vea *)
  let ts = 
    VMap.fold
    (fun vea const acc -> 
      if not (Const.is_zero const) then VMap.add vea const acc 
                                   else acc 
    )
    ts
    VMap.empty
  in

  (* 2. Check if poly contains only one Vea *)
  if Const.is_zero cs && VMap.cardinal ts = 1 then
    let vea, c = VMap.choose ts in 
    if Const.is_one c then Vea(vea)
                      else Poly(cs, ts)
    else Poly (cs, ts)

let rec simplification np a =
  let a = redondant_or_false (SAtom.remove a np) a in
  match a with
    | Atom.Comp (Vea(Elem (i, si)), op, Vea(Elem (j, sj))) -> simplify_comp i si op j sj
    | Atom.Comp (Poly (cs1, ts1), (Eq | Le), Poly (cs2, ts2)) 
        when VMap.equal Const.equal ts1 ts2 && Const.equal cs1 cs2 ->
          Atom.True
    | Atom.Comp (Poly (cs1, ts1), (Neq | Lt), Poly (cs2, ts2)) 
        when VMap.equal Const.equal ts1 ts2 && Const.equal cs1 cs2 ->
          Atom.False
   | Atom.Comp (Poly (cs1, ts1), Le, Poly (cs2, ts2)) 
        when VMap.equal Const.equal ts1 ts2 && Const.num_le cs1 cs2 ->
          Atom.True
    | Atom.Comp (Poly (cs1, ts1), Lt, Poly (cs2, ts2)) 
        when VMap.equal Const.equal ts1 ts2 && Const.num_lt cs1 cs2 ->
          Atom.True
    | Atom.Comp (Poly (cs1, ts1), Lt, Poly (cs2, ts2)) 
        when VMap.equal Const.equal ts1 ts2 && Const.num_le cs2 cs1 ->
          Atom.False
    | Atom.Comp (Poly (cs1, ts1), Le, Poly (cs2, ts2)) 
        when VMap.equal Const.equal ts1 ts2 && Const.num_lt cs2 cs1 ->
          Atom.False
    | Atom.Ite (sa, a1, a2) ->
      let sa = 
        SAtom.fold (fun a -> SAtom.add (simplification np a)) sa SAtom.empty
      in
      let a1 = simplification np a1 in
      let a2 = simplification np a2 in
      if SAtom.is_empty sa || SAtom.subset sa np then a1
      else if SAtom.mem Atom.False sa then a2
      else a
    | Atom.Comp ((Poly _ as t1), op, (Poly _ as t2)) ->
        let t1' = 
          match term_add t1 (term_neg t2) with 
          | Poly (cs,ts) -> simplify_poly cs ts 
          | t            -> t
        in
        Atom.Comp (t1', op, Poly(Const.int_zero, VMap.empty))
    (* TODO : Comparaison entre Poly et Vea *)
    | _ -> a

(***********************************)
(* Cheap check of inconsitent cube *)
(***********************************)

let rec list_assoc_term t = function
  | [] -> raise Not_found
  | (u, v)::l -> if Term.compare t u = 0 then v else list_assoc_term t l

let assoc_neq t1 l t2 =
  try Term.compare (list_assoc_term t1 l) t2 <> 0 with Not_found -> false

let assoc_eq t1 l t2 =
  try Term.compare (list_assoc_term t1 l) t2 = 0 with Not_found -> false

let inconsistent_list l =
  let rec check values eqs neqs les lts ges gts = function
    | [] -> ()
    | Atom.True :: l -> check values eqs neqs les lts ges gts l
    | Atom.False :: _ -> raise Exit
    | Atom.Comp (t1, Eq, (Vea(Elem (x, s)) as t2)) :: l
    | Atom.Comp ((Vea(Elem (x, s)) as t2), Eq, t1) :: l ->
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
    | Atom.Comp (t1, Eq, t2) :: l ->
      if assoc_eq t1 neqs t2 || assoc_eq t2 neqs t1
      then raise Exit
      else check values ((t1, t2)::eqs) neqs les lts ges gts l
    | Atom.Comp (t1, Neq, t2) :: l ->
      if assoc_eq t1 values t2 || assoc_eq t2 values t1
	|| assoc_eq t1 eqs t2 || assoc_eq t2 eqs t1
      then raise Exit
      else check values eqs ((t1, t2)::(t2, t1)::neqs) les lts ges gts l
    | Atom.Comp (t1, Lt, t2) :: l ->
      if assoc_eq t1 values t2 || assoc_eq t2 values t1
	|| assoc_eq t1 eqs t2 || assoc_eq t2 eqs t1
	|| assoc_eq t1 ges t2 || assoc_eq t2 les t1
	|| assoc_eq t1 gts t2 || assoc_eq t2 lts t1
      then raise Exit
      else check values eqs neqs les ((t1, t2)::lts) ges ((t2, t1)::gts) l
    | Atom.Comp (t1, Le, t2) :: l ->
      if assoc_eq t1 gts t2 || assoc_eq t2 lts t1
      then raise Exit
      else check values eqs neqs ((t1, t2)::les) lts ((t2, t1)::ges) gts l
    | _ :: l -> check values eqs neqs les lts ges gts l
  in
  try check [] [] [] [] [] [] [] l; false with Exit -> true

let inconsistent_aux ((values, eqs, neqs, les, lts, ges, gts) as acc) = function
    | Atom.True  -> acc
    | Atom.False -> raise Exit
    | Atom.Comp (t1, Eq, (Vea(Elem (x, s)) as t2))
    | Atom.Comp ((Vea(Elem (x, s)) as t2), Eq, t1) ->
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
    | Atom.Comp (t1, Eq, t2) ->
      if assoc_eq t1 neqs t2 || assoc_eq t2 neqs t1
      then raise Exit
      else values, ((t1, t2)::eqs), neqs, les, lts, ges, gts
    | Atom.Comp (t1, Neq, t2) ->
      if assoc_eq t1 values t2 || assoc_eq t2 values t1
	|| assoc_eq t1 eqs t2 || assoc_eq t2 eqs t1
      then raise Exit
      else values, eqs, ((t1, t2)::(t2, t1)::neqs), les, lts, ges, gts
    | Atom.Comp (t1, Lt, t2) ->
      if assoc_eq t1 values t2 || assoc_eq t2 values t1
	|| assoc_eq t1 eqs t2 || assoc_eq t2 eqs t1
	|| assoc_eq t1 ges t2 || assoc_eq t2 les t1
	|| assoc_eq t1 gts t2 || assoc_eq t2 lts t1
      then raise Exit
      else values, eqs, neqs, les, ((t1, t2)::lts), ges, ((t2, t1)::gts)
    | Atom.Comp (t1, Le, t2) ->
      if assoc_eq t1 gts t2 || assoc_eq t2 lts t1
      then raise Exit
      else values, eqs, neqs, ((t1, t2)::les), lts, ((t2, t1)::ges), gts
    | _  -> acc


let inconsistent_list =
  if not profiling then inconsistent_list
  else fun l ->
       TimeSimpl.start ();
       let r = inconsistent_list l in
       TimeSimpl.pause ();
       r

let inconsistent_aux =
  if not profiling then inconsistent_aux
  else fun acc a ->
       try
         TimeSimpl.start ();
         let r = inconsistent_aux acc a in
         TimeSimpl.pause ();
         r
       with Exit ->
         TimeSimpl.pause ();
         raise Exit

let inconsistent sa =
  let l = SAtom.elements sa in
  inconsistent_list l

let inconsistent_array a =
  let l = Array.to_list a in
  inconsistent_list l


let inconsistent_set sa =
  try
    let _ =
      SAtom.fold (fun a acc -> inconsistent_aux acc a)
	sa ([], [], [], [], [], [], []) in
    false
  with Exit -> true


let inconsistent_array ar =
  try
    TimeFormula.start ();
    let _ = Array.fold_left inconsistent_aux ([], [], [], [], [], [], []) ar in
    TimeFormula.pause ();
    false
  with Exit -> TimeFormula.pause (); true

let inconsistent_2arrays ar1 ar2 =
  try
    let acc =
      Array.fold_left inconsistent_aux ([], [], [], [], [], [], []) ar1 in
    let _ = Array.fold_left inconsistent_aux acc ar2 in
    false
  with Exit -> true


let inconsistent_2sets sa1 sa2 =
  try
    let acc = SAtom.fold
      (fun a acc -> inconsistent_aux acc a)
      sa1 ([], [], [], [], [], [], []) in
    let _ = SAtom.fold
      (fun a acc -> inconsistent_aux acc a)
      sa2 acc in
    false
  with Exit -> true

let inconsistent ?(use_sets=false) { litterals = sa; array = ar } =
  if use_sets then inconsistent_set sa
  else inconsistent_array ar

let inconsistent_2 ?(use_sets=false)
    { litterals = sa1; array = ar1 } { litterals = sa2; array = ar2 } =
  if use_sets then inconsistent_2sets sa1 sa2
  else inconsistent_2arrays ar1 ar2

let simplification_atoms base sa =
  SAtom.fold
    (fun a sa ->
       let a = simplification base a in
       let a = simplification sa a in
       match a with
       | Atom.True -> sa
       | Atom.False -> raise Exit
       | _ -> SAtom.add a sa
    )
    sa SAtom.empty

let rec break a =
  match a with
    | Atom.True | Atom.False | Atom.Comp _ -> [SAtom.singleton a]
    | Atom.Ite (sa, a1, a2) ->
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

let elim_ite_atoms np =
  try
    let ites, base = SAtom.partition (function Atom.Ite _ -> true | _ -> false) np in
    let base = simplification_atoms SAtom.empty base in
    let ites = simplification_atoms base ites in
      SAtom.fold
      (fun ite cubes ->
         List.fold_left
           (fun acc sa ->
            List.fold_left
            (fun sa_cubes cube ->
             try
               let sa = simplification_atoms cube sa in
               let sa = SAtom.union sa cube in
               if inconsistent_set sa then sa_cubes 
                                      else add_without_redondancy sa sa_cubes
             with Exit -> sa_cubes
            )
          acc cubes
          )
           []
           (break ite)
    )
	ites
	[base]
  with Exit -> []


let simplify { litterals = sa; } =
  create_normal (simplification_atoms SAtom.empty sa)

let elim_ite_simplify { litterals = sa; } =
  List.map create_normal (elim_ite_atoms sa)

let simplify_atoms_base = simplification_atoms
let simplify_atoms sa = simplification_atoms SAtom.empty sa
let elim_ite_simplify_atoms = elim_ite_atoms


let resolve_two_arrays ar1 ar2 =
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
        else if inconsistent_list [Atom.neg a1;Atom.neg  a2] then
          match !unsat_i with
          | Some _ -> raise Exit
          | None -> unsat_i := Some i
        else raise Exit
      done;
      match !unsat_i with
        | None -> None
        | Some i ->
            if !nb_eq <> n1 - 1 then raise Exit;
            let ar = Array.make !nb_eq Atom.True in
            for j = 0 to !nb_eq - 1 do
              if j < i then ar.(j) <- ar1.(j)
              else ar.(j) <- ar1.(j+1)
            done;
            Some ar
    with Exit -> None


let resolve_two c1 c2 =
  match resolve_two_arrays c1.array c2.array with
  | None -> None
  | Some ar -> Some (create_normal_array ar)

let term_vea t acc = 
  match t with  
  | Vea.Elem (a, Glob) | Vea.Access (a, _) -> Term.Set.add (Vea t) acc
  | _ -> acc

let rec term_globs t acc = 
  match t with 
  | Vea vea       -> term_vea vea acc
  | Poly (_, vm)  -> VMap.fold (fun vea _ acc -> term_vea vea acc) vm acc

let rec atom_globs a acc = match a with
    | Atom.True | Atom.False -> acc
    | Atom.Comp (t1, _, t2) -> term_globs t1 (term_globs t2 acc)
    | Atom.Ite (sa, a1, a2) ->
       Term.Set.union (satom_globs sa) (atom_globs a1 (atom_globs a2 acc))

and satom_globs sa = SAtom.fold atom_globs sa Term.Set.empty


let print fmt { litterals = sa } = SAtom.print fmt sa
