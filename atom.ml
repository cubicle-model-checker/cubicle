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

open Util
module HSet = Hstring.HSet


module rec Type = struct  
  type t =
    | True
    | False
    | Comp of term * op_comp * term
    | Ite of SAtom.t * t * t
end
and Atom = struct
  
  include Type

  let rec compare a1 a2 = 
    match a1, a2 with
      | True, True -> 0
      | True, _ -> -1 | _, True -> 1
      | False, False -> 0
      | False, _ -> -1 | _, False -> 1
      | Comp (x1, op1, y1), Comp (x2, op2, y2) ->
	  let c1 = compare_term x1 x2 in
	  if c1 <> 0  then c1 
	  else 
	    let c0 = Pervasives.compare op1 op2 in
	    if c0 <> 0 then c0 
	    else 
	      let c2 = compare_term y1 y2 in c2
      | Comp _, _ -> -1 | _, Comp _ -> 1
      | Ite (sa1, a1, b1), Ite (sa2, a2, b2) ->
	  let c = SAtom.compare sa1 sa2 in
	  if c<>0 then c else 
	    let c = compare a1 a2 in
	    if c<>0 then c else compare b1 b2

  let trivial_is_implied a1 a2 =
    match a1, a2 with
      | Comp (x1, Neq, Elem (v1, (Constr|Var))),
        Comp (x2, Eq, Elem (v2, (Constr|Var))) 
          when not (Hstring.equal v1 v2) && compare_term x1 x2 = 0 -> 0
      | _ -> compare a1 a2

  let neg = function
    | True -> False
    | False -> True
    | Comp (c, Eq, (Elem (x, Constr))) when Hstring.equal x hfalse -> 
	Comp (c, Eq, (Elem (htrue, Constr)))
    | Comp (c, Eq, (Elem (x, Constr))) when Hstring.equal x htrue -> 
	Comp (c, Eq, (Elem (hfalse, Constr)))
    | Comp (x, Eq, y) -> Comp (x, Neq, y)
    | Comp (x, Lt, y) -> Comp (y, Le, x)
    | Comp (x, Le, y) -> Comp (y, Lt, x)
    | Comp (x, Neq, y) -> Comp (x, Eq, y)
    | _ -> assert false

  let hash (sa: Atom.t) = Hashtbl.hash_param 50 100 sa

  let equal x y = compare x y = 0

  let subst sigma ?(sigma_sort=[]) a = 
    match a with
    | Ite (sa, a1, a2) ->
       Ite(SAtom.subst sigma ~sigma_sort sa, 
           subst sigma ~sigma_sort a1, 
           subst sigma ~sigma_sort a2)
    | Comp (x, op, y) -> 
       let sx = Term.subst_term sigma ~sigma_sort x in
       let sy = Term.subst sigma ~sigma_sort y in
       Comp(sx, op, sy)
    | _ -> a

  let rec contain_arg z = function
    | Elem (x, _) -> Hstring.equal x z
    | Access (_, lx) -> Hstring.list_mem z lx
    | Arith (t, _) -> contain_arg z t
    | Const _ -> false

  let has_var z = function
    | True | False -> false
    | Comp (t1, _, t2) -> (contain_arg z t1) || (contain_arg z t2)
    | Ite _ -> assert false

  let rec variables acc = function
    | True | False -> acc
    | Comp (t1, _, t2) -> Term.variables (Term.variables acc t1) t2
    | Ite (sa, a1, a2) -> SAtom.variables (variables (variables acc a1) a2) sa

end

and SAtom = struct 
    
  include Set.Make(Atom)

  let add a s = 
    match a with
    | Atom.True -> s
    | Atom.False -> SAtom.singleton Atom.False
    | _ -> if SAtom.mem Atom.False s then s else SAtom.add a s


  let equal sa1 sa2 = compare sa1 sa2 = 0

  let hash (sa:t) = Hashtbl.hash_param 100 500 sa

  let subst sigma ?(sigma_sort=[]) sa = 
  fold (fun a -> add (Atom.subst sigma ~sigma_sort a)) sa empty

  let variables acc sa = fold (fun a acc -> Atom.variables acc a) sa acc
                             

  let rec term_globs t acc = match t with
    | Elem (a, Glob) | Access (a, _) -> Term.Set.add t acc
    | Arith (x, _) -> terms_globs x acc
    | _ -> acc

  let rec atom_globs a acc = match a with
    | True | False -> acc
    | Comp (t1, _, t2) -> term_globs t1 (term_globs t2 acc) 
    | Ite (sa, a1, a2) -> 
       Term.Set.union (glob_terms sa) (atom_globs a1 (atom_globs a2 acc))

  and glob_terms sa = fold atom_globs sa Term.Set.empty

end


module ArrayAtom = struct

  type t = Atom.t array

  let equal a1 a2 =
    let n = Array.length a1 in
    let n2 = Array.length a2 in
    if n <> n2 then false
    else
      let res = ref true in
      let i = ref 0 in 
      while !res && !i < n  do
	res := (Atom.compare a1.(!i) a2.(!i) = 0);
	incr i
      done;
      !res

  let hash = Hashtbl.hash_param 100 500

  let subset a1 a2 =
    if profiling then TimerSubset.start ();
    let n1 = Array.length a1 in
    let n2 = Array.length a2 in
    let s = 
      if n1 > n2 then false
      else
	let i1 = ref 0 in 
	let i2 = ref 0 in
	while !i1 < n1 && !i2 < n2 do
	  let c = Atom.compare a1.(!i1) a2.(!i2) in
	  if c = 0 then (incr i1; incr i2)
	  else if c < 0 then i2 := n2
	  else incr i2
	done;
	!i1 = n1
    in
    if profiling then TimerSubset.pause ();
    s

  let trivial_is_implied a1 a2 =
    if profiling then TimerSubset.start ();
    let n1 = Array.length a1 in
    let n2 = Array.length a2 in
    let s = 
      if n1 > n2 then false
      else
	let i1 = ref 0 in 
	let i2 = ref 0 in
	while !i1 < n1 && !i2 < n2 do
	  let c = Atom.trivial_is_implied a1.(!i1) a2.(!i2) in
	  if c = 0 then (incr i1; incr i2)
	  else if c < 0 then i2 := n2
	  else incr i2
	done;
	!i1 = n1
    in
    if profiling then TimerSubset.pause ();
    s

  let subset = trivial_is_implied

  let of_satom s =
    Array.of_list (SAtom.elements s)

  let to_satom =
    Array.fold_left (fun s a -> SAtom.add a s) SAtom.empty

  let union = Array.append 
    (* let a = Array.append a1 a2 in *)
    (* Array.fast_sort Atom.compare a; a *)

  let apply_subst sigma a =
    if profiling then TimerApply.start ();
    let a' = Array.init (Array.length a) (fun i -> subst_atom sigma a.(i)) in
    Array.fast_sort Atom.compare a';
    if profiling then TimerApply.pause ();
    a'

  let alpha atoms args =
    let subst = Variable.build_subst args alpha_vars in
    List.map snd subst, apply_subst subst atoms

  let nb_diff a1 a2 =
    if profiling then TimerSubset.start ();
    let cpt = ref 0 in
    let n1 = Array.length a1 in
    let n2 = Array.length a2 in
    let i1 = ref 0 in 
    let i2 = ref 0 in
    while !i1 < n1 && !i2 < n2 do
      let c = Atom.compare a1.(!i1) a2.(!i2) in
      if c = 0 then (incr i1; incr i2)
      else if c < 0 then (incr cpt; incr i1)
      else incr i2
    done;
    if profiling then TimerSubset.pause ();
    !cpt + (n1 - !i1)

  let compare_nb_diff a p1 p2 =
    Pervasives.compare (nb_diff p1 a) (nb_diff p2 a)


  let nb_common a1 a2 =
    if profiling then TimerSubset.start ();
    let cpt = ref 0 in
    let n1 = Array.length a1 in
    let n2 = Array.length a2 in
    let i1 = ref 0 in 
    let i2 = ref 0 in
    while !i1 < n1 && !i2 < n2 do
      let c = Atom.compare a1.(!i1) a2.(!i2) in
      if c = 0 then (incr cpt; incr i1; incr i2)
      else if c < 0 then incr i1
      else incr i2
    done;
    if profiling then TimerSubset.pause ();
    (float_of_int !cpt) /. (float_of_int n1)


  let compare_nb_common a p1 p2 =
    Pervasives.compare (nb_common p2 a) (nb_common p1 a)

  let diff a1 a2 =
    let n1 = Array.length a1 in
    let n2 = Array.length a2 in
    let i1 = ref 0 in 
    let i2 = ref 0 in
    let cpt = ref 0 in
    let d = Array.copy a1 in
    while !i1 < n1 && !i2 < n2 do
      let ai1 = a1.(!i1) in
      let c = Atom.compare ai1 a2.(!i2) in
      if c = 0 then (incr i1; incr i2)
      else if c < 0 then begin
	d.(!cpt) <- ai1;
	incr cpt;
	incr i1
      end
      else incr i2
    done;
    while !i1 < n1 do
      d.(!cpt) <- a1.(!i1);
      incr cpt;
      incr i1
    done;
    Array.sub d 0 !cpt

end


include Atom


module Set : sig 

  include Set.S with type elt = Atom.t

  val equal : t -> t -> bool
  val hash : t -> int
  val subst : Variables.subst -> ?sigma_sort:Term.subst_sort -> t -> t
  val variables : t -> Variables.Set.t
  val glob_terms : t -> Term.Set.t

end = struct
  
  include SAtom

  let subst sigma ?(sigma_sort=[]) sa =
    if profiling then TimerApply.start ();
    let sa = subst sigma ~sigma_sort sa in
    if profiling then TimerApply.pause ();
    sa

end


(* type aliases for convenience *)

type array = Array.t

type set = Set.t
