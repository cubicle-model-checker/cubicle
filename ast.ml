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

open Options

exception ReachBound

type op_comp = Eq | Lt | Le | Neq
type op_arith = Plus | Minus

type sort = Glob | Arr | Constr | Var

type const = ConstInt of Num.num | ConstReal of Num.num | ConstName of Hstring.t

let compare_const c1 c2 = match c1, c2 with
  | (ConstInt n1 | ConstReal n1), (ConstInt n2 | ConstReal n2) ->
      Num.compare_num n1 n2
  | (ConstInt _ | ConstReal _), _ -> -1
  | _, (ConstInt _ | ConstReal _) -> 1
  | ConstName h1, ConstName h2 -> Hstring.compare h1 h2

module MConst = struct 
  module M = Map.Make (struct type t = const let compare = compare_const end)
  include M

  exception Choose of const * int
  let choose m =
    try
      M.iter (fun c i -> raise (Choose (c, i))) m;
      raise Not_found
    with Choose (c, i) -> c, i

end

let compare_constants = MConst.compare Pervasives.compare 

type term = 
  | Const of int MConst.t
  | Elem of Hstring.t * sort
  | Access of Hstring.t * Hstring.t list
  | Arith of term * int MConst.t

let rec compare_term t1 t2 = 
  match t1, t2 with
    | Const c1, Const c2 -> compare_constants c1 c2
    | Const _, _ -> -1 | _, Const _ -> 1
    | Elem (_, (Constr | Var)), Elem (_, (Glob | Arr)) -> -1
    | Elem (_, (Glob | Arr)), Elem (_, (Constr | Var)) -> 1
    | Elem (s1, _), Elem (s2, _) -> Hstring.compare s1 s2
    | Elem _, _ -> -1 | _, Elem _ -> 1
    | Access (a1, l1), Access (a2, l2) ->
	let c = Hstring.compare a1 a2 in
	if c<>0 then c else Hstring.compare_list l1 l2
    | Access _, _ -> -1 | _, Access _ -> 1 
    | Arith (t1, cs1), Arith (t2, cs2) ->
	let c = compare_term t1 t2 in
	if c<>0 then c else compare_constants cs1 cs2

let rec hash_term = function
  | Const c -> Hashtbl.hash c
  (* | Elem (_, Var) -> 31 *)
  | Elem (s, _) -> Hstring.hash s
  | Access (a, lx) -> 
      List.fold_left (fun acc x -> acc * Hstring.hash x (* * 29 *))
        (Hstring.hash a) lx
  | Arith (x, c) -> hash_term x + Hashtbl.hash c

let htrue = Hstring.make "True"
let hfalse = Hstring.make "False"

type acc_eq = { a : Hstring.t; i: Hstring.t; e: term }

module rec Atom : sig

  type t =
    | True
    | False
    | Comp of term * op_comp * term
    | Ite of SAtom.t * t * t

  val compare : t -> t -> int
  val trivial_is_implied : t -> t -> int
  val neg : t -> t
  val hash : t -> int
  val equal : t -> t -> bool

end = struct
  
  type t =
    | True
    | False
    | Comp of term * op_comp * term
    | Ite of SAtom.t * t * t

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

  let rec hash = function
    | True -> 7 | False -> 11
    | Comp (x, Eq, y) -> 7 * (hash_term x * hash_term y)
    | Comp (x, Neq, y) -> 13 * (hash_term x * hash_term y)
    | Comp (x, Le, y) -> 5 * hash_term x * 7 * hash_term y
    | Comp (x, Lt, y) -> 5 * hash_term x * 11 * hash_term y
    | Ite (sa, a1, a2) -> SAtom.hash sa + (7 * hash a1) + (11 * hash a2)
  and hash_set sa = SAtom.fold (fun a acc -> hash a + acc) sa 0

  let equal x y = compare x y = 0

end

and SAtom : sig 

  include Set.S with type elt = Atom.t

  val equal : t -> t -> bool
  val hash : t -> int

end = struct 
    
  include Set.Make(Atom)

  let equal sa1 sa2 = compare sa1 sa2 = 0

  let hash sa =
    let _, h = fold (fun a (n,acc) -> n + 1, n + Atom.hash a * acc)
      sa (2,1) in
    h (* mod 1_000_000 *)
end

let gen_vars s n = 
  let l = ref [] in
  for i = 1 to max_proc do
    l := Hstring.make (s^(string_of_int i)) :: !l
  done;
  List.rev !l

let alpha_vars = gen_vars "$" max_proc
let proc_vars = gen_vars "#" max_proc
let fresh_vars = gen_vars "?" max_proc
let proc_vars_int = 
  let l = ref [] in
  for i = 1 to max_proc do
    l := i :: !l
  done;
  List.rev !l

let add a s = 
  match a with
    | Atom.True -> s
    | Atom.False -> SAtom.singleton Atom.False
    | _ -> if SAtom.mem Atom.False s then s else SAtom.add a s

  (* Substitute an indice variable j by i in a set of atoms *)

let svar sigma v = Hstring.list_assoc v sigma

let ssort sigma_sort s = try List.assoc s sigma_sort with Not_found -> s
    
let rec subst_term sigma ?(sigma_sort=[]) t = 
  match t with
    | Elem (x, s) -> 
	(try Elem (svar sigma x, ssort sigma_sort s) with Not_found -> t)
    | Access (a, lz) -> 
	Access (a, List.map
          (fun z ->
            try svar sigma z with Not_found -> z) lz)
    | Arith (x, c) -> Arith (subst_term sigma ~sigma_sort x, c)
    | _ -> t
	

module TimerSubset = Timer.Make (struct end)

module TimerApply = Timer.Make (struct end)

open Atom

let rec subst_atoms sigma ?(sigma_sort=[]) sa = 
  SAtom.fold (fun a -> add (subst_atom sigma ~sigma_sort a)) sa SAtom.empty
and subst_atom sigma ?(sigma_sort=[]) a = 
  match a with
    | Ite (sa, a1, a2) ->
	Ite(subst_atoms sigma ~sigma_sort sa, 
            subst_atom sigma ~sigma_sort a1, 
            subst_atom sigma ~sigma_sort a2)
    | Comp (x, op, y) -> 
	let sx = subst_term sigma ~sigma_sort x in
	let sy = subst_term sigma ~sigma_sort y in
	Comp(sx, op, sy)
    | _ -> a


let subst_atoms sigma ?(sigma_sort=[]) sa =
  if profiling then TimerApply.start ();
  let sa = subst_atoms sigma ~sigma_sort sa in
  if profiling then TimerApply.pause ();
  sa


let build_subst args a_args =
  let rec a_subst acc args a_args =
    match args, a_args with
      | [], _ -> acc
      | x::args, ax::a_args ->
	a_subst ((x, ax)::acc) args a_args
      | _ -> assert false
  in
  a_subst [] args a_args


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

  let hash ar = 
    let _, h = Array.fold_left (fun (n,acc) a -> n+1,  n + Atom.hash a * acc)
      (2,1) ar in
    h

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
    let subst = build_subst args alpha_vars in
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


type update = {
  up_arr : Hstring.t;
  up_arg : Hstring.t list;
  up_swts : (SAtom.t * term) list;
}

type transition = {
  tr_name : Hstring.t;
  tr_args : Hstring.t list;
  tr_reqs : SAtom.t;
  tr_ureq : (Hstring.t * SAtom.t list) list;
  tr_assigns : (Hstring.t * term) list;
  tr_upds : update list;
  tr_nondets : Hstring.t list;
}

type elem = Hstring.t * (Hstring.t list)

type system = {
  globals : (Hstring.t * Hstring.t) list;
  consts : (Hstring.t * Hstring.t) list;
  arrays : (Hstring.t * (Hstring.t list * Hstring.t)) list;
  type_defs : elem list;
  init : Hstring.t list * SAtom.t list;
  invs : (Hstring.t list * SAtom.t) list;
  cands : (Hstring.t list * SAtom.t) list;
  unsafe : (Hstring.t list * SAtom.t) list;  
  forward : (Hstring.t list * Hstring.t list * SAtom.t) list;
  trans : transition list
}

module STerm = Set.Make (struct type t = term let compare = compare_term end)

(* Typed AST *)

type t_system = {
  t_globals : Hstring.t list;
  t_arrays : Hstring.t list;
  t_from : (transition * Hstring.t list * t_system) list;
  t_init : Hstring.t list * SAtom.t list;
  t_invs : (Hstring.t list * SAtom.t) list;
  t_cands : (Hstring.t list * SAtom.t) list;
  t_unsafe : Hstring.t list * SAtom.t;
  t_forward : (Hstring.t list * Hstring.t list * SAtom.t) list;
  t_arru : ArrayAtom.t;
  t_alpha : Hstring.t list * ArrayAtom.t;
  t_trans : transition list;
  mutable t_deleted : bool;
  t_nb : int;
  t_nb_father : int;
  t_glob_proc : Hstring.t list;
}

let declared_term x =
  match x with
    | Elem (_, Var) -> true
    | Elem (s, _) | Access (s, _) -> Smt.Symbol.declared s
    | _ -> true

let declared_terms ar =
  Array.fold_left
  (fun acc -> function
    | Comp (t1, _ , t2) -> acc && declared_term t1 && declared_term t2
    | _ -> acc) true ar



let rec variables_term t acc = match t with
  | Elem (a, Glob) | Access (a, _) -> STerm.add t acc
  | Arith (x, _) -> variables_term x acc
  | _ -> acc

let rec variables_atom a acc = match a with
  | True | False -> acc
  | Comp (t1, _, t2) -> variables_term t1 (variables_term t2 acc) 
  | Ite (sa, a1, a2) -> 
    STerm.union (variables_of sa) (variables_atom a1 (variables_atom a2 acc))

and variables_of sa = SAtom.fold variables_atom sa STerm.empty



let rec contain_arg z = function
  | Elem (x, _) -> Hstring.equal x z
  | Access (_, lx) -> Hstring.list_mem z lx
  | Arith (t, _) -> contain_arg z t
  | Const _ -> false

let has_var z = function
  | True | False -> false
  | Comp (t1, _, t2) -> (contain_arg z t1) || (contain_arg z t2)
  | Ite _ -> assert false

let is_int_const = function
  | ConstInt _ -> true
  | ConstReal _ -> false
  | ConstName n -> 
    Hstring.equal (snd (Smt.Symbol.type_of n)) Smt.Type.type_int

let rec type_of_term = function
  | Const cs ->
      if is_int_const (fst (MConst.choose cs)) then
        Smt.Type.type_int
      else Smt.Type.type_real
  | Elem (x, Var) -> Smt.Type.type_proc
  | Elem (x, _) | Access (x, _) -> snd (Smt.Symbol.type_of x)
  | Arith(t, _) -> type_of_term t


let arity s = List.length (fst (Smt.Symbol.type_of s))



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

let rec all_arrangements n l =
  assert (n > 0);
  match n with
    | 1 -> List.map (fun x -> [x]) l
    | _ -> 
        List.fold_left (fun acc l' ->
          List.fold_left (fun acc x -> (x :: l') :: acc) acc l
        ) [] (all_arrangements (n - 1) l)


let rec all_instantiations l1 l2 =
  match l1 with
    | [] -> []
    | [x1] -> List.map (fun x2 -> [x1, x2]) l2
    | x1 :: r1 -> 
        List.fold_left (fun acc l' ->
          List.fold_left (fun acc x2 -> ((x1, x2) :: l') :: acc) acc l2
        ) [] (all_instantiations r1 l2)


let init_instances = Hashtbl.create 11

let fill_init_instances (iargs, l_init) = match l_init with
  | [init] ->
      let sa, cst = SAtom.partition (fun a ->
        List.exists (fun z -> has_var z a) iargs) init in
      let ar0 = ArrayAtom.of_satom cst in
      Hashtbl.add init_instances 0 ([[cst]], [[ar0]]);
      let cpt = ref 1 in
      ignore (List.fold_left (fun v_acc v ->
        let v_acc = v :: v_acc in
        let vars = List.rev v_acc in
        let si = List.fold_left (fun si sigma ->
          SAtom.union (subst_atoms sigma sa) si)
          cst (all_instantiations iargs vars) in
        let ar = ArrayAtom.of_satom si in
        Hashtbl.add init_instances !cpt ([[si]], [[ar]]);
        incr cpt;
        v_acc) [] proc_vars)

  | _ ->
      let dnf_sa0, dnf_ar0 =
        List.fold_left (fun (dnf_sa0, dnf_ar0) sa ->
          let sa0 = SAtom.filter (fun a ->
            not (List.exists (fun z -> has_var z a) iargs)) sa in
          let ar0 = ArrayAtom.of_satom sa0 in
          sa0 :: dnf_sa0, ar0 :: dnf_ar0) ([],[]) l_init in
      Hashtbl.add init_instances 0  ([dnf_sa0], [dnf_ar0]);
      let cpt = ref 1 in
      ignore (List.fold_left (fun v_acc v ->
        let v_acc = v :: v_acc in
        let vars = List.rev v_acc in
        let inst =
          List.fold_left (fun (cdnf_sa, cdnf_ar) sigma ->
            let dnf_sa, dnf_ar = 
              List.fold_left (fun (dnf_sa, dnf_ar) init ->
              let sa = subst_atoms sigma init in
              let ar = ArrayAtom.of_satom sa in
              sa :: dnf_sa, ar :: dnf_ar
            ) ([],[]) l_init in
            dnf_sa :: cdnf_sa, dnf_ar :: cdnf_ar
          ) ([],[]) (all_instantiations iargs vars) in
        Hashtbl.add init_instances !cpt inst;
        incr cpt;
        v_acc) [] proc_vars)
        

let make_finite_inst_array a args =
    let rec add_args acc = function
      | [] -> acc
      | [x] -> acc ^ (Hstring.view x)
      | x :: r -> add_args (acc ^ "," ^ (Hstring.view x)) r in
    let a_str = Hstring.view a in
    let s = add_args (a_str ^ "[") args ^ "]" in
    Hstring.make s
    

















