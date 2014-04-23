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

module HSet = Hstring.HSet

type op_comp = Eq | Lt | Le | Neq

type sort = Glob | Constr | Var


type const =
    ConstInt of Num.num | ConstReal of Num.num | ConstName of Hstring.t

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

  let is_num m =
    if M.cardinal m = 1 then
      match choose m with
      | (ConstInt n | ConstReal n), i -> Some (Num.mult_num (Num.Int i) n)
      | _ -> None
    else None
	   
end

type term =
  | Const of int MConst.t
  | Elem of Hstring.t * sort
  | Access of Hstring.t * Variable.t list
  | Arith of term * int MConst.t

let is_int_const = function
  | ConstInt _ -> true
  | ConstReal _ -> false
  | ConstName n -> 
     Hstring.equal (snd (Smt.Symbol.type_of n)) Smt.Type.type_int


let compare_constants = MConst.compare Pervasives.compare 


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
    (fun c i (cs, num) ->
     match c, num with
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


let const_sign c =
  try
    let n = ref (Num.Int 0) in
    MConst.iter (fun c i ->
      if i <> 0 then 
	match c with
	| ConstName _ -> raise Exit
	| ConstInt a | ConstReal a -> 
	   n := Num.add_num (Num.mult_num (Num.Int i) a) !n) c;
    Some (Num.compare_num !n (Num.Int 0))
  with Exit -> None

let const_nul c = const_sign c = Some 0



module Term = struct

  type t = term

  let rec compare t1 t2 = 
    match t1, t2 with
    | Const c1, Const c2 -> compare_constants c1 c2
    | Const _, _ -> -1 | _, Const _ -> 1
    | Elem (_, (Constr | Var)), Elem (_, Glob) -> -1
    | Elem (_, Glob), Elem (_, (Constr | Var)) -> 1
    | Elem (s1, _), Elem (s2, _) -> Hstring.compare s1 s2
    | Elem _, _ -> -1 | _, Elem _ -> 1
    | Access (a1, l1), Access (a2, l2) ->
       let c = Hstring.compare a1 a2 in
       if c<>0 then c else Hstring.compare_list l1 l2
    | Access _, _ -> -1 | _, Access _ -> 1 
    | Arith (t1, cs1), Arith (t2, cs2) ->
       let c = compare t1 t2 in
       if c<>0 then c else compare_constants cs1 cs2

  let hash = Hashtbl.hash_param 50 50

  let equal t1 t2 = compare t1 t2 = 0

  let htrue = Hstring.make "True"
  let hfalse = Hstring.make "False"

  module STerm = Set.Make (struct
                            type t = term
                            let compare = compare
                          end)

  module Set = STerm

  let rec subst sigma t =
    match t with
    | Elem (x, s) ->
       let nx = Variable.subst sigma x in
       if x == nx then t
       else Elem (nx, s)
    | Access (a, lz) -> 
       Access (a, List.map
                    (fun z ->
                     try Variable.subst sigma z with Not_found -> z) lz)
    | Arith (x, c) -> Arith (subst sigma x, c)
    | _ -> t


  let rec variables = function
    | Elem (x, Var) -> Variable.Set.singleton x
    | Access (_, lx) ->
       List.fold_left (fun acc x -> Variable.Set.add x acc)
                      Variable.Set.empty lx
    | Arith (t, _) -> variables t
    | _ -> Variable.Set.empty


  let variables_proc t = Variable.Set.filter Variable.is_proc (variables t)

  let rec type_of = function
    | Const cs ->
       if is_int_const (fst (MConst.choose cs)) then
         Smt.Type.type_int
       else Smt.Type.type_real
    | Elem (x, Var) -> Smt.Type.type_proc
    | Elem (x, _) | Access (x, _) -> snd (Smt.Symbol.type_of x)
    | Arith(t, _) -> type_of t


  let rec print_strings fmt = function
    | [] -> ()
    | [s] -> fprintf fmt "%s" s
    | s :: l -> fprintf fmt "%s %a" s print_strings l

  let print_const fmt = function
    | ConstInt n | ConstReal n -> fprintf fmt "%s" (Num.string_of_num n)
    | ConstName n -> fprintf fmt "%a" Hstring.print n

  let print_cs fmt cs =
    MConst.iter 
      (fun c i ->
       fprintf fmt " %s %a" 
	       (if i = 1 then "+" else if i = -1 then "-" 
	        else if i < 0 then "- "^(string_of_int (abs i)) 
	        else "+ "^(string_of_int (abs i)))
	       print_const c) cs

  let rec print fmt = function
    | Const cs -> print_cs fmt cs
    | Elem (s, _) -> fprintf fmt "%a" Hstring.print s
    | Access (a, li) ->
       fprintf fmt "%a[%a]" Hstring.print a (Hstring.print_list ", ") li
    | Arith (x, cs) -> 
       fprintf fmt "@[%a%a@]" print x print_cs cs

end





module rec Atom : sig

  type t =
    | True
    | False
    | Comp of Term.t * op_comp * Term.t
    | Ite of SAtom.t * t * t

  val compare : t -> t -> int
  val trivial_is_implied : t -> t -> int
  val neg : t -> t
  val hash : t -> int
  val equal : t -> t -> bool
  val subst : Variable.subst -> t -> t
  val has_var : Variable.t -> t -> bool
  val has_vars : Variable.t list -> t -> bool
  val variables : t -> Variable.Set.t
  val variables_proc : t -> Variable.Set.t
  val print : Format.formatter -> t -> unit
  val print_atoms : bool -> string -> Format.formatter -> t list -> unit

end = struct

  type t =
    | True
    | False
    | Comp of Term.t * op_comp * Term.t
    | Ite of SAtom.t * t * t

  let rec compare a1 a2 = 
    match a1, a2 with
      | True, True -> 0
      | True, _ -> -1 | _, True -> 1
      | False, False -> 0
      | False, _ -> -1 | _, False -> 1
      | Comp (x1, op1, y1), Comp (x2, op2, y2) ->
	  let c1 = Term.compare x1 x2 in
	  if c1 <> 0  then c1 
	  else 
	    let c0 = Pervasives.compare op1 op2 in
	    if c0 <> 0 then c0 
	    else 
	      let c2 = Term.compare y1 y2 in c2
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
          when not (Hstring.equal v1 v2) && Term.compare x1 x2 = 0 -> 0
      | _ -> compare a1 a2

  let neg = function
    | True -> False
    | False -> True
    | Comp (c, Eq, (Elem (x, Constr))) when Hstring.equal x Term.hfalse -> 
	Comp (c, Eq, (Elem (Term.htrue, Constr)))
    | Comp (c, Eq, (Elem (x, Constr))) when Hstring.equal x Term.htrue -> 
	Comp (c, Eq, (Elem (Term.hfalse, Constr)))
    | Comp (x, Eq, y) -> Comp (x, Neq, y)
    | Comp (x, Lt, y) -> Comp (y, Le, x)
    | Comp (x, Le, y) -> Comp (y, Lt, x)
    | Comp (x, Neq, y) -> Comp (x, Eq, y)
    | _ -> assert false

  let hash (sa: Atom.t) = Hashtbl.hash_param 50 100 sa

  let equal x y = compare x y = 0

  let rec subst sigma a =
    match a with
    | Ite (sa, a1, a2) ->
       Ite(SAtom.subst sigma sa, 
           subst sigma a1, 
           subst sigma a2)
    | Comp (x, op, y) -> 
       let sx = Term.subst sigma x in
       let sy = Term.subst sigma y in
       if x == sx && y == sy then a
       else Comp(sx, op, sy)
    | _ -> a

  let rec has_vars_term vs = function
    | Elem (x, Var) -> Hstring.list_mem x vs
    | Access (_, lx) -> List.exists (fun z -> Hstring.list_mem z lx) vs 
    | Arith (x, _) ->  has_vars_term vs x
    | _ -> false

  let rec has_vars vs = function
    | True | False -> false
    | Comp (x, _, y) -> has_vars_term vs x || has_vars_term vs y
    | Ite (sa, a1, a2) ->
       SAtom.exists (has_vars vs) sa || has_vars vs a1 || has_vars vs a2

  let has_var v = has_vars [v]


  let rec variables = function
    | True | False -> Variable.Set.empty
    | Comp (t1, _, t2) -> 
       Variable.Set.union (Term.variables t1) (Term.variables t2)
    | Ite (sa, a1, a2) -> 
       let acc = Variable.Set.union (variables a1) (variables a2) in
       Variable.Set.union acc (SAtom.variables sa)


  let variables_proc a = Variable.Set.filter Variable.is_proc (variables a)


  let str_op_comp = function Eq -> "=" | Lt -> "<" | Le -> "<=" | Neq -> "<>"

  let rec print fmt = function
    | True -> fprintf fmt "true"
    | False -> fprintf fmt "false"
    | Comp (x, op, y) -> 
       fprintf fmt "%a %s %a" Term.print x (str_op_comp op) Term.print y
    | Ite (la, a1, a2) ->
       fprintf fmt "@[ite(%a,@ %a,@ %a)@]" 
	       (print_atoms false "&&") (SAtom.elements la) print a1 print a2

  and print_atoms inline sep fmt = function
    | [] -> ()
    | [a] -> print fmt a
    | a::l -> 
       if inline then 
         fprintf fmt "%a %s@ %a" print a sep (print_atoms inline sep) l
       else
         fprintf fmt "%a %s@\n%a" print a sep (print_atoms inline sep) l

end

and SAtom : sig

  include Set.S with type elt = Atom.t

  val equal : t -> t -> bool
  val hash : t -> int
  val subst : Variable.subst -> t -> t
  val variables : t -> Variable.Set.t
  val variables_proc : t -> Variable.Set.t
  val print : Format.formatter -> t -> unit
  val print_inline : Format.formatter -> t -> unit

end = struct 
    
  include Set.Make(Atom)

  let add a s = 
    match a with
    | Atom.True -> s
    | Atom.False -> singleton Atom.False
    | _ -> if mem Atom.False s then s else add a s


  let equal sa1 sa2 = compare sa1 sa2 = 0

  let hash (sa:t) = Hashtbl.hash_param 100 500 sa

  let subst sigma sa =
    if Variable.is_subst_identity sigma then sa
    else
      fold (fun a -> add (Atom.subst sigma a)) sa empty

  let subst sigma sa =
    TimerApply.start ();
    let sa = subst sigma sa in
    TimerApply.pause ();
    sa

  let variables sa =
    fold (fun a -> Variable.Set.union (Atom.variables a)) sa Variable.Set.empty

  let variables_proc sa = Variable.Set.filter Variable.is_proc (variables sa)

  let print fmt sa =
    fprintf fmt "@[%a@]" (Atom.print_atoms false "&&") (elements sa)

  let print_inline fmt sa =
    fprintf fmt "@[%a@]" (Atom.print_atoms true "&&") (elements sa)

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
    TimerSubset.start ();
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
    TimerSubset.pause ();
    s

  let trivial_is_implied a1 a2 =
    TimerSubset.start ();
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
    TimerSubset.pause ();
    s

  let subset = trivial_is_implied

  let of_satom s =
    Array.of_list (SAtom.elements s)

  let to_satom =
    Array.fold_left (fun s a -> SAtom.add a s) SAtom.empty

  let union a b = Array.append a b
    (* let cpt = ref 0 in fun a b -> incr cpt; eprintf "%d@." !cpt;  *)
    (*                               Array.append a b *)
    (* let a = Array.append a1 a2 in *)
    (* Array.fast_sort Atom.compare a; a *)

  let apply_subst sigma a =
    TimerApply.start ();
    if Variable.is_subst_identity sigma then (TimerApply.pause (); a)
    else
      let a' = Array.init (Array.length a) (fun i -> Atom.subst sigma a.(i)) in
      Array.fast_sort Atom.compare a';
      TimerApply.pause ();
      a'

  let alpha atoms args =
    let subst = Variable.build_subst args Variable.alphas in
    List.map snd subst, apply_subst subst atoms

  let nb_diff a1 a2 =
    TimerSubset.start ();
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
    TimerSubset.pause ();
    !cpt + (n1 - !i1)

  let compare_nb_diff a p1 p2 =
    Pervasives.compare (nb_diff p1 a) (nb_diff p2 a)


  let nb_common a1 a2 =
    TimerSubset.start ();
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
    TimerSubset.pause ();
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

  let print fmt a =
    fprintf fmt "@[%a@]" (Atom.print_atoms false "&&") (Array.to_list a)

end
