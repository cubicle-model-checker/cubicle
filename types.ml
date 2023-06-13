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
    | ConstInt  of Num.num 
    | ConstReal of Num.num

module Const = struct
  type t = const

  let compare c1 c2 = 
    match c1, c2 with 
    | ConstInt i1, ConstInt i2
    | ConstReal i1, ConstReal i2 -> Num.compare_num i1 i2 
    | ConstReal _, _ -> 1
    | ConstInt _, ConstReal _ -> -1
    
  let equal c1 c2 = compare c1 c2 = 0


  let type_of = function 
    | ConstInt  _ -> Smt.Type.type_int
    | ConstReal _ -> Smt.Type.type_real

  let is_int = function
    | ConstInt  _ -> true 
    | ConstReal _ -> false

  let sign = function
    | ConstInt n | ConstReal n -> Num.sign_num n

  let to_num = function
    | ConstInt n | ConstReal n -> n

  let is_one  n = Num.compare_num (to_num n) (Num.num_of_int 1) = 0
  let is_zero n = Num.compare_num (to_num n) (Num.num_of_int 0) = 0

  let num_equal c1 c2 = Num.eq_num (to_num c1) (to_num c2)
  let num_lt    c1 c2 = Num.lt_num (to_num c1) (to_num c2)
  let num_le    c1 c2 = Num.le_num (to_num c1) (to_num c2)

  (* -- *)

  let const_int  n = ConstInt   (n)
  let const_real n = ConstReal  (n)
  let int_zero     = ConstInt   (Num.num_of_int 0)
  let int_one      = ConstInt   (Num.num_of_int 1)
  let real_zero    = ConstReal  (Num.num_of_int 0)
  let real_one     = ConstReal  (Num.num_of_int 1)
  
  (* Opérations arithméthiques *)

  let add_const c1 c2 =
    match c1, c2 with 
    | ConstInt i1, ConstInt i2   -> ConstInt(Num.add_num i1 i2) 
    | ConstReal i1, ConstReal i2 
    | ConstInt i1, ConstReal i2 
    | ConstReal i1, ConstInt i2 -> ConstReal(Num.add_num i1 i2) 

  let add_int c i = add_const c (ConstInt(i))

  let add_real c i = add_const c (ConstReal(i))

  let mult_by_int c i =
    match c with 
    | ConstInt  n -> ConstInt (Num.mult_num n i)
    | ConstReal n -> ConstReal (Num.mult_num n i) 

  let mult_by_real c i =  
    match c with 
    | ConstReal n | ConstInt n -> ConstReal (Num.mult_num n i)

  let mult_by_const c1 c2 =
    match c1, c2 with 
    | ConstInt i1,  ConstInt  i2 -> ConstInt (Num.mult_num i1 i2)
    | ConstReal i1, ConstReal i2  
    | ConstReal i1, ConstInt  i2
    | ConstInt  i1, ConstReal i2 -> ConstReal (Num.mult_num i1 i2)

  let neg = function 
    | ConstReal r -> ConstReal(Num.minus_num r)
    | ConstInt  i -> ConstInt(Num.minus_num i)

  let cast c t =
    let is_type = Hstring.equal t in 
    match c with
    | ConstInt  _ when is_type Smt.Type.type_int  -> c
    | ConstInt  i when is_type Smt.Type.type_real -> ConstReal(i) 
    | ConstReal i when is_type Smt.Type.type_real -> c
    | _ -> assert false

end

module Vea = struct
    type t = 
      | Elem   of Hstring.t * sort             
      | Access of Hstring.t * Variable.t list  

    let to_string = function
      | Elem   (t,_) -> Hstring.view t
      | Access (t,_) -> Hstring.view t

    let compare x y =
      match x, y with
      | Elem (a1,s1), Elem(a2, s2) ->
         let c = Stdlib.compare s1 s2 in
         if c <> 0 then c
         else Hstring.compare a1 a2
      | Access(t1,l1), Access(t2,l2) ->
         let c = Hstring.compare t1 t2 in
         if c <> 0 then c
         else Variable.compare_list l1 l2
      | Elem (_,_), Access(_,_) -> -1
      | Access (_,_), Elem(_,_) -> 1

    let type_of = function 
        | Elem (x, Var)               -> Smt.Type.type_proc
        | Elem (x, _) | Access (x, _) -> snd (Smt.Symbol.type_of x)
end

module VMap = struct
  include Map.Make(Vea)

  let add_vmap = 
    union (fun _ c1 c2 -> Some(Const.add_const c1 c2)) 

  let mult_int v i = 
    map (fun x -> Const.mult_by_int x i) v

  let mult_real v i = 
    map (fun x -> Const.mult_by_real x i) v

  let vmap_mult_const v c = 
    map (fun x -> Const.mult_by_const x c) v

  let neg =
    map Const.neg

end


(* -- *)

type term = 
  | Vea   of Vea.t
  | Poly  of Const.t * Const.t VMap.t

let term_mult_by_int t1 i = 
  match t1 with
  | Poly(cs, ts) -> 
    Poly(Const.mult_by_int cs i, VMap.mult_int ts i)
  | Vea(v) ->
    Poly(Const.int_zero, VMap.add v (Const.const_int i) VMap.empty )

let term_mult_by_real t i =
  match t with
  | Poly(cs, ts) -> 
    Poly(Const.mult_by_real cs i, VMap.mult_real ts i)
  | Vea(v) -> 
    Poly(Const.real_zero, VMap.add v (Const.const_real i) VMap.empty)

let term_mult_by_vea t v =
  match t with 
  | Poly(ConstInt(_) as cs, ts) when ts = VMap.empty  ->
      Poly(Const.int_zero, VMap.add v cs VMap.empty)
  | Poly(ConstReal(_) as cs, ts) when ts = VMap.empty -> 
      Poly(Const.real_zero, VMap.add v cs VMap.empty)
  | _ -> failwith "trying to multiply two vars"

let term_neg = function
  | Poly(cs,ts) -> Poly(Const.neg cs, VMap.neg ts)
  | Vea v -> 
      Poly(Const.neg (Const.int_zero), VMap.neg (VMap.add v Const.int_one VMap.empty))

let term_add t1 t2 = 
  match t1, t2 with
  | Vea(v1), Vea(v2) ->
      let cs = Const.int_zero in 
      let ts = VMap.empty in
      let vtots1 = VMap.add v1 Const.int_one VMap.empty in 
      let ts = VMap.add_vmap vtots1 ts in
      let vtots2 = VMap.add v1 Const.int_one VMap.empty in 
      let ts = VMap.add_vmap vtots2 ts in
      Poly(cs, ts)
  | Vea v, Poly(cs, ts) | Poly(cs ,ts), Vea v ->
      let vtots = VMap.add v Const.int_one VMap.empty in 
      let ts' = VMap.add_vmap vtots ts in 
      Poly(cs, ts')
  | Poly(cs1, ts1), Poly(cs2, ts2) -> 
      let cs' = Const.add_const cs1 cs2 in 
      let ts' = VMap.add_vmap ts1 ts2 in
      Poly(cs', ts')

let term_mult_by_term t1 t2 =
  match t1, t2 with 
  | t, Poly(ConstInt i, ts) 
  | Poly(ConstInt i, ts), t ->  
      if VMap.cardinal ts = 0 then term_mult_by_int  t i
                              else failwith "trying to multiply two vars"
  | t, Poly(ConstReal  i, ts) | Poly(ConstReal i, ts), t ->
      if VMap.cardinal ts = 0 then term_mult_by_real  t i
                              else failwith "trying to multiply two vars"
  | _ -> failwith "trying to multiply two vars" 

module Term = struct

  type t = term
 
  let rec compare t1 t2 = 
    match t1, t2 with
    | Vea v1, Vea v2 -> Vea.compare v1 v2
    | Vea v, Poly(cs, ts) ->
        if VMap.cardinal ts = 1 then
          let (v2, c2) = VMap.choose ts in 
          if Const.is_one c2 then Vea.compare v2 v else 1
        else 1
    | Poly(cs, ts), Vea v ->
        if VMap.cardinal ts = 1 then
          let (v2, c2) = VMap.choose ts in 
          if Const.is_one c2 then Vea.compare v2 v else -1
        else -1
    | Poly(cs1, ts1), Poly(cs2, ts2) ->
        let c = Const.compare cs1 cs2 in 
        if c <> 0 then c else
          VMap.compare Const.compare ts1 ts2
  
  let hash (a : t) = Hashtbl.hash_param 50 50 a

  let equal t1 t2 = compare t1 t2 = 0

  let htrue  = Hstring.make "True"
  let hfalse = Hstring.make "False"

  module STerm = Set.Make (struct
                            type t = term
                            let compare = compare
                          end)

  module Set = STerm

  let subst sigma t =
    let subst_vea (vea : Vea.t) = 
      match vea with
      | Elem (x, s) ->
         let nx = Variable.subst sigma x in
         if x == nx then vea
         else Elem (nx, s)
      | Access (a, lz) -> 
         Access (a, List.map
                      (fun z -> try Variable.subst sigma z with Not_found -> z) lz)
    in
    match t with
    | Vea  v        -> Vea(subst_vea v)
    | Poly (cs, ts) -> 
        Poly(cs, VMap.fold (fun v c acc -> VMap.add (subst_vea v) c acc) ts
        VMap.empty)

  let variables t = 
    let variables_vea = function 
      | Vea.Elem (x, Var) -> Variable.Set.singleton x
      | Vea.Access (_, lx) ->
         List.fold_left (fun acc x -> Variable.Set.add x acc)
                        Variable.Set.empty lx
      | _ -> Variable.Set.empty
    in 
    match t with 
    | Vea v -> variables_vea v
    | Poly(cs, ts) -> 
        VMap.fold
        (fun k _ s -> Variable.Set.union (variables_vea k) s)
        ts
        Variable.Set.empty

  let variables_proc t = Variable.Set.filter Variable.is_proc (variables t)


  let type_of = function
    | Vea  (v)      -> Vea.type_of v
    | Poly (cs, ts) -> Const.type_of cs

  let print fmt t = 
    let vea_to_string = function 
      | Vea.Elem (s, _) -> sprintf "%s" (Hstring.view s)
      | Vea.Access (a, li) ->
         let li = List.map Hstring.view li in 
         sprintf "%s[%s]" (Hstring.view a) (String.concat ", " li)
    in
    match t with
    | Vea v         -> fprintf fmt "%s" (vea_to_string v) 
    | Poly (cs, ts) ->
        let const_to_string c = Const.to_num c |> Num.string_of_num in
        let bind = VMap.bindings ts in 

        let bind_str = 
          List.map 
          (fun (k,c) -> sprintf "%s*%s" (vea_to_string k) (const_to_string c))
          bind
        in
        let sum_str = String.concat " + " bind_str in
        
        if List.length bind_str > 0 then 
          if not (Const.is_zero cs) then fprintf fmt "%s + %s" (const_to_string cs) sum_str 
                                    else fprintf fmt "%s" sum_str 
        else 
          fprintf fmt "%s" (const_to_string cs)

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
	    let c0 = Stdlib.compare op1 op2 in
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
      | Comp (x1, Neq, Vea(Elem (v1, (Constr|Var)))),
        Comp (x2, Eq,  Vea(Elem (v2, (Constr|Var)))) 
          when not (Hstring.equal v1 v2) && Term.compare x1 x2 = 0 -> 0
      | _ -> compare a1 a2

  let neg = function
    | True -> False
    | False -> True
    (* TODO G 
    | Comp (c, Eq, (Elem (x, Constr))) when Hstring.equal x Term.hfalse -> 
	Comp (c, Eq, (Elem (Term.htrue, Constr)))
    | Comp (c, Eq, (Elem (x, Constr))) when Hstring.equal x Term.htrue -> 
	Comp (c, Eq, (Elem (Term.hfalse, Constr)))
    *)
    | Comp (x, Eq, y) -> Comp (x, Neq, y)
    | Comp (x, Lt, y) -> Comp (y, Le, x)
    | Comp (x, Le, y) -> Comp (y, Lt, x)
    | Comp (x, Neq, y) -> Comp (x, Eq, y)
    | _ -> failwith "todo neg" (*assert false TODO G : Reput assert false*)

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
    | Vea v -> 
        begin match v with 
        | Elem (x, Var) -> Hstring.list_mem x vs
        | Access (_, lx) -> List.exists (fun z -> Hstring.list_mem z lx) vs
        | _ -> false
        end 
    (* TODO G
    | Arith (x, _) ->  has_vars_term vs x
    *)
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
    fprintf fmt "@[<hov>%a@]" (Atom.print_atoms false "&&") (elements sa)

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
    Stdlib.compare (nb_diff p1 a) (nb_diff p2 a)


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
    Stdlib.compare (nb_common p2 a) (nb_common p1 a)

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
    fprintf fmt "@[<hov>%a@]" (Atom.print_atoms false "&&") (Array.to_list a)

end
