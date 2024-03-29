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
open Sig

module rec CX : sig
  include Sig.X

  val set_arith_active : bool -> unit
  val set_sum_active : bool -> unit

  val extract1 : r -> X1.t option
  val embed1 : X1.t -> r

  val extract5 : r -> X5.t option
  val embed5 : X5.t -> r

end =
struct

  type r =
    | Term  of Term.t
    | X1    of X1.t 
    | X5    of X5.t 
    
  let x1_active = ref true
  let x5_active = ref true

  let set_arith_active b =  x1_active := b
  let set_sum_active b =  x5_active := b

  let extract1 = function X1 r   -> Some r | _ -> None
  let extract5 = function X5 r   -> Some r | _ -> None
  
  let embed1 x = X1 x
  let embed5 x = X5 x
	
  let is_int v = 
    let ty  = match v with
      | X5 x -> X5.type_info x
      | X1 x -> X1.type_info x
      | Term t -> (Term.view t).Term.ty
    in 
    ty = Ty.Tint
      
  let rec compare a b = 
    let c = compare_tag a b in 
    if c = 0 then comparei a b else c

  and compare_tag a b = 
    Stdlib.compare (theory_num a) (theory_num b)
      
  and comparei a b = 
    match a, b with
      | X5 x, X5 y -> X5.compare x y
      | X1 x, X1 y -> X1.compare x y
      | Term x  , Term y  -> Term.compare x y
      | _                 -> assert false

  and theory_num x = Obj.tag (Obj.repr x)

  let equal a b = compare a b = 0

  let hash = function
    | Term  t -> Term.hash t 
    | X5 x -> X5.hash x
    | X1 x -> X1.hash x

  module MR = Map.Make(struct type t = r let compare = compare end)
    
  let print fmt r = 
    match r with
      | X5 t    -> fprintf fmt "%a" X5.print t
      | X1 t    -> fprintf fmt "%a" X1.print t
      | Term t  -> fprintf fmt "%a" Term.print t
            
  let leaves r = 
    match r with 
      | X5 t -> X5.leaves t 
      | X1 t -> X1.leaves t 
      | Term _ -> [r]

  let term_embed t = Term t

  let term_extract r = 
    match r with 
      | X5 _ -> X5.term_extract r 
      | X1 _ -> X1.term_extract r 
      | Term t -> Some t

  let subst p v r = 
    if equal p v then r 
    else match r with
      | X5 t   -> X5.subst p v t
      | X1 t   -> X1.subst p v t
      | Term _ -> if equal p r then v else r

  let make t = 
    let {Term.f=sb} = Term.view t in
    match !x1_active && X1.is_mine_symb sb, !x5_active && X5.is_mine_symb sb with
      | false, true  -> X5.make t
      | true, false -> X1.make t
      | false, false -> Term t, []
      | _ -> assert false
	  
  let fully_interpreted sb =
    match !x1_active && X1.is_mine_symb sb, !x5_active && X5.is_mine_symb sb with
      | false, true -> X5.fully_interpreted sb
      | true, false -> X1.fully_interpreted sb
      | false, false -> false
      | _ -> assert false

  let add_mr =
    List.fold_left 
      (fun solved (p,v) -> 
	 MR.add p (v::(try MR.find p solved with Not_found -> [])) solved)

  let unsolvable = function
    | X5 x -> X5.unsolvable x 
    | X1 x -> X1.unsolvable x
    | Term _  -> true
	
  let partition tag = 
    List.partition 
      (fun (u,t) -> 
	 (theory_num u = tag || unsolvable u) && 
	   (theory_num t = tag || unsolvable t))

  let rec solve_list  solved l =
    List.fold_left
      (fun solved (a,b) -> 
	 let cmp = compare a b in
	 if cmp = 0 then solved else
	   match a , b with
	       (* both sides are empty *)
	     | Term _ , Term _  -> 
		 add_mr solved (unsolvable_values cmp  a b)
		   
	     (* only one side is empty *)
	     | (a, b) 
                 when unsolvable a || unsolvable b ||  compare_tag a b = 0 ->
		 let a,b = if unsolvable a then b,a else a,b in
		 let cp , sol = partition (theory_num a) (solvei  b a) in
		 solve_list  (add_mr solved cp) sol
		   
	     (* both sides are not empty *)
	     | a , b -> solve_theoryj  solved a b
      ) solved l

  and unsolvable_values cmp a b =
    match a, b with
      (* Clash entre theories: On peut avoir ces pbs ? *)
      | X1 _, X5 _
      | X5 _, X1 _ 
       -> assert false

      (* theorie d'un cote, vide de l'autre *)
      | X1 _, _ | _, X1 _ -> X1.solve a b
      | X5 _, _ | _, X5 _ -> X5.solve a b
      | Term _, Term _ -> [if cmp > 0 then a,b else b,a]

  and solve_theoryj solved xi xj =
    let cp , sol = partition (theory_num xj) (solvei  xi xj) in
    solve_list  (add_mr solved cp) (List.rev_map (fun (x,y) -> y,x) sol)

  and solvei  a b =
    match b with
      | X5 _ -> X5.solve  a b
      | X1 _ -> X1.solve  a b
      | Term _ -> assert false

  let rec solve_rec  mt ab = 
    let mr = solve_list  mt ab in
    let mr , ab = 
      MR.fold 
	(fun p lr ((mt,ab) as acc) -> match lr with
	     [] -> assert false
	   | [_] -> acc
	   | x::lx -> 
	       MR.add p [x] mr , List.rev_map (fun y-> (x,y)) lx)	 
	mr (mr,[])
    in 
    if ab = [] then mr else solve_rec  mr ab
      
  let solve  a b =
    MR.fold 
      (fun p lr ret -> 
	 match lr with [r] -> (p ,r)::ret | _ -> assert false) 
      (solve_rec  MR.empty [a,b]) []

  let rec type_info = function
    | X5 t   -> X5.type_info t
    | X1 t   -> X1.type_info t
    | Term t -> let {Term.ty = ty} = Term.view t in ty
	
  module Rel = struct
    type elt = r
    type r = elt

    type t = { 
      r1: X1.Rel.t; 
      r5: X5.Rel.t; 
    }
	
    let empty _ = {
      r1=X1.Rel.empty (); 
      r5=X5.Rel.empty ();
    }
      
    let assume env sa =
      let env1, { assume = a1; remove = rm1} = 
        if !x1_active then X1.Rel.assume env.r1 sa 
        else env.r1, { assume = []; remove = []} in
      let env5, { assume = a5; remove = rm5} = 
        if !x5_active then X5.Rel.assume env.r5 sa 
        else env.r5, { assume = []; remove = []} in
      { r1 = env1; r5 = env5 }, 
      { assume = a1@a5; remove = rm1@rm5;}
	
    let query env a =
      if !x1_active && !x5_active then
        match X5.Rel.query env.r5 a with
	  | Yes _ as ans -> ans
	  | No -> X1.Rel.query env.r1 a
      else if !x1_active then X1.Rel.query env.r1 a
      else if !x5_active then X5.Rel.query env.r5 a
      else No


    let case_split env = 
      let seq5 = if !x5_active then X5.Rel.case_split env.r5 else [] in
      let seq1 = if !x1_active then X1.Rel.case_split env.r1 else [] in
      seq1 @ seq5

    let add env r =
      { r1 = if !x1_active then X1.Rel.add env.r1 r else env.r1;
        r5 = if !x5_active then X5.Rel.add env.r5 r else env.r5 }
  end

end

and TX1 : Polynome.T with type r = CX.r = Arith.Type(CX)

and X1 : Sig.THEORY  with type t = TX1.t and type r = CX.r =
  Arith.Make(CX)(TX1)
    (struct
       type t = TX1.t
       type r = CX.r
       let extract = CX.extract1
       let embed =  CX.embed1
       let assume env _ _ = env, {Sig.assume = []; remove = []} 
     end)

and X5 : Sig.THEORY with type r = CX.r and type t = CX.r Sum.abstract =
  Sum.Make
    (struct
       include CX
       let extract = extract5
       let embed = embed5
     end)
