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
open Ast
open Util
open Types

module H = Hstring

(*********************************************)
(* all permutations excepted impossible ones *)
(*********************************************)

let filter_impos perms impos =
  List.filter (fun sigma ->
               not (List.exists (List.for_all 
                    (fun (x,y) -> H.list_mem_couple (x,y) sigma))
                    impos))
              perms

let rec all_permutations_impos l1 l2 impos =
  filter_impos (Variable.all_permutations l1 l2) impos




(****************************************************)
(* Improved relevant permutations (still quadratic) *)
(****************************************************)

let list_rev_split =
  List.fold_left (fun (l1, l2) (x, y) -> x::l1, y::l2) ([], [])

let list_rev_combine =
  List.fold_left2 (fun acc x1 x2 -> (x1, x2) :: acc) []


exception NoPermutations

let find_impossible a1 lx1 op c1 i2 a2 n2 impos obvs =
  failwith "todo find impossible"
  
  (* TODO G 
  let i2 = ref i2 in
  while !i2 < n2 do
    let a2i = a2.(!i2) in
    (match a2i, op with
      | Atom.Comp (Vea(Access (a2, _)), _, _), _ when not (H.equal a1 a2) ->
	  i2 := n2

      | Atom.Comp (Vea(Access (a2, lx2)), Eq,
	      (Vea(Elem (_, Constr)) | Vea(Elem (_, Glob)) (* TODO G | Arith _ as c2
        *))), (Neq | Lt)
	  when Term.compare c1 c2 = 0 ->
	  
	  if List.for_all2 
            (fun x1 x2 -> H.list_mem_couple (x1, x2) obvs) lx1 lx2 then
            raise NoPermutations;
          impos := (list_rev_combine lx1 lx2) :: !impos
	      
      | Atom.Comp (Vea(Access (a2, lx2)), (Neq | Lt),
	      (Vea(Elem (_, Constr)) | Vea(Elem (_, Glob)) | Arith _ as c2)), Eq
	  when Term.compare c1 c2 = 0 ->

	  if List.for_all2
            (fun x1 x2 -> H.list_mem_couple (x1, x2) obvs) lx1 lx2 then
            raise NoPermutations;
          impos := (list_rev_combine lx1 lx2) :: !impos

      | Atom.Comp (Vea(Access (a2, lx2)), Eq, (Vea(Elem (_, Constr)) as c2)), Eq 
	  when Term.compare c1 c2 <> 0 ->
	  
	  if List.for_all2
            (fun x1 x2 -> H.list_mem_couple (x1, x2) obvs) lx1 lx2 then
            raise NoPermutations;
          impos := (list_rev_combine lx1 lx2) :: !impos
	    
      | _ -> ());
    incr i2
  done
  *)

let clash_binding (x,y) l =
  try not (H.equal (H.list_assoc_inv y l) x)
  with Not_found -> false
    
let add_obv ((x,y) as p) obvs =
  begin
    try if clash_binding p !obvs || not (H.equal (H.list_assoc x !obvs) y) then 
	raise NoPermutations
    with Not_found -> obvs := p :: !obvs
  end

let obvious_impossible a1 a2 =
  failwith "todo obvious impossible"
  (* TODO G
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
       | Atom.Comp (Vea(Elem (x1, sx1)), Eq, Vea(Elem (y1, sy1))), 
	 Atom.Comp (Vea(Elem (x2, sx2)), Eq, Vea(Elem (y2, sy2))) ->
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
       | Atom.Comp (Vea(Elem (x1, sx1)), Eq, Vea(Elem (y1, sy1))), 
	 Atom.Comp (Vea(Elem (x2, sx2)), (Neq | Lt), Vea(Elem (y2, sy2))) ->
    	   begin
	     match sx1, sy1, sx2, sy2 with
    	       | Glob, Constr, Glob, Constr 
		   when H.equal x1 x2 && H.equal y1 y2 ->
    		   raise NoPermutations
    	       | _ -> ()
	   end
       | Atom.Comp (Access (a1, lx1), op, 
	            (Vea(Elem (_, Constr)) | Vea(Elem (_, Glob)) | Arith _ as c1)), 
	 Atom.Comp (Vea(Access (a, _)), _,
                    (Vea(Elem (_, Constr)) | Vea(Elem (_, Glob)) | Arith _ ))
    	   when H.equal a1 a ->
	   find_impossible a1 lx1 op c1 !i2 a2 n2 impos !obvs
       | _ -> ());
    if Atom.compare a1i a2i <= 0 then incr i1 else incr i2
  done;
  !obvs, !impos
  *)

(*******************************************)
(* Relevant permuations for fixpoint check *)
(*******************************************)

(****************************************************)
(* Find relevant quantifier instantiation for 	    *)
(* \exists z_1,...,z_n. np => \exists x_1,...,x_m p *)
(****************************************************)

let relevant_permutations np p l1 l2 =
  TimeRP.start ();
  try
    let obvs, impos = obvious_impossible p np in
    let obvl1, obvl2 = list_rev_split obvs in
    let l1 = List.filter (fun b -> not (H.list_mem b obvl1)) l1 in
    let l2 = List.filter (fun b -> not (H.list_mem b obvl2)) l2 in
    let perm = all_permutations_impos l1 l2 impos in
    let r = List.rev_map (List.rev_append obvs) perm in
    (* assert (List.for_all Variable.well_formed_subst r); *)
    TimeRP.pause ();
    r
  with NoPermutations -> TimeRP.pause (); []

let relevant ~of_cube ~to_cube =
  let of_vars, to_vars = of_cube.Cube.vars, to_cube.Cube.vars in
  let dif = Variable.extra_vars of_vars to_vars in
  let to_vars = if dif = [] then to_vars else to_vars@dif in
  relevant_permutations to_cube.Cube.array of_cube.Cube.array of_vars to_vars

let exhaustive ~of_cube ~to_cube =
  let of_vars, to_vars = of_cube.Cube.vars, to_cube.Cube.vars in
  let dif = Variable.extra_vars of_vars to_vars in
  let to_vars = if dif = [] then to_vars else to_vars@dif in
  Variable.all_permutations of_vars to_vars

