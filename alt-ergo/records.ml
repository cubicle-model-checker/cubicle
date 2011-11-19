(**************************************************************************)
(*                                                                        *)
(*     The Alt-ergo theorem prover                                        *)
(*     Copyright (C) 2006-2010                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
(*     Alain Mebsout                                                      *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

open Format
open Options
open Sig

type ('a, 'b) mine = Yes of 'a | No of 'b

type 'a abstract = 
  | Record of (Hstring.t * 'a abstract) list * Ty.t
  | Access of Hstring.t * 'a abstract * Ty.t
  | Other of 'a * Ty.t

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end

module Make (X : ALIEN) = struct 

  module XS = Set.Make(struct type t = X.r let compare = X.compare end)

  let name = "records"

  type t = X.r abstract
  type r = X.r

  let rec print fmt = function
    | Record (lbs, _) -> 
	fprintf fmt "{ ";
	List.iter 
	  (fun (lb, e) -> 
	     fprintf fmt "%s = %a; " (Hstring.view lb) print e) lbs;
	fprintf fmt "}"
    | Access(a, e, _) -> 
	fprintf fmt "%a.%s" print e (Hstring.view a)
    | Other(t, _) -> X.print fmt t

  let rec raw_compare r1 r2 =
    match r1, r2 with
      | Other (u1, _), Other (u2, _) -> 
	  X.compare u1 u2
      | Other _, _ -> -1
      | _, Other _ -> 1
      | Access (s1, u1, _), Access (s2, u2, _) ->
	  let c = Hstring.compare s1 s2 in
	  if c <> 0 then c
	  else raw_compare u1 u2
      | Access _, _ -> -1
      | _, Access _ -> 1
      | Record (lbs1, _), Record (lbs2, _) ->
	  raw_compare_list lbs1 lbs2
  and raw_compare_list l1 l2 = 
    match l1, l2 with
      | [], [] -> 0
      | [], _ -> 1
      | _, [] -> -1
      | (_, x1)::l1, (_, x2)::l2 -> 
	let c = raw_compare x1 x2 in 
	if c<>0 then c else raw_compare_list l1 l2
  
  let rec normalize v =
    match v with
      | Record (lbs, ty) ->
	  begin
	    let lbs_n = List.map (fun (lb, x) -> lb, normalize x) lbs in
	    match lbs_n with
	      | (lb1, Access(lb2, x, _)) :: l when Hstring.equal lb1 lb2 ->
		  if List.for_all 
		    (function 
		       | (lb1, Access(lb2, y, _)) -> 
			   Hstring.equal lb1 lb2 && raw_compare x y = 0
		       | _ -> false) l 
		  then x
		  else Record (lbs_n, ty)
	      | _ -> Record (lbs_n, ty)
	  end
      | Access (a, x, ty) ->
	  begin 
	    match normalize x with 
	      | Record (lbs, _) -> Hstring.list_assoc a lbs
	      | x_n -> Access (a, x_n, ty)
	  end
      | Other _ -> v

  let compare t u = raw_compare (normalize t) (normalize u)
	
  let is_mine t =
    match normalize t with
      | Other(r, _) -> r
      | x -> X.embed x

  let make t = 
    let rec make_rec t ctx = 
      let { Term.f = f; xs = xs; ty = ty} = Term.view t in
      match f, ty with
	| Symbols.Op (Symbols.Record), Ty.Trecord {Ty.lbs=lbs} ->
	    assert (List.length xs = List.length lbs);
	    let l, ctx = 
	      List.fold_right2 
		(fun x (lb, _) (l, ctx) -> 
		   let r, ctx = make_rec x ctx in (lb, r)::l, ctx) 
		xs lbs ([], ctx)
	    in
	    Record (l, ty), ctx
	| Symbols.Op (Symbols.Access a), _ ->
	    begin
	      match xs with
		| [x] -> 
		    let r, ctx = make_rec x ctx in
		    Access (a, r, ty), ctx
		| _ -> assert false
	    end
	| _, _ -> 
	    let r, ctx' = X.make t in
	    Other (r, ty), ctx'@ctx
    in
    let r, ctx = make_rec t [] in
    is_mine r, ctx

  let color _ = assert false
    
  let embed r =
    match X.extract r with
      | Some p -> p
      | None -> Other(r, X.type_info r)

  let xs_of_list = List.fold_left (fun s x -> XS.add x s) XS.empty

  let leaves t = 
    let rec leaves t = 
      match normalize t with
	| Record (lbs, _) -> 
	    List.fold_left (fun s (_, x) -> XS.union (leaves x) s) XS.empty lbs
	| Access (_, x, _) -> leaves x
	| Other (x, _) -> xs_of_list (X.leaves x)
    in
    XS.elements (leaves t)

  let rec hash  = function
    | Record (lbs, ty) ->
	List.fold_left 
	  (fun h (lb, x) -> 17 * hash x + 13 * Hstring.hash lb + h) 
	  (Ty.hash ty) lbs
    | Access (a, x, ty) ->
	19 * hash x + 17 * Hstring.hash a + Ty.hash ty 
    | Other (x, ty) -> 
	Ty.hash ty + 23 * X.hash x

  let rec subst_rec p v r = 
    match r with
      | Other (t, ty) -> 
	  embed (if X.compare p t = 0 then v else X.subst p v t)
      | Access (a, t, ty) ->
	  Access (a, subst_rec p v t, ty)
      | Record (lbs, ty) ->
	  let lbs = List.map (fun (lb, t) -> lb, subst_rec p v t) lbs in
	  Record (lbs, ty)

  let subst p v r = is_mine (subst_rec p v r)
      
  let is_mine_symb =  function 
    | Symbols.Op (Symbols.Record | Symbols.Access _) -> true
    | _ -> false
	
  let unsolvable _ = false

  let type_info = function
    | Record (_, ty) | Access (_, _, ty) | Other (_, ty) -> ty

  (* Shostak'pair solver adapted to records *)

  let mk_fresh_record x info = 
    let ty = type_info x in
    let lbs = match ty with Ty.Trecord r -> r.Ty.lbs | _ -> assert false in
    let lbs = 
      List.map 
	(fun (lb, ty) -> 
	   match info with
	     | Some (a, v) when Hstring.equal lb a -> lb, v 
	     | _ -> let n = embed (X.term_embed (Term.fresh_name ty)) in lb, n)
	lbs
    in
    Record (lbs, ty), lbs

  let rec occurs x = function
    | Record (lbs, _) ->
	List.exists (fun (_, v) -> occurs x v) lbs
    | Access (_, v, _) -> occurs x v
    | Other _ as v -> compare x v = 0

  let direct_args_of_labels x = List.exists (fun (_, y) -> compare x y = 0) 

  let rec subst_access x s e = 
    match e with
      | Record (lbs, ty) -> 
	  Record (List.map (fun (n,e') -> n, subst_access x s e') lbs, ty)
      | Access (lb, e', _) when compare e e' = 0 -> 
	  Hstring.list_assoc lb s
      | Access (lb', e', ty) -> Access (lb', subst_access x s e', ty)
      | Other _ -> e

  let rec find_list x = function
    | [] -> raise Not_found
    | (y, t) :: _ when compare x y = 0 -> t
    | _ :: l -> find_list x l

  let split l = 
    let rec split_rec acc = function
      | [] -> acc, []
      | ((x, t) as v) :: l -> 
	  try acc, (t, find_list x acc) :: l 
	  with Not_found -> split_rec (v::acc) l
    in
    split_rec [] l

  let rec solve_one u v =
    if compare u v = 0 then [] else
      match u, v with
	| Access (a, x, _), v | v, Access (a, x, _) ->
	    let nr, _ = mk_fresh_record x (Some(a,v)) in
	    solve_one x nr

	| Record (lbs1, _), Record (lbs2, _) ->
	    let l = 
	      List.fold_left2 
		(fun l (_, x) (_, y) -> (solve_one x y)@l) [] lbs1 lbs2
	    in 
	    resolve l

	| (Record (lbs, _) as w), (Other _ as x) 
	| (Other _ as x), (Record (lbs, _) as w) ->
	    if not (occurs x w) then [x, w]
	    else if direct_args_of_labels x lbs then raise Exception.Unsolvable
	    else 
	      let nr, sigma = mk_fresh_record w None in
	      let l = 
		List.fold_left2
		  (fun l (_, ai) (_, ei) -> 
		     (solve_one ai (subst_access x sigma ei))@l) [] sigma lbs
	      in
	      (x, nr)::resolve l

	| Other _, Other _ -> [u, v]
	    
  and resolve l = 
    let s, r = split l in
    match r with [] -> s | (u, v) :: l -> resolve (s@(solve_one u v)@l)

  let solve r1 r2 = 
    let r1 = normalize (embed r1) in
    let r2 = normalize (embed r2) in
    List.map (fun (x, y) -> is_mine x, is_mine y) (solve_one r1 r2)

  let fully_interpreted _ = false

  let rec term_extract r = 
    match X.extract r with
      | Some v -> begin match v with
	  | Record (lbs, ty) -> 
	      begin try
		let lbs = 
		  List.map 
		    (fun (_, r) -> 
		       match term_extract (is_mine r) with 
			 | None -> raise Not_found
			 | Some t -> t) lbs in
		Some (Term.make (Symbols.Op Symbols.Record) lbs ty)
	      with Not_found -> None
	      end
	  | Access (a, r, ty) ->
	      begin
		match X.term_extract (is_mine r) with
		  | None -> None
		  | Some t -> 
		      Some (Term.make (Symbols.Op (Symbols.Access a)) [t] ty)
	      end
	  | Other (r, _) -> X.term_extract r
	end
      | None -> X.term_extract r

          
  module Rel =
  struct
    type r = X.r
    type t = unit
    exception Inconsistent    
    let empty _ = ()
    let assume _ _ ~are_eq ~are_neq ~class_of ~find =
      (), { assume = []; remove = []}
    let query _ _ ~are_eq ~are_neq ~class_of ~find = Sig.No
    let case_split env = []
    let add env _ = env
  end
end
