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

type trecord = { name : Hstring.t;
		 lbs : (Hstring.t * t) list;
	       (*null : bool*)
	       }

and t = 
  | Tint
  | Treal
  | Tbool
  | Tabstract of Hstring.t
  | Tsum of Hstring.t * Hstring.t list
  | Trecord of trecord
  | Tnull of trecord
  | Tbitv of int
  | Text of t list * Hstring.t
  | Tfarray of t * t
  | Tnext of t

let rec hash t =
  match t with
    | Tabstract s -> Hstring.hash s
    | Tsum (s, l) -> 
	let h = 
	  List.fold_left 
	    (fun h x -> 13 * h + Hstring.hash x) (Hstring.hash s) l
	in
	abs h
    | Trecord { name = s; lbs = lbs} ->
      let h = 
	List.fold_left 
	  (fun h (lb, ty) -> 23 * h + 19 * (Hstring.hash lb) + hash ty)
	  (Hstring.hash s) lbs
      in 
      abs h
    | Text(l,s) -> 
      abs (List.fold_left (fun acc x-> acc*19 + hash x) (Hstring.hash s) l)
    | Tfarray (t1,t2) -> 19 * (hash t1) + 23 * (hash t2)
	
    | _ -> Hashtbl.hash t
      
let rec equal t1 t2 = 
  match t1, t2 with
    | Tabstract s1, Tabstract s2 
    | Tsum (s1, _), Tsum (s2, _)
      ->
	Hstring.equal s1 s2
    | Tint, Tint | Treal, Treal | Tbool, Tbool -> true
    | Trecord {name=s1;lbs=l1; (*null = false*)}, Trecord {name=s2;lbs=l2; (*null = false*)} ->
      begin
	try 
	  Hstring.equal s1 s2  &&
	    List.for_all2 
	    (fun (l1, ty1) (l2, ty2) -> 
	      Hstring.equal l1 l2 && equal ty1 ty2) l1 l2
	with Invalid_argument _ -> false
      end

    | Text(l1, s1), Text(l2, s2) ->
      (try s1.tag = s2.tag && List.for_all2 equal l1 l2
       with Invalid_argument _ -> false)
    | Tfarray (ta1, ta2), Tfarray (tb1, tb2) -> 
      equal ta1 tb1 && equal ta2 tb2
    | Tbitv n1, Tbitv n2 -> n1 =n2
    | Tnext t1, Tnext t2 -> equal t1 t2
	
    | _ -> false
	
let rec compare t1 t2 = 
  match t1, t2 with
    | Tabstract s1, Tabstract s2 ->
	Hstring.compare s1 s2 
    | Tabstract _, _ -> -1 | _ , Tabstract _ -> 1
    | Tsum (s1, _), Tsum(s2, _) ->
	Hstring.compare s1 s2
    | Tsum _, _ -> -1 | _ , Tsum _ -> 1
    (*| Trecord { null = true} , Trecord {null = true } -> -1
    | Trecord {null = true}, _ -> -1 | _, Trecord { null = true} -> 1*)
    | Trecord {name=s1;lbs=l1; (*null = false*)},Trecord {name=s2;lbs=l2; (*null = false*)} ->
      let c = Hstring.compare s1 s2 in
      if c <> 0 then c else
	  let l1, l2 = List.map snd l1, List.map snd l2 in
	  compare_list l1 l2
    | Trecord _, _ -> -1 | _ , Trecord _ -> 1

    | Text(l1, s1) , Text(l2, s2) ->
      let c = Hstring.compare s1 s2 in
      if c<>0 then c
      else compare_list l1 l2
    | Text _, _ -> -1 | _ , Text _ -> 1
    | Tfarray (ta1,ta2), Tfarray (tb1,tb2) ->
      let c = compare ta1 tb1 in
      if c<>0 then c
      else compare ta2 tb2
    | Tfarray _, _ -> -1 | _ , Tfarray _ -> 1
      
      
    | t1, t2 -> Stdlib.compare t1 t2

and compare_list l1 l2 = match l1, l2 with
  | [] , [] -> 0
  | [] , _ -> -1
  | _ , [] -> 1
  | x::ll1 , y::ll2 -> 
    let c = compare x y in
    if c<>0 then c else compare_list ll1 ll2

let rec print fmt ty = 
  match ty with
    | Tint -> fprintf fmt "int"
    | Treal -> fprintf fmt "real"
    | Tbool -> fprintf fmt "bool"
    | Tabstract s -> fprintf fmt "%s" (Hstring.view s)
    | Tsum (s, sl) -> fprintf fmt "%s" (Hstring.view s);
      if Options.debug_subtypes then
	begin
	  fprintf fmt " (= ";
	  List.iter (fprintf fmt "| %a " Hstring.print) sl;
	  fprintf fmt ")"   
	end
    | Trecord {name = n; lbs = lbs;(* null = null*)} ->
      (*if null then*)
	begin
	  fprintf fmt "record %a = { " Hstring.print n;
	  List.iter (fun (x,y) -> fprintf fmt "%a : %a; " Hstring.print x print y) lbs;
	  fprintf fmt "}"
	end
    | _ -> ()
(*      else
	fprintf fmt "record %a = Null " Hstring.print n; *)
