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
		 lbs : (Hstring.t * t) list}

and t = 
  | Tint
  | Treal
  | Tbool
  | Tabstract of Hstring.t
  | Tsum of Hstring.t * Hstring.t list
  | Trecord of trecord

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
    | _ -> Hashtbl.hash t
      
let rec equal t1 t2 = 
  match t1, t2 with
    | Tabstract s1, Tabstract s2 
    | Tsum (s1, _), Tsum (s2, _)
      ->
	Hstring.equal s1 s2
    | Tint, Tint | Treal, Treal | Tbool, Tbool -> true
    | Trecord {name=s1;lbs=l1}, Trecord {name=s2;lbs=l2} ->
      begin
	try 
	  Hstring.equal s1 s2  &&
	    List.for_all2 
	    (fun (l1, ty1) (l2, ty2) -> 
	      Hstring.equal l1 l2 && equal ty1 ty2) l1 l2
	with Invalid_argument _ -> false
      end
    | _ -> false
	
let rec compare t1 t2 = 
  match t1, t2 with
    | Tabstract s1, Tabstract s2 ->
	Hstring.compare s1 s2 
    | Tabstract _, _ -> -1 | _ , Tabstract _ -> 1
    | Tsum (s1, _), Tsum(s2, _) ->
	Hstring.compare s1 s2
    | Tsum _, _ -> -1 | _ , Tsum _ -> 1
    | Trecord {name=s1;lbs=l1},Trecord {name=s2;lbs=l2} ->
      let c = Hstring.compare s1 s2 in
      if c <> 0 then c else
	  let l1, l2 = List.map snd l1, List.map snd l2 in
	  compare_list l1 l2
    | Trecord _, _ -> -1 | _ , Trecord _ -> 1

      
    | t1, t2 -> Pervasives.compare t1 t2

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
    | Tsum (s, _) -> fprintf fmt "%s" (Hstring.view s)
    | Trecord {name = n; lbs = lbs} ->
      fprintf fmt "record %a = { " Hstring.print n;
      List.iter (fun (x,y) -> fprintf fmt "%a : %a; " Hstring.print x print y) lbs;
      fprintf fmt "}"
