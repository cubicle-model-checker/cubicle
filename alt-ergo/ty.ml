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

open Hashcons
open Format

type t = 
    | Tint
    | Treal
    | Tbool
    | Tunit
    | Tvar of tvar
    | Tbitv of int
    | Text of t list * Hstring.t
    | Tfarray of t * t
    | Tnext of t
    | Tsum of Hstring.t * Hstring.t list
    | Trecord of trecord

and tvar = { v : int ; mutable value : t option }
and trecord = { 
  mutable args : t list; 
  name : Hstring.t; 
  mutable lbs :  (Hstring.t * t) list
}

exception TypeClash of t*t
exception Shorten of t


(* smart constructors *)

let tunit = Text ([],Hstring.make "unit")

let text l s = Text (l,Hstring.make s)

let tsum s lc = Tsum (Hstring.make s, List.map Hstring.make lc)

let trecord lv n lbs = 
  let lbs = List.map (fun (l,ty) -> Hstring.make l, ty) lbs in
  let lbs = List.sort (fun (l1, _) (l2, _) -> Hstring.compare l1 l2) lbs in
  Trecord { args = lv; name = Hstring.make n; lbs = lbs}

let shorten t = 
  let h = Hashtbl.create 17 in
  let rec shorten t = 
    match t with
      | Tvar {value=None}  -> t
      | Tvar {value=Some(Tvar{value=None} as t')} -> t'
      | Tvar ({value=Some(Tvar t2)} as t1) -> t1.value <- t2.value; shorten t
      | Tvar {v = n; value = Some t'} -> 
	  (try Hashtbl.find h n 
	   with Not_found -> Hashtbl.add h n t'; shorten t')
      | Text (l,s) -> Text(List.map shorten l,s)
      | Tfarray (t1,t2) -> Tfarray(shorten t1,shorten t2)
      | Trecord r -> 
	  r.args <- List.map shorten r.args;
	  r.lbs <- List.map (fun (lb, ty) -> lb, shorten ty) r.lbs;
	  t
      | _ -> t
  in
  shorten t

let fresh_var = 
  let cpt = ref (-1) in
  fun () -> incr cpt; {v= !cpt ; value = None }

let fresh_empty_text =
  let cpt = ref (-1) in
  fun () -> incr cpt; text [] ("'_c"^(string_of_int !cpt))

let memo1 ff = 
  let h = Hashtbl.create 17 in
  let rec f x = 
    try Hashtbl.find h x 
    with Not_found -> let v = ff f x in Hashtbl.add h x v; v
  in 
  f

let memo2 ff = 
  let h = Hashtbl.create 17 in
  let rec f x y = 
    try Hashtbl.find h (x, y) 
    with Not_found -> let v = ff f x y in Hashtbl.add h (x, y) v; v
  in 
  f

let hash = memo1
  (fun hash t -> match t with
     | Tvar{v=v} -> v
     | Text(l,s) -> 
	 abs (List.fold_left (fun acc x-> acc*19 + hash x) (Hstring.hash s) l)
     | Tfarray (t1,t2) -> 19 * (hash t1) + 23 * (hash t2)
     | Trecord { args = args; name = s; lbs = lbs} ->
	 let h = 
	   List.fold_left (fun h ty -> 27 * h + hash ty) (Hstring.hash s) args 
	 in
	 let h = 
	   List.fold_left 
	     (fun h (lb, ty) -> 23 * h + 19 * (Hstring.hash lb) + hash ty)
	     (abs h) lbs
	 in 
	 abs h
     | Tsum (s, l) -> 
	 let h = 
	   List.fold_left 
	     (fun h x -> 13 * h + Hstring.hash x) (Hstring.hash s) l
	 in
	 abs h
     | _ -> Hashtbl.hash t)

let equal = 
  memo2 
    (fun equal t1 t2 -> match shorten t1 , shorten t2 with
       | Tvar{v=v1}, Tvar{v=v2} -> v1 = v2
       | Text(l1, s1), Text(l2, s2) ->
	   (try s1.tag = s2.tag && List.for_all2 equal l1 l2
	    with Invalid_argument _ -> false)
       | Tfarray (ta1, ta2), Tfarray (tb1, tb2) -> 
	   equal ta1 tb1 && equal ta2 tb2
       | Tsum (s1, _), Tsum (s2, _) -> Hstring.equal s1 s2
       | Trecord {args=a1;name=s1;lbs=l1}, Trecord {args=a2;name=s2;lbs=l2} ->
	   begin
	     try 
	       Hstring.equal s1 s2 && List.for_all2 equal a1 a2 &&
		 List.for_all2 
		 (fun (l1, ty1) (l2, ty2) -> 
		    Hstring.equal l1 l2 && equal ty1 ty2) l1 l2
	     with Invalid_argument _ -> false
	   end
       | Tint, Tint | Treal, Treal | Tbool, Tbool | Tunit, Tunit -> true
       | Tbitv n1, Tbitv n2 -> n1 =n2
       | Tnext t1, Tnext t2 -> equal t1 t2
       | _ -> false)

let compare t1 t2 = 
  let h = Hashtbl.create 17 in
  let rec compare t1 t2 = match shorten t1 , shorten t2 with
    | Tvar{v=v1} , Tvar{v=v2} -> Pervasives.compare v1 v2
    | Tvar _, _ -> -1 | _ , Tvar _ -> 1
    | Text(l1, s1) , Text(l2, s2) ->
	let c = Hstring.compare s1 s2 in
	if c<>0 then c
	else compare_list l1 l2
    | Text _, _ -> -1 | _ , Text _ -> 1
    | Tfarray (ta1,ta2), Tfarray (tb1,tb2) ->
	let c = compare_m ta1 tb1 in
	if c<>0 then c
	else compare_m ta2 tb2
    | Tfarray _, _ -> -1 | _ , Tfarray _ -> 1
    | Tsum(s1, _), Tsum(s2, _) ->
	Hstring.compare s1 s2
    | Tsum _, _ -> -1 | _ , Tsum _ -> 1
    | Trecord {args=a1;name=s1;lbs=l1},Trecord {args=a2;name=s2;lbs=l2} ->
	let c = Hstring.compare s1 s2 in
	if c <> 0 then c else
	  let c = compare_list a1 a2 in
	  if c <> 0 then c else
	    let l1, l2 = List.map snd l1, List.map snd l2 in
	    compare_list l1 l2
    | Trecord _, _ -> -1 | _ , Trecord _ -> 1
    | t1 , t2 -> Pervasives.compare t1 t2
  and compare_list l1 l2 = match l1, l2 with
    | [] , [] -> 0
    | [] , _ -> -1
    | _ , [] -> 1
    | x::ll1 , y::ll2 -> 
	let c = compare_m x y in
	if c<>0 then c else compare_list ll1 ll2
  and compare_m t1 t2 = 
    try Hashtbl.find h (t1, t2)
    with Not_found -> let v = compare t1 t2 in Hashtbl.add h (t1, t2) v; v
  in compare t1 t2

let occurs {v=n} t = 
  let rec occursrec = function
      Tvar {v=m} -> n=m
    | Text(l,_) -> List.exists occursrec l
    | Tfarray (t1,t2) -> occursrec t1 || occursrec t2
    | _ -> false
  in occursrec t 

(*** destructive unification ***)
let rec unify t1 t2 = 
  let t1 = shorten t1 in
  let t2 = shorten t2 in
  match t1 , t2 with
      Tvar ({v=n;value=None} as tv1), Tvar {v=m;value=None} ->
	if n<>m then tv1.value <- Some t2
    | _ ,  Tvar ({value=None} as tv) -> 
	if (occurs tv t1) then raise (TypeClash(t1,t2));
	tv.value <- Some t1
    | Tvar ({value=None} as tv) , _ -> 
	  if (occurs tv t2) then raise (TypeClash(t1,t2));
	tv.value <- Some t2
    | Text(l1,s1) , Text(l2,s2) when Hstring.equal s1 s2 ->
	List.iter2 unify l1 l2
    | Tfarray (ta1,ta2), Tfarray (tb1,tb2) -> unify ta1 tb1;unify ta2 tb2
    | Trecord r1, Trecord r2 when Hstring.equal r1.name r2.name -> 
	List.iter2 unify r1.args r2.args
    | Tsum(s1, _) , Tsum(s2, _) when Hstring.equal s1 s2 -> ()
    | Tint, Tint | Tbool, Tbool | Treal, Treal | Tunit, Tunit -> ()
    | Tbitv n , Tbitv m when m=n -> ()
    | _ , _ -> 
	raise (TypeClash(t1,t2))


(*** matching with a substitution mechanism ***)
module M = Map.Make(struct type t=int let compare = Pervasives.compare end)
type subst = t M.t

let esubst = M.empty

let matching s pat t =
  let h = Hashtbl.create 17 in
  let rec matching s pat t = 
    match pat , t with
      | Tvar {v=n;value=None} , _ -> 
	  (try if not (equal (M.find n s) t) then raise (TypeClash(pat,t)); s
	   with Not_found -> M.add n t s)
      | Tvar {value=_}, _ -> raise (Shorten pat)
      | Text (l1,s1) , Text (l2,s2) when Hstring.equal s1 s2 ->
	  List.fold_left2 matching_m s l1 l2 
      | Tfarray (ta1,ta2), Tfarray (tb1,tb2) ->
	  matching_m (matching_m s ta1 tb1) ta2 tb2
      | Trecord r1, Trecord r2 when Hstring.equal r1.name r2.name ->
	  let s = List.fold_left2 matching_m s r1.args r2.args in
	  List.fold_left2 
	    (fun s (_, p) (_, ty) -> matching_m s p ty) s r1.lbs r2.lbs
      | Tsum (s1, _), Tsum (s2, _) when Hstring.equal s1 s2 -> s
      | Tint , Tint | Tbool , Tbool | Treal , Treal | Tunit, Tunit -> s
      | Tbitv n , Tbitv m when n=m -> s
      | _ , _ -> raise (TypeClash(pat,t))
  and matching_m s pat t = 
    try Hashtbl.find h (s, pat, t)
    with Not_found -> 
      let v = matching s pat t in
      Hashtbl.add h (s, pat, t) v; v
  in
  matching s pat t

let apply_subst = 
  memo2
    (fun apply_subst s ty ->
       match ty with
	 | Tvar {v=n} -> 
	     (try M.find n s with Not_found -> ty)
	 | Text (l,e) -> Text(List.map (apply_subst s) l,e)
	 | Tfarray (t1,t2) -> Tfarray (apply_subst s t1,apply_subst s t2)
	 | Trecord r -> 
	     let lbs = List.map (fun (x,t) -> x, apply_subst s t) r.lbs in
	     Trecord 
	       {args = List.map (apply_subst s) r.args; 
		name = r.name; 
		lbs = lbs}
	 | t -> t)

let instantiate lvar lty ty = 
  let s = 
    List.fold_left2 
      (fun s x t -> 
	 match x with 
	   | Tvar {v=n} -> 
	       M.add n t s
	   | _ -> assert false) M.empty lvar lty 
  in
  apply_subst s ty

let union_subst s1 s2 = 
  M.fold (fun k x s2 -> M.add k x s2) (M.map (apply_subst s2)  s1) s2

let compare_subst = M.compare Pervasives.compare

let rec fresh ty subst = 
  match ty with
    | Tvar {v=x} -> 
	begin
	  try M.find x subst, subst
	  with Not_found -> 
	    let nv = Tvar (fresh_var()) in 
	    nv, M.add x nv subst
	end
    | Text (args, n) -> 
	let args, subst = fresh_list args subst in
	Text (args, n), subst
    | Tfarray (ty1, ty2) -> 
	let ty1, subst = fresh ty1 subst in
	let ty2, subst = fresh ty2 subst in
	Tfarray (ty1, ty2), subst
    | Trecord {args = args; name = n; lbs = lbs} -> 
	let args, subst = fresh_list args subst in
	let lbs, subst = 
	  List.fold_right 
	    (fun (x,ty) (lbs, subst) -> 
	       let ty, subst = fresh ty subst in	   
	       (x, ty)::lbs, subst) lbs ([], subst)
	in
	Trecord { args = args; name = n; lbs = lbs}, subst
    | t -> t, subst
and fresh_list lty subst = 
  List.fold_right 
    (fun ty (lty, subst) -> 
       let ty, subst = fresh ty subst in	   
       ty::lty, subst) lty ([], subst)

module Svty = 
  Set.Make(struct type t = int let compare = Pervasives.compare end)

let vty_of t = 
  let rec vty_of_rec acc t = 
    let t = shorten t in
    match t with
      | Tvar { v = i ; value = None } -> Svty.add i acc 
      | Text(l,_) -> List.fold_left vty_of_rec acc l
      | Tfarray (t1,t2) -> vty_of_rec (vty_of_rec acc t1) t2
      | Trecord {args = args; name = s; lbs = lbs} ->
	  let acc = List.fold_left vty_of_rec acc args in
	  List.fold_left (fun acc (_, ty) -> vty_of_rec acc ty) acc lbs
      | _ -> acc
  in
  vty_of_rec Svty.empty t

let monomorphize = 
  memo1 
    (fun monomorphize ty ->
       match ty with 
	 | Tint | Treal | Tbool | Tunit   | Tbitv _  | Tsum _ -> ty
	 | Text (tyl,hs) -> Text (List.map monomorphize tyl, hs)
	 | Trecord {args = tylv; name = n; lbs = tylb} ->
	     let m_tylv = List.map monomorphize tylv in
	     let m_tylb = 
	       List.map (fun (lb, ty_lb) -> lb, monomorphize ty_lb) tylb 
	     in
	     Trecord {args = m_tylv; name = n; lbs = m_tylb}
	 | Tfarray (ty1,ty2)    -> Tfarray (monomorphize ty1,monomorphize ty2)
	 | Tnext ty    -> Tnext (monomorphize ty)
	 | Tvar {v=v; value=None} -> text [] ("'_c"^(string_of_int v))
	 | Tvar ({value=Some ty1} as r) -> 
	     Tvar { r with value = Some (monomorphize ty1)})

(*** pretty print ***)
let print fmt ty = 
  let h = Hashtbl.create 17 in
  let rec print fmt = function
    | Tint -> fprintf fmt "int"
    | Treal -> fprintf fmt "real"
    | Tbool -> fprintf fmt "bool"
    | Tunit -> fprintf fmt "unit"
    | Tbitv n -> fprintf fmt "bitv[%d]" n
    | Tvar{v=v ; value = None} -> fprintf fmt "'a_%d" v
    | Tvar{v=v ; value = Some (Trecord {args=l; name=n} as t) } -> 
	if Hashtbl.mem h v then
	  fprintf fmt "%a%s" printl l (Hstring.view n)
	else
	  (Hashtbl.add h v (); 
	   (*fprintf fmt "('a_%d->%a)" v print t *)
	   print fmt t)
    | Tvar{v=v ; value = Some t} -> 
	    (*fprintf fmt "('a_%d->%a)" v print t *)
	    print fmt t
    | Text(l, s) -> fprintf fmt "%a%s" printl l (Hstring.view s)
    | Tfarray (t1, t2) -> fprintf fmt "(%a,%a) farray" print t1 print t2
    | Tnext t -> fprintf fmt "%a next" print t
    | Tsum(s, _) -> fprintf fmt "%s" (Hstring.view s)
    | Trecord {args=lv; name=n; lbs=lbls} -> 
	fprintf fmt "%a%s = {" printl lv (Hstring.view n);
	List.iter 
	  (fun (s, t) -> 
	     fprintf fmt "%s : %a; " (Hstring.view s) print t) lbls;
	fprintf fmt "}"
	  
  and printl fmt = function
      [] -> ()
    | [t] -> fprintf fmt "%a " print t
    | t::l -> fprintf fmt "%a,%a" print t printl l
  in 
  print fmt ty


let print_subst fmt sbt = 
  M.iter (fun n ty -> fprintf fmt "%d -> %a" n print ty) sbt;
  fprintf fmt "@?";
