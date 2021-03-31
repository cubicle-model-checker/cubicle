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
open Exception  
module Sy = Symbols
module T  = Term
module A  = Literal
module L  = List
module Hs = Hstring
module Ex = Explanation

type 'a abstract = Cons of Hs.t * Ty.t |  Alien of 'a

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end

module Make(X : ALIEN) = struct

  type t = X.r abstract
  type r = X.r

  let name = "Sum"
  
  let unsolvable _ = false
  
  let is_mine_a _ = false
  
  let is_mine_symb = function 
    | Sy.Name(_, Sy.Constructor) -> true 
    | _ -> false
        
  let fully_interpreted sb = true

  let type_info = function
    | Cons (_, ty) -> ty
    | Alien x -> X.type_info x
        
  let is_mine_type c = match type_info c with
    | Ty.Tsum _ -> true 
    | _ -> false
        
  let color _ = assert false
  
  let print fmt = function
    | Cons (hs,ty) -> fprintf fmt "%s" (Hs.view hs)
    | Alien x -> fprintf fmt "%a" X.print x

  let embed r =
    match X.extract r with
      | Some c -> c
      | None -> Alien r 

  let is_mine = function
    | Alien r -> r
    | Cons(hs,ty) as c -> X.embed c
        
  let compare c1 c2 = 
    match c1 , c2 with
      | Cons (h1,ty1) , Cons (h2,ty2)  -> 
          let n = Hs.compare h1 h2 in
          if n <> 0 then n else Ty.compare ty1 ty2
      | Alien r1, Alien r2 -> X.compare r1 r2
      | Alien _ , Cons _   -> 1
      | Cons _  , Alien _  -> -1
    
  let hash = function
    | Cons (h, ty) -> Hstring.hash h + 19 * Ty.hash ty
    | Alien r -> X.hash r

  let leaves _ = []

  let subst p v c = 
    let cr = is_mine c in
    if X.equal p cr then v
    else 
      match c with
        | Cons(hs,t) -> cr
        | Alien r    -> X.subst p v r
    
  let make t = match T.view t with
    | {T.f=Sy.Name(hs, Sy.Constructor); xs=[];ty=ty} ->
        is_mine (Cons(hs,ty)), []
    | _ -> assert false
        
  let solve a b = 
    match embed a, embed b with
      | Cons(c1,_) , Cons(c2,_) when Hs.equal c1 c2 -> []
      | Cons(c1,_) , Cons(c2,_) -> raise Unsolvable
      | Cons _     , Alien r2   -> [r2,a]
      | Alien r1   , Cons _     -> [r1,b]
      | Alien _    , Alien _    -> assert false

  let term_extract _ = None

  let term_extract t =
    match X.extract t with
      | Some v ->
	begin
	   match v with
	    | Cons (hs, ty) ->
	      Some (T.make (Symbols.Name(hs, Symbols.Constructor)) [] ty)
	    | Alien a -> X.term_extract a
	end
      | None -> X.term_extract t

  module Rel = struct
    type r = X.r

    exception Not_Cons

    module Ex = Explanation

    module MX = Map.Make(struct type t = X.r include X end)
    module HSS = Set.Make (struct type t=Hs.t let compare = Hs.compare end)

    type t = (HSS.t * Ex.t) MX.t

    let empty () = MX.empty

    module Debug = struct

      let assume bol r1 r2 = ()

        let print_env env = ()

    end

    let values_of r = match X.type_info r with
      | Ty.Tsum (_,l) -> 
        Some (List.fold_left (fun st hs -> HSS.add hs st) HSS.empty l)
      | _ -> None

    let add_diseq hss sm1 sm2 dep env eqs = 
      match sm1, sm2 with
        | Alien r , Cons(h,ty) 
        | Cons (h,ty), Alien r  ->
	  (*h is the constructor itself, ty is the type it belongs to *)
	  (* h = Idle and ty = t *)

          let enum, ex = try MX.find r env with Not_found -> hss, Ex.empty in
          let enum = HSS.remove h enum in
	  (*unbind h in enum *)
          let ex = Ex.union ex dep in
	  (*combine explanations*)
          if HSS.is_empty enum then raise (Inconsistent ex)
	  (* if every binding has been removed -> oops *)
          else
	    (*there are still bindings left*)
            let env = MX.add r (enum, ex) env in
	    (* bind (alien) r to (enum, ex) - values that the term r can have - in env*)
            if HSS.cardinal enum = 1 then
	      (*if there is only on possible value, then pick that value and add the
		new equality to all of the equalities
	      *)
              let h' = HSS.choose enum in
              env, (LSem (A.Eq(r, is_mine (Cons(h',ty)))), ex)::eqs
	    (*if there's more than one thing in enum*)
            else env, eqs
              
        | Alien r1   , Alien r2   -> env, eqs
        |  _ -> env, eqs

    let add_eq hss sm1 sm2 dep env eqs =
      match sm1, sm2 with
        | Alien r, Cons(h,ty) | Cons (h,ty), Alien r  ->
	  (*find the term r in the environment*)
          let enum, ex = try MX.find r env with Not_found -> hss, Ex.empty in
	  (*combine explanations*)
          let ex = Ex.union ex dep in
	  (*if the constructor h isn't a possible value -> oops*)
          if not (HSS.mem h enum) then raise (Inconsistent ex);
	  (* specifically add that r is equal to this one constructor in the env*)
	  MX.add r (HSS.singleton h, ex) env, eqs
            
        | Alien r1, Alien r2   -> 
	  (*try to find the two r's in the environment*)
          let enum1,ex1 = try MX.find r1 env with Not_found -> hss, Ex.empty in
          let enum2,ex2 = try MX.find r2 env with Not_found -> hss, Ex.empty in
	  (*combine the explanations*)
          let ex = Ex.union dep (Ex.union ex1 ex2) in
	  (* the intersection of the two sets of possible values *)
          let diff = HSS.inter enum1 enum2 in
	  (*at least one value must be common*)
          if HSS.is_empty diff then raise (Inconsistent ex); 
	  (*r1/r2 is equal to this intersection in the environment*)
          let env = MX.add r1 (diff, ex) env in
          let env = MX.add r2 (diff, ex) env in
          if HSS.cardinal diff = 1 then
	    (*if there's only one possible value then it can be added to the eqs to be assumed*)
            let h' = HSS.choose diff in
            let ty = X.type_info r1 in
            env, (LSem (A.Eq(r1, is_mine (Cons(h',ty)))), ex)::eqs
          else env, eqs

        |  _ -> env, eqs

    let assume env la = 
      let aux bol r1 r2 dep env eqs = function
        | None     -> env, eqs
        | Some hss -> 
            Debug.assume bol r1 r2;
            if bol then 
              add_eq hss (embed r1) (embed r2) dep env eqs
            else
              add_diseq hss (embed r1) (embed r2) dep env eqs
      in
      Debug.print_env env;
      let env, eqs = 
	List.fold_left
          (fun (env,eqs) -> function
            | A.Eq(r1,r2), _, ex ->
		 (*if the element is an equality*)
		 (*values_of -> all the possible constructors for r1's type*)
		 (* if r1's type isn't a sum type, then you get None from the fct*)
		 aux true  r1 r2 ex env eqs (values_of r1)
		   
            | A.Distinct(false, [r1;r2]), _, ex ->
		 aux false r1 r2 ex env eqs (values_of r1)
		   
             | _ -> env, eqs
		 
          ) (env,[]) la
      in
      env, { assume = eqs; remove = [] }

    (* XXXXXX : TODO -> ajouter les explications dans les choix du
       case split *)

    let case_split env =
      (*fold on the map of thing = stuff *)
      let acc = MX.fold
        (fun r (hss, ex) acc ->
          let sz = HSS.cardinal hss in
	  (*if the thing is only equal to one stuff, 
	    don't do anything, no reason to case-split
	  *)
          if sz = 1 then acc
	   (* if there's multiple stuff*)
          else match acc with
	     (* if there's something smaller in my acc then nothing*)
            | Some (n,r,hs) when n <= sz -> acc
	     (* otherwise pick something*)
             | _ ->   Some (sz, r, HSS.choose hss)
        ) env None
      in
      match acc with
        | Some (n,r,hs) ->
	  
          let r' = is_mine (Cons(hs,X.type_info r)) in
            [A.Eq(r, r'), Ex.empty, Num.Int n]
        | None -> []
      

    let query env a_ex =
      try ignore(assume env [a_ex]); Sig.No
      with Inconsistent expl -> Sig.Yes expl          

    let add env r = match embed r, values_of r with
      | Alien r, Some hss -> 
          if MX.mem r env then env else 
            MX.add r (hss, Ex.empty) env

      | _ -> env

  end
end
