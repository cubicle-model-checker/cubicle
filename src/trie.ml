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

module type OrderedType = sig
  type t
  val compare : t -> t -> int
end


module Make ( X : OrderedType ) = struct

type 'a t = 
  | Empty
  | Full of 'a
  | Node of (X.t * 'a t) list

let empty = Empty

let is_empty = function
  | Empty -> true
  | _ -> false

let rec add l v trie = match trie with
  | Empty -> List.fold_right (fun a t -> Node [a,t]) l (Full v)
  | Full _ -> trie
  | Node r -> match l with
      | [] -> Full v
      | a::c -> Node (add_to_list a c v r)
and add_to_list a c v l = match l with
  | [] -> [a, add c v Empty]
  | (a',t')::n ->
      let cmp = X.compare a a' in
      if cmp = 0 then (a, add c v t')::n
      else if cmp > 0 then (a',t')::(add_to_list a c v n)
      else (a, add c v Empty)::l

let rec add_force l v trie = match trie with
  | Empty -> List.fold_right (fun a t -> Node [a,t]) l (Full v)
  | Full _ -> trie
  | Node r -> match l with
      | [] -> Full v
      | a::c -> Node (add_force_to_list a c v r)
and add_force_to_list a c v l = match l with
  | [] -> [a, add c v Empty]
  | (a',t')::n ->
      let cmp = X.compare a a' in
      if cmp > 0 then (a',t')::(add_force_to_list a c v n)
      else (a, add_force c v Empty)::l

let rec mem c trie = match trie with 
  | Empty -> None
  | Full v -> Some v
  | Node l -> match c with
      | [] -> None
      | a::c -> 
          mem_list a c l
and mem_list a c l = match l with
  | [] -> None
  | (a',t')::n ->
      let cmp = X.compare a a' in
      if cmp = 0 then match mem c t' with
        | Some _ as r -> r
        | None -> match c with
            | [] -> None
            | a::c -> mem_list a c l
      else if cmp > 0 then mem_list a c n
      else match c with
          | [] -> None
          | a::c -> mem_list a c l
   
(* Apply f to all values mapped to in the trie. *)
let rec iter f trie = match trie with
  | Empty -> ()
  | Full v -> f v
  | Node l -> List.iter (fun (_,t) -> iter f t) l

let rec iter_nodes f trie = match trie with
  | Empty | Full _ -> ()
  | Node l -> List.iter (fun (n,t) -> f n; iter_nodes f t) l

(* Fold f to all values mapped to in the trie. *)
let rec fold f acc trie = match trie with
  | Empty -> acc
  | Full v -> f acc v
  | Node l -> List.fold_left (fun acc (_,t) -> fold f acc t) acc l

(* Apply f to all values whose keys (cubes) are subsumed by the given cube. *)
let rec iter_sub f c trie = match c, trie with
  | [], _ -> iter f trie
  | _, Empty 
  | _, Full _ -> () 
  | _, Node l -> iter_sub_list f c l
and iter_sub_list f c l = match l with
  | [] -> ()
  | (a',t')::n ->
      let a = List.hd c in
      let cmp = X.compare a a' in
      if cmp=0 then 
        iter_sub f (List.tl c) t'
      else if cmp>0 then begin
        iter_sub f c t';
        iter_sub_list f c n 
      end

(* Delete all values which satisfy the predicate p *)
let rec delete p trie = match trie with 
  | Empty -> Empty
  | Full v -> if p v then Empty else trie
  | Node l -> 
      let l' = delete_list p l in
      if l == l' then trie else Node l'
and delete_list p l = match l with
  | [] -> []
  | (a, t):: n ->
      let t' = delete p t in
      let n' = delete_list p n in
      if t'==t && n'==n then l else (a,t')::n'


(* List of all values mapped by the trie *)
let rec all_vals = function
  | Empty -> []
  | Full v -> [v]
  | Node l -> 
      List.flatten (List.fold_left (fun acc (_,t) -> (all_vals t)::acc) [] l)


let rec forall_exists p = function
  | Empty -> true
  | Full _ -> false
  | Node l -> List.for_all (fun (a,t) -> p a || forall_exists p t) l

end

