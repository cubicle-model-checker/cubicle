(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*  Amit Goel                                                             *)
(*  Copyright (c) 2012, Intel Corporation.                                *)
(*                                                                        *)
(* This Trie-based Reachability extension to Cubicle ("Software") is      *)
(* furnished under Intel BSD License Agreement and may only be used       *)
(* or copied in accordance with the terms of that agreement. No           *)
(* license, express or implied, by estoppel or otherwise, to any          *)
(* intellectual property rights is granted by this document. The          *)
(* Software is subject to change without notice, and should not be        *)
(* construed as a commitment by Intel Corporation to market, license,     *)
(* sell or support any product or technology. Unless otherwise provided   *)
(* for in the license under which this Software is provided, the          *)
(* Software is provided AS IS, with no warranties of any kind, express    *)
(* or implied. Except as expressly permitted by the Software license,     *)
(* neither Intel Corporation nor its suppliers assumes any                *)
(* responsibility or liability for any errors or inaccuracies that may    *)
(* appear herein. Except as expressly permitted by the Software           *)
(* license, no part of the Software may be reproduced, stored in a        *)
(* retrieval system, transmitted in any form, or distributed by any       *)
(* means without the express written consent of Intel Corporation.        *)
(*                                                                        *)
(**************************************************************************)

open Ast

module H = Hstring

(* Trie, mapping cubes to value of type 'a *)
type 'a t = 
  | Empty
  | Full of 'a
  | Node of (Atom.t * 'a t) list

let empty = Empty

(* Add a mapping cube->v to trie *)
let rec add cube v trie = match trie with
  | Empty -> List.fold_right (fun a t -> Node [a,t]) cube (Full v)
  | Full _ -> trie
  | Node l -> match cube with
      | [] -> Full v
      | atom::cube -> Node (add_to_list atom cube v l)
and add_to_list atom cube v l = match l with
  | [] -> [atom, add cube v Empty]
  | (atom',t')::n ->
      let cmp = Atom.compare atom atom' in
      if cmp = 0 then (atom, add cube v t')::n
      else if cmp > 0 then (atom',t')::(add_to_list atom cube v n)
      else (atom, add cube v Empty)::l

(* Is cube subsumed by some cube in the trie? *)
let rec mem cube trie = match trie with 
  | Empty -> None
  | Full {t_nb = id} -> Some [id]
  | Node l -> match cube with
      | [] -> None
      | atom::cube -> 
          mem_list atom cube l
and mem_list atom cube l = match l with
  | [] -> None
  | (atom',t')::n ->
      let cmp = Atom.compare atom atom' in
      if cmp = 0 then mem cube t'
      else if cmp > 0 then mem_list atom cube n
      else match cube with
          | [] -> None
          | atom::cube -> mem_list atom cube l

(* Apply f to all values mapped to in the trie. *)
let rec iter f trie = match trie with
  | Empty -> ()
  | Full v -> f v
  | Node l -> List.iter (fun (_,t) -> iter f t) l

(* Apply f to all values whose keys (cubes) are subsumed by the given cube. *)
let rec iter_subsumed f cube trie = match cube, trie with
  | [], _ -> iter f trie
  | _, Empty 
  | _, Full _ -> () 
  | _, Node l -> iter_subsumed_list f cube l
and iter_subsumed_list f cube l = match l with
  | [] -> ()
  | (atom',t')::n ->
      let atom = List.hd cube in
      let cmp = Atom.compare atom atom' in
      if cmp=0 then 
        iter_subsumed f (List.tl cube) t'
      else if cmp>0 then begin
        iter_subsumed f cube t';
        iter_subsumed_list f cube n 
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
  | (atom, t):: n ->
      let t' = delete p t in
      let n' = delete_list p n in
      if t'==t && n'==n then l else (atom,t')::n'

(* List of all values mapped by the trie *)
let rec all_vals = function
  | Empty -> []
  | Full v -> [v]
  | Node l -> 
      List.flatten (List.fold_left (fun acc (_,t) -> (all_vals t)::acc) [] l)

(* All values whose keys (cubes) are not inconsistent with the given cube. *)
let rec consistent cube trie = match cube, trie with
  | [], _ -> all_vals trie
  | _, Empty -> []
  | _, Full v -> [v]
  | (atom::cube), Node l -> List.flatten (List.map (consistent_list atom cube) l)
and consistent_list atom cube ((atom', t') as n) = match (atom, atom') with
  | Atom.Comp (Elem (v1, Glob), Eq, Elem (x1, Constr)),
    Atom.Comp (Elem (v2, Glob), Eq, Elem (x2, Constr))
  | Atom.Comp (Elem (v1, Glob), Eq, Elem (x1, Var)),
    Atom.Comp (Elem (v2, Glob), Eq, Elem (x2, Var)) 
      when H.equal v1 v2 && not (H.equal x1 x2) ->
      []
  | Atom.Comp (Elem (v1, Glob), Eq, Elem (x1, Constr)),
    Atom.Comp (Elem (v2, Glob), (Neq|Lt), Elem (x2, Constr))
      when H.equal v1 v2 && H.equal x1 x2 ->
      []
  | Atom.Comp (Access (a1,i1,Var), Eq, (Elem (_,(Constr|Glob)) | Arith _ as x1)),
    Atom.Comp (Access (a2,i2,Var), Eq, (Elem (_,(Constr|Glob)) | Arith _ as x2))
      when H.equal a1 a2 && H.equal i1 i2 && compare_term x1 x2 <> 0 ->
      []
  | Atom.Comp (Access (a1,i1,Var), Eq,
               (Elem (_, (Constr|Glob)) | Arith _ as x1)),
    Atom.Comp (Access (a2,i2,Var), (Neq | Lt), 
               (Elem (_, (Constr|Glob)) | Arith _ as x2))
      when H.equal a1 a2 && H.equal i1 i2 && compare_term x1 x2 = 0 ->
      []
  | _, _ ->
      let cmp = Atom.compare atom atom' in
      if cmp = 0 then consistent cube t'
      else if cmp < 0 then match cube with
        | [] -> all_vals t'
        | atom::cube -> consistent_list atom cube n
      else consistent (atom::cube) t'

