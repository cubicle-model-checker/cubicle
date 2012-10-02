(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                  Universite Paris-Sud 11                               *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

open Options
open Ast

module HS = Hstring.H
module HSet = Hstring.HSet
module HA = Hashtbl.Make (Atom)
module HT = Hashtbl.Make (struct
  type t = term
  let equal x y = compare_term x y = 0
  let hash = hash_term
end)


type env = {
  size : int;
  term_bounds : (int * int) HT.t;
  bounds : int list;
  proc_bits : (int list) HS.t;
  proc_section : (int * int) HS.t;
}

(* let bits_procs = *)
(*   let rec aux n = *)
(*     if max_procs lsr n = 0 then n *)
(*     else aux (n + 1) *)
(*   in aux 0 *)


(** number of bits required to represtent a value of type [ty]*)
let size_of_type ty =
  try
    if Hstring.equal ty Smt.Type.type_proc then max_proc
    else List.length (Smt.Type.constructors ty)
  with Not_found -> assert false

(** number of bits required to represtent a value associated to symbol [x]*)
let size_of_symbol x = size_of_type (snd (Smt.Symbol.type_of x))

(** number of bits required to represtent cubes of system [s]*)  
let bitvsize_from_pb s =
  let size_globals = 
    List.fold_left (fun n g -> size_of_symbol g + n) 0 s.t_globals in
  let size_arrays =
    List.fold_left (fun n a -> size_of_symbol a + n) 0 s.t_arrays in
  size_globals + max_proc * size_arrays


let add_proc_bits offset pbts =
  let i = ref 0 in
  List.iter (fun p -> 
    let l = try HS.find pbts p with Not_found -> [] in
    HS.add pbts p ((!i + offset)::l);
    incr i
  ) proc_vars

(** returns a hash table mapping terms [x] to bounds [(right, left)] delimiting
    the bits representing the value of [x].*)  
let bitvbounds_from_pb s =
  let nb_vars = List.length s.t_globals + max_proc * (List.length s.t_arrays) in
  let h = HT.create nb_vars in
  let i = ref 0 in
  let bounds = ref [] in
  let proc_bits = HS.create max_proc in
  let proc_section = HS.create max_proc in
  List.iter (fun g ->
    let right = !i in
    let left = right + size_of_symbol g - 1 in
    HT.add h (Elem (g, Glob)) (right, left);
    bounds := right :: !bounds;
    if Smt.Symbol.has_type_proc g then add_proc_bits right proc_bits;
    i := left + 1
  ) s.t_globals;
  List.iter (fun p ->
    let right_sec_p = !i in
    List.iter (fun a ->
      let right = !i in
      let left = right + size_of_symbol a - 1 in
      HT.add h (Access (a, p, Var)) (right, left);
      bounds := right :: !bounds;
      if Smt.Symbol.has_type_proc a then add_proc_bits right proc_bits;
      i := left + 1
    ) s.t_arrays;
    let left_sec_p = !i - 1 in
    HS.add proc_section p (right_sec_p, left_sec_p);
  ) proc_vars;
  h, List.rev !bounds, proc_bits, proc_section

(** returns an environnement with the bitvector size needed for the
    representation of cubes of system [s] and the associated bounds
    (see {!bitvbounds_from_pb}).*)
let create_env s = 
  let term_bounds, bounds, proc_bits, proc_section = bitvbounds_from_pb s in
  {
    size = bitvsize_from_pb s;
    term_bounds = term_bounds;
    bounds = bounds;
    proc_bits = proc_bits;
    proc_section = proc_section;
  }

let values_of_type ty =
  let vals =
    if Hstring.equal ty Smt.Type.type_proc then proc_vars
    else Smt.Type.constructors ty in
  List.fold_left (fun acc v -> HSet.add v acc) HSet.empty vals      

let values_of_term = function
  | Elem (x, Glob) | Access (x, _, Var) ->
      values_of_type (snd (Smt.Symbol.type_of x))
  | Elem (x, (Var | Constr)) -> HSet.singleton x
  | _ -> assert false

let index_value x v =
  let cpt = ref 0 in
  let i = ref (-1) in
  HSet.iter (fun vx ->
    if Hstring.equal v vx then i := !cpt;
    incr cpt) (values_of_term x);
  if !i = -1 then raise Not_found;
  !i

let create_mask_value_aux env x op v right left =
  let i = index_value x v in
  let b = Bitv.create env.size true in
  begin match op with
    | Eq -> 
        Bitv.fill b right (left - right) false;
        Bitv.set b (i + right) true
    | Neq ->
        Bitv.set b (i + right) false
    | _ -> assert false
  end;
  b

let create_mask_value env x op v =
  let r,l = HT.find env.term_bounds x in
  create_mask_value_aux env x op v r l

let create_mask_comp env x op y =
  let rx,lx = HT.find env.term_bounds x in
  let ry,ly = HT.find env.term_bounds y in
  let values_x = values_of_term x in
  let values_y = values_of_term y in
  match op with
    | Eq -> 
        HSet.fold (fun vy acc ->
          HSet.fold (fun vx acc -> 
            if Hstring.equal vx vy then
              let bx = create_mask_value_aux env x Eq vx rx lx in
              let by = create_mask_value_aux env y Eq vy ry ly in
              Bitv.bw_and bx by :: acc
            else acc
          ) values_x acc
        ) values_y []
    | Neq ->
        HSet.fold (fun vy acc ->
          if HSet.mem vy values_x then
            let by = create_mask_value_aux env y Eq vy ry ly in
            let bx = create_mask_value_aux env x Neq vy rx lx in
            Bitv.bw_and bx by :: acc
          else acc
        ) values_y []
    | _ -> assert false  


let atom_masks env = function
  | Atom.True -> [Bitv.create env.size true]
  | Atom.False -> [Bitv.create env.size false]
  | Atom.Comp (x, op, Elem (v, (Constr | Var)))
  | Atom.Comp (Elem (v, (Constr | Var)), op, x) ->
      [create_mask_value env x op v]
  | Atom.Comp (x, op, y) ->
      create_mask_comp env x op y
  | _ -> assert false


let add_atom_to_bitv env a bvs =
  List.flatten (List.map (fun m -> 
    List.map (Bitv.bw_and m) bvs) (atom_masks env a))

let cube_to_bitvs env sa =
  SAtom.fold (add_atom_to_bitv env) sa (atom_masks env Atom.True)
        
      


let apply_subst env sigma b =
  let nbv = Bitv.copy b in
  List.iter (fun (x,y) ->
    let bits_x = HS.find env.proc_bits x in
    let bits_y = HS.find env.proc_bits y in
    List.iter2 (fun i j -> Bitv.set nbv i (Bitv.get b j)) bits_x bits_y;
    let right_sec_x, _ = HS.find env.proc_section x in
    let right_sec_y, left_sec_y = HS.find env.proc_section y in
    Bitv.blit b right_sec_y nbv right_sec_x (left_sec_y - right_sec_y)
  ) sigma;
  nbv


exception Not_unit

let next_bound env i =
  let rec next_bound env i = function
    | [] -> env.size - 1
    | bn :: r -> if i < bn then bn - 1 else next_bound env i r
  in
  next_bound env i env.bounds

let is_unit env b =
  try
    let first = ref (-1) in
    let last = ref (-1) in
    Bitv.iteri_true (fun i ->
      if !first <> -1 then (last := next_bound env i; first := i)
      else if i > !last then raise Not_unit
    ) b;
    let u = Bitv.create env.size false in
    Bitv.fill u !first (!last - !first + 1) false;
    Bitv.bw_or_in_place b u;
    true
  with Not_unit -> false

let is_bottom = Bitv.all_zeros

exception Unsat

let rec propagate env conj neg_visited =
  let todo, remaining =
    List.fold_left (fun (todo, remaining) b ->
      Bitv.bw_and_in_place b conj;
      if is_bottom b then raise Unsat;
      if is_unit env b then b :: todo, remaining
      else todo, b :: remaining
    ) ([],[]) neg_visited in
  match todo with
    | conj :: todo -> propagate env conj (todo @ remaining)
    | [] -> ()
