(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2013                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

open Options
open Ast
open Format

module HS = Hstring.H
module HSet = Hstring.HSet
module HA = Hashtbl.Make (Atom)
module HT = Hashtbl.Make (struct
  type t = term
  let equal x y = compare_term x y = 0
  let hash = hash_term
end)


type env = {
  mutable size : int;
  mutable term_bounds : (int * int) HT.t;
  mutable bounds : int list;
  mutable proc_bits : (int list) HS.t;
  mutable proc_section : (int * int) HS.t;
}

let env = 
  let proc_bits = HS.create max_proc in
  List.iter (fun p ->
    HS.add proc_bits p [];
  ) proc_vars;
  {
    size = 0;
    term_bounds = HT.create 0;
    bounds = [];
    proc_bits = proc_bits;
    proc_section = HS.create max_proc;
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
let bitvsize_from_pb s nb_procs =
  let size_globals = 
    List.fold_left (fun n g -> size_of_symbol g + n) 0 s.t_globals in
  let size_arrays =
    List.fold_left (fun n a -> size_of_symbol a + n) 0 s.t_arrays in
  size_globals + nb_procs * size_arrays


let add_proc_bits offset =
  let i = ref 0 in
  List.iter (fun p -> 
    let l = HS.find env.proc_bits p in
    HS.add env.proc_bits p ((!i + offset)::l);
    incr i
  ) proc_vars

(** returns a hash table mapping terms [x] to bounds [(right, left)] delimiting
    the bits representing the value of [x].*)  
let bitvbounds_from_pb s =
  let nb_vars = List.length s.t_globals + max_proc * (List.length s.t_arrays) in
  let h = HT.create nb_vars in
  let i = ref 0 in
  let bounds = ref [] in
  List.iter (fun g ->
    let right = !i in
    let left = right + size_of_symbol g - 1 in
    HT.add h (Elem (g, Glob)) (right, left);
    bounds := right :: !bounds;
    if Smt.Symbol.has_type_proc g then add_proc_bits right;
    i := left + 1
  ) s.t_globals;
  List.iter (fun p ->
    let right_sec_p = !i in
    List.iter (fun a ->
      let right = !i in
      let left = right + size_of_symbol a - 1 in
      HT.add h (Access (a, [p])) (right, left);
      bounds := right :: !bounds;
      if Smt.Symbol.has_type_proc a then add_proc_bits right;
      i := left + 1
    ) s.t_arrays;
    let left_sec_p = !i - 1 in
    HS.add env.proc_section p (right_sec_p, left_sec_p);
  ) proc_vars;
  h, List.rev (!bounds)


let init_env s nb_procs = 
  let term_bounds, bounds = bitvbounds_from_pb s in
  if debug then begin
    HT.iter (fun t (r,l) ->
      eprintf "%a \t: %d  to %d@." Pretty.print_term t r l
    ) term_bounds ;
    eprintf "bounds : [";
    List.iter (fun bn ->
      eprintf "%d," bn
    ) bounds;
    eprintf "]@.";
  end;
  env.size <- bitvsize_from_pb s nb_procs;
  env.term_bounds <- term_bounds;
  env.bounds <- bounds

let values_of_type ty =
  let vals =
    if Hstring.equal ty Smt.Type.type_proc then proc_vars
    else Smt.Type.constructors ty in
  List.fold_left (fun acc v -> HSet.add v acc) HSet.empty vals      

let values_of_term = function
  | Elem (x, Glob) | Access (x, _) ->
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

let not_index_values x v =
  let cpt = ref 0 in
  HSet.fold (fun vx acc ->
    let acc = if not (Hstring.equal v vx) then !cpt :: acc else acc in
    incr cpt;
    acc
  ) (values_of_term x) []  


let create_masks_value_aux ~dnf x op v right left =
  try
    match op with
      | Eq ->
          let b = Bitv.create env.size true in
          Bitv.fill b right (left - right + 1) false;
          let i = index_value x v in
          Bitv.set b (i + right) true;
          [b]
      | Neq ->
          if not dnf then 
            let b = Bitv.create env.size true in
            let i = index_value x v in
            Bitv.set b (i + right) false;
            [b]
          else
            let b = Bitv.create env.size true in
            Bitv.fill b right (left - right + 1) false;
            List.fold_left (fun acc i ->
              let b = Bitv.copy b in
              Bitv.set b (i + right) true;
              b :: acc) [] (not_index_values x v)
      | _ -> assert false
  with Not_found -> [Bitv.create env.size false]

let create_masks_value ~dnf x op v =
  let r,l = HT.find env.term_bounds x in
  create_masks_value_aux ~dnf x op v r l

let create_masks_comp ~dnf x op y =
  let rx,lx = HT.find env.term_bounds x in
  let ry,ly = HT.find env.term_bounds y in
  let values_x = values_of_term x in
  let values_y = values_of_term y in
  match op with
    | Eq -> 
        HSet.fold (fun vy acc ->
          HSet.fold (fun vx acc -> 
            if Hstring.equal vx vy then
              let bxs = create_masks_value_aux ~dnf x Eq vx rx lx in
              let bys = create_masks_value_aux ~dnf y Eq vy ry ly in
              List.fold_left (fun acc bx ->
                List.fold_left (fun acc by ->
                  Bitv.bw_and bx by :: acc
                ) acc bys
              ) acc bxs
            else acc
          ) values_x acc
        ) values_y []
    | Neq ->
        HSet.fold (fun vy acc ->
          if HSet.mem vy values_x then
            let bys = create_masks_value_aux ~dnf y Eq vy ry ly in
            let bxs = create_masks_value_aux ~dnf x Neq vy rx lx in
              List.fold_left (fun acc bx ->
                List.fold_left (fun acc by ->
                  Bitv.bw_and bx by :: acc
                ) acc bys
              ) acc bxs
          else acc
        ) values_y []
    | _ -> assert false  


let atom_masks ~dnf = function
  | Atom.True -> [Bitv.create env.size true]
  | Atom.False -> [Bitv.create env.size false]
  | Atom.Comp (x, op, Elem (v, (Constr | Var)))
  | Atom.Comp (Elem (v, (Constr | Var)), op, x) ->
      create_masks_value ~dnf x op v
  | Atom.Comp (x, op, y) ->
      create_masks_comp ~dnf x op y
  | _ -> assert false


let add_atom_to_bitv ~dnf a bvs =
  List.flatten (List.map (fun m -> 
    List.map (Bitv.bw_and m) bvs) (atom_masks ~dnf a))

let cube_to_bitvs ~dnf sa =
  SAtom.fold (add_atom_to_bitv ~dnf) sa (atom_masks ~dnf Atom.True)


let in_bounds i =
  let rec next_bound i right = function
    | [] -> right, env.size - 1
    | bn :: r -> if i < bn then right, bn - 1 else next_bound i bn r
  in
  next_bound i 0 env.bounds


exception Found of term
let term_in_bounds bn =
  try
    HT.iter (fun t bn' -> if bn = bn' then raise (Found t)) env.term_bounds;
    raise Not_found
  with Found t -> t

let value_of_index i vals =
  let cpt = ref 0 in
  let v = ref (Hstring.empty) in
  HSet.iter (fun v' -> if !cpt = i then v := v'; incr cpt) vals;
  !v

let print_bitv_to_cube b =
  let values = HT.create 17 in
  HT.iter (fun t _ -> HT.add values t HSet.empty) env.term_bounds;
  Bitv.iteri_true (fun i ->
    let r,l = in_bounds i in
    let t = term_in_bounds (r,l) in
    let id = i - r in
    let v = value_of_index id (values_of_term t) in
    let vals = HT.find values t in
    HT.replace values t (HSet.add v vals) 
  ) b;
  eprintf "-----------------------@.";
  HT.iter (fun x vals ->
    (* if not (vals = values_of_term x) then begin *)
    if not (HSet.is_empty vals) then begin
      eprintf "%a = " Pretty.print_term x;
      eprintf "{";
      HSet.iter (fun v -> eprintf " %a |" Hstring.print v) vals;
      eprintf "}@.";
    end
  ) values



let cube_to_bitvs2 ~dnf sa =
  let bs = cube_to_bitvs ~dnf sa in
  eprintf "CUBE : %a\n--->\nBITV : " Pretty.print_cube sa;
  List.iter (fun b ->
    eprintf "---------------\n";
    print_bitv_to_cube b) bs;
  eprintf "@.";
  bs



let apply_subst sigma b =
  let nbv = Bitv.copy b in
  List.iter (fun (x,y) ->
    let bits_x = HS.find env.proc_bits x in
    let bits_y = HS.find env.proc_bits y in
    List.iter2 (fun i j -> 
      Bitv.set nbv j (Bitv.get b i);
      Bitv.set nbv i (Bitv.get b j);
      (* Bitv.set nbv j true; *)
    ) bits_x bits_y;
    let right_sec_x, left_sec_x = HS.find env.proc_section x in
    let right_sec_y, left_sec_y = HS.find env.proc_section y in
    Bitv.blit b right_sec_x nbv right_sec_y (left_sec_x - right_sec_x + 1);
    Bitv.blit b right_sec_y nbv right_sec_x (left_sec_y - right_sec_y + 1);
    (* Bitv.fill nbv right_sec_x (left_sec_x - right_sec_x + 1) true; *)
  ) sigma;
  nbv

let is_unit b =
  try
    let first = ref true in
    let bnds = ref (-1, -1) in
    Bitv.iteri_true (fun i ->
      if !first then (bnds := in_bounds i; first := false)
      else if i > snd !bnds then raise Exit
    ) b;
    (* eprintf "IS_UNIT : "; *)
    (* print_bitv_to_cube b; *)
    (* eprintf "@."; *)
    Some !bnds
  with Exit -> 
    (* eprintf "NOT_UNIT : "; *)
    (* print_bitv_to_cube b; *)
    (* eprintf "@."; *)
    None

let to_unit b (right,left) =
  let u = Bitv.create env.size true in
  Bitv.fill u right (left - right + 1) false;
  Bitv.bw_or_in_place b u


(* inefficient and useless *)
let is_top b =
  try
    HT.iter (fun _ (r, l) ->
      let u = Bitv.create env.size true in
      Bitv.fill u r (l - r + 1) false;
      Bitv.bw_or_in_place u b;
      if Bitv.all_ones u then raise Exit
    ) env.term_bounds;
    false
  with Exit -> true
    
  

let is_bottom = Bitv.all_zeros

exception Unsat

let rec propagate conj neg_visited =
  if is_bottom conj then raise Unsat;
  let unit, remaining =
    List.fold_left (fun (unit, remaining) b ->
      Bitv.bw_and_in_place b conj;
      if is_bottom b then raise Unsat;
      if unit = None then
        match is_unit b with
          | Some bnds -> to_unit b bnds; Some b, remaining
          | _ -> unit, b :: remaining
      else unit, b :: remaining
    ) (None, []) neg_visited in
  match unit with
    | Some conj -> propagate conj remaining
    | None -> ()

let copy_visited = List.map Bitv.copy

let is_unsat cubes neg_visited =
  List.for_all (fun conj ->
    let neg_visited = copy_visited neg_visited in
    try propagate conj neg_visited; false with Unsat -> true)
    cubes


let fixpoint ~invariants ~visited ({t_unsafe = args, sa} as s) =
  if (delete && (s.t_deleted || Cube.has_deleted_ancestor s)) then Some []
  else
    let visited = (List.rev_append invariants visited) in
    let cubes = cube_to_bitvs ~dnf:true sa in
    if debug then eprintf "fixpoint:\ncube: %a@." Pretty.print_cube sa;
    if debug then 
      List.iter (fun c -> eprintf "Bitv : %s@." (Bitv.L.to_string c)) cubes;
    (* let neg_visited = *)
    (*   List.fold_left (fun acc {t_unsafe = vargs, sa} -> *)
    (*     if debug then eprintf "visited: %a@." Pretty.print_cube sa; *)
    (*     let bvs = cube_to_bitvs ~dnf:false sa in *)
    (*     let perms = Cube.all_permutations vargs args in *)

    (*     List.fold_left (fun acc bv -> *)
    (*       List.fold_left (fun acc sigma -> *)
    (*         let bv = apply_subst sigma bv in *)
    (*         Bitv.bw_not_in_place bv; *)
    (*         bv :: acc) acc perms *)
    (*     ) acc bvs *)

    (*   ) [] visited *)
    (* in *)
    let neg_visited =
      List.fold_left (fun acc {t_alpha = vargs, sa; t_nb = nb} ->
        let sa = ArrayAtom.to_satom sa in
        if debug then eprintf "%d visited: %a@." nb Pretty.print_cube sa;
        let perms = all_permutations vargs args in

        List.fold_left (fun acc sigma ->
          
          let sa = Cube.apply_subst sa sigma in
          let bvs = cube_to_bitvs ~dnf:false sa in
          List.iter Bitv.bw_not_in_place bvs;
          bvs @ acc) acc perms

      ) [] visited
    in
    if is_unsat cubes neg_visited then begin
      (* if debug then eprintf "FIXPONT!@."; *)
      (* if Cube.fixpoint ~invariants ~visited s = None then *)
      (*   (eprintf "PROBLEM (correction) !!!!!!@."; exit 1); *)
      Some []
    end else begin
      if debug then eprintf "NOT fixpoint@.";
      (* (match Cube.fixpoint ~invariants ~visited s with  *)
      (*   | Some uc -> *)
      (*       eprintf "UC:@."; *)
      (*       List.iter (fun i -> eprintf "%d@." i) uc; *)
      (*       (eprintf "PROBLEM (completude) !!!!!!@."; exit 1); *)
      (*   | _ -> ()); *)
      None
    end



(* Buggy : need to check if at least one term is 0 *)
let safe {t_unsafe = args, sa; t_init = iargs, inisa} = assert false
  (* let cubes = cube_to_bitvs ~dnf:false sa in *)
  (* eprintf "safety : \ncube: %a@." Pretty.print_cube sa; *)
  (* List.iter (fun c -> eprintf "Bitv : %s@." (Bitv.L.to_string c)) cubes; *)
  (* let init_sa = match iargs with *)
  (*   | [] -> inisa *)
  (*   | _ -> *)
  (*     List.fold_left (fun acc ss -> *)
  (*       SAtom.union (Cube.apply_subst inisa ss) acc) *)
  (*       SAtom.empty *)
  (*       (all_instantiations iargs args) *)
  (* in *)
  (* let init_cubes = cube_to_bitvs ~dnf:false init_sa in *)
  (* eprintf "\ninit: %a@." Pretty.print_cube init_sa; *)
  (* List.iter (fun c -> eprintf "Bitv : %s@." (Bitv.L.to_string c)) init_cubes; *)
  (* List.for_all (fun c -> *)
  (*   List.for_all (fun init -> *)
  (*     Bitv.all_zeros (Bitv.bw_and c init) *)
  (*   ) init_cubes *)
  (* ) cubes *)

let check_safety s =
  if not (safe s) then raise (Search.Unsafe s)


