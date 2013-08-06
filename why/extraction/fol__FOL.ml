(* This file has been generated from Why3 theory FOL *)
open Ast
module S = Set__Fset

type t = 
  | Lit of Atom.t
  | Not of t
  | Or of t list
  | And of t list

exception Compare of int
let rec compare f1 f2 = match f1, f2 with
  | Lit a1, Lit a2 -> Atom.compare a1 a2
  | Lit _, _ -> -1
  | _, Lit _ -> 1
  | Not x1, Not x2 -> compare x1 x2
  | Not _, _ -> -1
  | _, Not _ -> 1
  | And l1, And l2 | Or l1, Or, l2 ->
    let r = Pervasives.compare (List.length l1) (List.length l2) in
    if r <> 0 then r
    else begin
      try 
	List.iter2 (fun x1 x2 ->
	  let r = compare x1 x2 in
	  if r <> 0 then raise Compare r
	) l1 l2;
	0	
      with Compare r -> r
    end
  | And _, _ -> -1
  | _, And -> 1


(* type structure to be defined (uninterpreted type) *)

(* let infix_breq (x: structure) (x1: t) : bool = *)
(*   failwith "to be implemented" (\* uninterpreted symbol *\) *)

let ffalse  : t = Lit False

let ttrue  : t = Lit True


(*---------- Helper functions ----------------*)
let conj_to_cube = function
  | And l -> 
    List.fold_left (fun acc x -> SAtom.add x acc) SAtom.empty l
  | _ -> assert false

let fol_to_cubes = function
  | Lit x -> [SAtom.singleton x]
  | And _ as f -> [conj_to_cube f]
  | Or l -> List.map conj_to_cube l
  | _ -> assert false

let cube_to_fol sa = 
  And (SAtom.fold (fun x acc -> Lit x :: acc) sa [])

let cubes_to_fol = function
  | [] -> []
  | [sa] -> cubes_to_fol sa
  | lsa -> Or (List.map cube_to_fol lsa)


let wrap_system sa =
  let sa, (args, _) = proper_cube sa in
  let arr_sa = ArrayAtom.of_satom sa in
  { global_system with 
    t_unsafe = args, sa;
    t_arru = arr_sa;
    t_alpha = ArrayAtom.alpha arr_sa args }
    

let fol_to_systems f = List.map wrap_system (fol_to_cubes f)

let rec push_neg p = function
  | Lit _ as x -> if p then x else Atom.neg x
  | Not f -> push_neg (not p) f
  | Or l ->
      if p then Or (List.map (push_neg p) l)
      else And (List.map (push_neg p) l)
  | And l ->
      if p then And (List.map (push_neg p) l)
      else Or (List.map (push_neg p) l)

let dnf f =
  let cons x xs = x :: xs in
  let rec fold g = function
    | And hs -> List.fold_left fold g hs
    | Or hs -> List.concat (List.map (fold g) hs)
    | h -> List.map (cons h) g in
  fold [[]] (push_neg true f)

let dnfize f =
  Or (List.map (fun conj -> And conj) (dnf f)
(*-----------------------------------------------*)

	
(* neg *)  
let prefix_tl (x: t) : t = dnfize (Not x)

let infix_et (x: t) (x1: t) : t = dnfize (And [x; x1])

let infix_plpl (x: t) (x1: t) : t = dnfize (Or [x; x1])

let infix_eqgt (x: t) (x1: t) : t = dnfize (Or [Not x; x1])
  
let infix_breqeq (x: t) (x1: t) : bool =
  let ls = fol_to_systems x in
  match ls with
  | [s] -> fixpoint ~invariants:[] ~visited:(fol_to_systems x1) s <> None
  | _ -> assert false


(* Notataions *)

let neg = prefix_tl

let (&) x x1 = infix_et x x1

let (++) x x1 = infix_plpl x x1

let (=>) x x1 = infix_eqgt x x1
  
let (|=) x x1 = infix_breqeq x x1



(* let cnf_split_quantified f = *)
(*   match push_neg false f with *)
(*   | Lit _ as nf -> *)
  
let sat (f: t) : bool = not ((Lit True) |= push_neg false f)
  


let valid (f: t) : bool = not (sat (prefix_tl f))
