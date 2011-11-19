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

(* open Solver_types  *)
(* open Format *)

(* type exp = Atom Solver_types.atom | Fresh of int *)
(* type t = Empty | Leaf of exp | Node of t * t  *)

(* let singleton e = Leaf (Atom e) *)
(* let empty = Empty *)
(* let union s1 s2 = Node (s1,s2) *)


(* let rec iter f s = match s with *)
(*   | Empty -> () *)
(*   | Leaf e -> f e *)
(*   | Node(s1,s2) -> iter f s1; iter f s2 *)
      
(* let print fmt s = *)
(*   if Options.verbose then begin *)
(*     fprintf fmt "EXP:["; *)
(*     iter (fprintf fmt "(%a)" Debug1.atom) s; *)
(*     fprintf fmt "]" *)
(*   end *)

open Solver_types 
open Format

type exp = Atom of Solver_types.atom | Fresh of int

module S = 
  Set.Make
    (struct 
       type t = exp
       let compare a b = match a,b with
	 | Atom _, Fresh _ -> -1
	 | Fresh _, Atom _ -> 1
	 | Fresh i1, Fresh i2 -> i1 - i2
	 | Atom a, Atom b -> a.aid - b.aid
     end)
  
type t = S.t

let singleton e = S.singleton (Atom e)
    
let empty = S.empty

let union s1 s2 = S.union s1 s2

let iter_atoms f s = 
  S.iter (fun e -> match e with
    | Fresh _ -> ()
    | Atom a -> f a) s
  
let print fmt s =
  if Options.verbose then begin
  fprintf fmt "EXP:[";
  S.iter (fun a -> match a with
    | Atom a -> fprintf fmt "(%a)" Debug1.atom a
    | Fresh i -> fprintf fmt "(fresh %d)" i
  ) s;
  fprintf fmt "]"
  end
    
let merge e1 e2 = e1


let fresh_exp =
  let r = ref (-1) in
  fun () -> incr r; !r

let remove_fresh i s =
  let fi = Fresh i in
  if S.mem fi s then Some (S.remove fi s)
  else None

let add_fresh i = S.add (Fresh i)

let print_proof = print
