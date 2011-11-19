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

type t = unit

type gformula = { 
  f:Formula.t; 
  age: int; 
  name: Formula.t option; 
  mf: bool;
  gf: bool;
}

exception Sat of t
exception Unsat of Explanation.t
exception I_dont_know

(* the empty sat-solver context *)
val empty : t

(* [assume env f] assume a new formula [f] in [env]. Raises Unsat if
   [f] is unsatisfiable in [env] *)
val assume : gformula -> unit

(* [pred_def env f] assume a new predicate definition [f] in [env]. *)
val pred_def : t -> Formula.t -> t

(* [unsat env f size] checks the unsatisfiability of [f] in
   [env]. Raises I_dont_know when the proof tree's height reaches
   [size]. Raises Sat if [f] is satisfiable in [env] *)
val unsat : t -> gformula -> Explanation.t

val check : unit -> unit

val start : unit -> unit
val stop : unit -> int64
val clear : unit -> unit
