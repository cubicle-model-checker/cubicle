(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon, Universite Paris-Sud 11              *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

open Ast

(* Checks if the system is unsafe *)
val unsafe : t_system -> AltErgo.Formula.t

(* 
   fixpoint env [#1;...;#n] np p check for the formula
   distinct(#1,...,#n) and np => p 
*)
val fixpoint : 
  t_system -> string list -> SAtom.t -> SAtom.t -> AltErgo.Formula.t


val extended_fixpoint : 
  t_system ->
  string list -> (string * string) list -> 
  SAtom.t -> SAtom.t -> AltErgo.Formula.t

val simpl_check :
  (string, (sort * AltErgo.Ty.t * AltErgo.Term.t)) Hashtbl.t ->
  string list -> Ast.SAtom.t -> Ast.SAtom.t -> bool
