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

open Ast

module TimeF : Timer.S

module SMT : Smt.Solver
module ESMT : Smt.EnumSolver

(* Checks if the system is unsafe *)
val unsafe : t_system -> unit

val reached : Hstring.t list -> SAtom.t -> SAtom.t -> unit

(* Clears the context and assumes a goal formula *)
val assume_goal : t_system -> unit

(* Assumes the negation of a node; raises Unsat if the context becomes
   unsatisfiable *)
val assume_node : ArrayAtom.t -> id:int -> unit

val check_guard : Hstring.t list -> SAtom.t -> SAtom.t -> unit

(*val extract_candidates : 
  Hstring.t list -> ArrayAtom.t -> ArrayAtom.t list list -> SAtom.t list*)
