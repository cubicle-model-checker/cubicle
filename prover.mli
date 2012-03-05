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

open Ast

(* Checks if the system is unsafe *)
val unsafe : t_system -> unit
val assume_goal : t_system -> unit
val assume_node : ArrayAtom.t -> unit
val check_guard : 
  Hstring.t list -> SAtom.t -> SAtom.t -> SAtom.t list list -> unit

