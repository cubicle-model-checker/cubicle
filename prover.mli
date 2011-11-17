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


module TimeAE : Timer.S

val nb_calls : unit -> int

val empty : Hstring.t list -> unit

(* Checks if the system is unsafe *)
val unsafe : t_system -> unit

val add_goal : t_system -> unit
val add_node : ('a * 'b * AltErgo.Term.t) Hstring.H.t -> Ast.ArrayAtom.t -> unit

val check_fixpoint : t_system -> Ast.ArrayAtom.t list -> bool
