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

open Format
open Ast

val print_term : formatter -> term -> unit

val print_atom : formatter -> Atom.t -> unit

val print_cube : formatter -> SAtom.t -> unit

val print_system : formatter -> t_system -> unit

val print_unsafe : formatter -> t_system -> unit

val print_node : formatter -> t_system -> unit
