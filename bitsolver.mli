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

type env

exception Unsat

val init_env : Ast.t_system -> unit
(** returns an environnement with the bitvector size needed for the
    representation of cubes of system [s] and the associated bounds
    (see {!bitvbounds_from_pb}).*)

val cube_to_bitvs : Ast.SAtom.t -> Bitv.t list
(** [cube_to_bitvs env c] returns the bit-vector representation of the
    cube [c].*)


val apply_subst : (Hstring.t * Hstring.t) list -> Bitv.t -> Bitv.t
(** applies a process substitution on a bit-vector representation of a cube.*)


val solve : Bitv.t list -> Bitv.t list -> unit
(** {b Raises} {! Unsat } *)


val fixpoint : Ast.t_system -> Ast.t_system list -> bool

val safe : Ast.t_system -> bool

val check_safety : Ast.t_system ->  unit















