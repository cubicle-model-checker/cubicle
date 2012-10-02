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

val create_env : Ast.t_system -> env
(** returns an environnement with the bitvector size needed for the
    representation of cubes of system [s] and the associated bounds
    (see {!bitvbounds_from_pb}).*)

val cube_to_bitvs : env -> Ast.SAtom.t -> Bitv.t list
(** [cube_to_bitvs env c] returns the bit-vector representation of the
    cube [c].*)


val apply_subst : env -> (Hstring.t * Hstring.t) list -> Bitv.t -> Bitv.t
(** applies a process substitution on a bit-vector representation of a cube.*)



















