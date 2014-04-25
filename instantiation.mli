(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2014                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

(** Exhaustive Instantiation features *)

(** Because the SMT solver only takes as input ground formulas, we need to do
    the instantiation of quantifiers inside the model checker. The simplest
    (and complete) way to do this is to saturate exhaustively with the process
    varialbles (skolems). *)

val relevant : of_cube:Cube.t -> to_cube:Cube.t -> Variable.subst list
(** [relevant ~of_cube:a ~to_cube:b ] returns the list of relevant
    instantiations of the quantifiers of [b] for the test
    [exists i1,... b => exists z1,... a]. Eliminates trivial useless
    (because they make the goal inconsistent) instantiations with simple
    checks.

    Quadratic in the size of the largest contiguous subset of [a] and [b]
    of atoms with terms of the same type.
 *)

val exhaustive : of_cube:Cube.t -> to_cube:Cube.t -> Variable.subst list
(** Same as {! relevant} but does not performs any checks *)
