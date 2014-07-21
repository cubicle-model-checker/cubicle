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

(** Backward reachability with Approximations and Backtracking *)

val brab : Ast.t_system -> Bwd.result
(** Backtracking procedure that uses approximated backward reachability
    ({! Bwd}).

    [brab system] calls BRAB on the given system. *)
