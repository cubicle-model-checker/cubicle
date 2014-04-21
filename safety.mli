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

exception Unsafe of Node.t

val check : Ast.t_system -> Node.t -> unit
(** [check s n] raises [Unsafe n] if the node [n] is immediately reachable in
    the system [s], i.e. if [n /\ s.init] is not unsatifiable. Otherwise it
    does nothing.*)
