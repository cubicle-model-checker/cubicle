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

open Types

module HMap = Hstring.HMap
       
(** Interface with the SMT solver *)

module SMT : Smt.Solver
(** Instance of the SMT solver *)

val unsafe : Ast.t_system -> Node.t -> unit
(** Checks if the node is directly reachable on init of the system *)

val reached : Hstring.t list -> SAtom.t -> SAtom.t -> unit
(** [reached vars s1 s2] raises [Unsat] if s2 has not been reached *)

val assume_goal : Node.t -> unit
(** Clears the context and assumes a goal formula *)

val assume_node : Node.t -> ArrayAtom.t -> unit
(** [assume_node n a] assumes the negation of a node [n] given in the form of a
    renaming [a]; raises [Unsat] if the context becomes unsatisfiable *)

val assume_goal_no_check : Node.t -> unit
(** Same as {!assume_goal but without the solver check} *)

val assume_node_no_check : Node.t -> ArrayAtom.t -> unit
(** Same as {!assume_node but without the solver check} *)
  
val check_guard : Hstring.t list -> SAtom.t -> SAtom.t -> unit
(** [check_guard vars s g] checks if the guard g is feasible in state [s];
    raises [Unsat] if it is not the case *)

val run : unit -> unit
(** Runs the SMT solver on its current context *)

val assume_goal_nodes : Node.t -> (Node.t * ArrayAtom.t) list -> unit

val init : unit -> unit
