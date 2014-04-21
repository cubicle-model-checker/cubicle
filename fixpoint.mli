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

(** {b Fixpoint tests with optimizations }*)

(** Fixpoint tests on list structures *)
module FixpointList : sig

  val check : Node.t -> Node.t list -> int list option
  (** [check s v] returns the tags of nodes in v that were used if [s] implies
      the disjunction of the nodes in [v]. Otherwise, it returns [None]. *)

  val pure_smt_check : Node.t -> Node.t list -> int list option
  (** Same as [check] but only uses the SMT solver. Only use for benchmarking
      purposes or for reference implementation. *)

end

(** Fixpoint tests on trie structures *)
module FixpointTrie : sig

  val check : Node.t -> Node.t Cubetrie.t -> int list option
  (** [check s v] returns the tags of nodes in v that were used if [s] implies
      the disjunction of the nodes in [v]. Otherwise, it returns [None]. *)

end
