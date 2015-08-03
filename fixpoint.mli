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

(** Fixpoint tests with optimizations *)

(** Fixpoint tests on list structures *)
module FixpointList : sig

  val check : Node.t -> Node.t list -> int list option
  (** [check s v] returns the tags of nodes in v that were used if [s] implies
      the disjunction of the nodes in [v]. Otherwise, it returns [None]. *)

  val pure_smt_check : Node.t -> Node.t list -> int list option
  (** Same as [check] but only uses the SMT solver. Only use for benchmarking
      purposes or for reference implementation. *)
end

module FixpointCubeList : sig

  val fix_hard : int ref

  val check : Cube.t -> Cube.t list -> int list option
  (** [check s v] returns the tags of cubes in v that were used if [s] implies
      the disjunction of the cubes in [v]. Otherwise, it returns [None]. *)
    
end


module FixpointCertif : sig

  val useful_instances : Node.t -> Node.t list -> (Node.t * Variable.subst) list
  (** Returns the cube instances that were useful in proving the fixpoint.
      Raises Assertion_failure if it is not a fixpoint.
      (Useful for certificates) *)
end

(** Fixpoint tests on trie structures *)
module FixpointTrie : sig

  val easy_fixpoint : Node.t -> Node.t Cubetrie.t -> int list option
  (** easy fixpoint test with subset tests *)

  val peasy_fixpoint : Node.t -> Node.t Cubetrie.t -> int list option
  (** easy fixpoint test including permutations *)

  val hard_fixpoint : Node.t -> Node.t Cubetrie.t -> int list option
  (** full semantic fixpoint test with SMT solver *)

  val check : Node.t -> Node.t Cubetrie.t -> int list option
  (** [check s v] returns the tags of nodes in v that were used if [s] implies
      the disjunction of the nodes in [v]. Otherwise, it returns [None]. *)

end


module FixpointTrieNaive : sig
  (** {b Warning}: Only for benchmarking purposes *)

  val check : Node.t -> Node.t Cubetrie.t -> int list option

end
