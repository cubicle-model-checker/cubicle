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

open Cubtypes

(** Trie structure for cubes sets *)

type 'a t
(** Trie, mapping sets of atoms (i.e. cubes) to values of type 'a *)

val empty : 'a t
(** The empty trie. *)

val is_empty : 'a t -> bool
(** Test emptyness of a trie *)

val add : Atom.t list -> 'a -> 'a t -> 'a t
(** Add a mapping cube->v to trie *)

val add_force : Atom.t list -> 'a -> 'a t -> 'a t
(** Add a mapping cube->v to trie without checking for subsomption *)

val add_array : ArrayAtom.t -> 'a -> 'a t -> 'a t
(** Add a mapping cube->v to trie *)

val add_array_force : ArrayAtom.t -> 'a -> 'a t -> 'a t
(** Add a mapping cube->v to trie without checking for subsomption *)

val mem : Atom.t list -> Node.t t -> int list option
(** Is cube subsumed by some cube in the trie? *)

val mem_array : ArrayAtom.t -> Node.t t -> int list option
(** Is cube subsumed by some cube in the trie? *)

val mem_array_poly : ArrayAtom.t -> 'a t -> bool
(** Is cube subsumed by some cube in the trie? *)

val iter : ('a -> unit) -> 'a t -> unit
(** Apply f to all values mapped to in the trie. *)

val fold : ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b
(** fold f to all values mapped to in the trie. *)

val delete : ('a -> bool) -> 'a t -> 'a t
(** Delete all values which satisfy the predicate p *)

val iter_subsumed : ('a -> unit) -> Atom.t list -> 'a t -> unit
(** Apply f to all values whose keys (cubes) are subsumed by the given cube. *)

val all_vals : 'a t -> 'a list
(** List of all values mapped by the trie *)

val consistent : Atom.t list -> 'a t -> 'a list
(** All values whose keys (cubes) are not inconsistent with the given cube. *)

val add_and_resolve : Node.t -> Node.t t -> Node.t t

val delete_subsumed : ?cpt:int ref -> Node.t -> Node.t t -> Node.t t
(** Delete from the trie nodes that are subsumed by the first arguments *)

val add_node : Node.t -> Node.t t -> Node.t t
(** Add a node in the trie *)
