(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2013                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

(** Trie, mapping cubes to value of type 'a *)
type 'a t

(** The empty trie. *)
val empty : 'a t

(** Test emptyness of a trie *)
val is_empty : 'a t -> bool

(** Add a mapping cube->v to trie *)
val add : Ast.Atom.t list -> 'a -> 'a t -> 'a t

(** Add a mapping cube->v to trie without checking for subsomption *)
val add_force : Ast.Atom.t list -> 'a -> 'a t -> 'a t

(** Add a mapping cube->v to trie *)
val add_array : Ast.ArrayAtom.t -> 'a -> 'a t -> 'a t

(** Add a mapping cube->v to trie without checking for subsomption *)
val add_array_force : Ast.ArrayAtom.t -> 'a -> 'a t -> 'a t

(** Is cube subsumed by some cube in the trie? *)
val mem : Ast.Atom.t list -> Ast.t_system t -> int list option

(** Is cube subsumed by some cube in the trie? *)
val mem_array : Ast.ArrayAtom.t -> Ast.t_system t -> int list option

(** Apply f to all values mapped to in the trie. *)
val iter : ('a -> unit) -> 'a t -> unit

(** fold f to all values mapped to in the trie. *)
val fold : ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b

(** Delete all values which satisfy the predicate p *)
val delete : ('a -> bool) -> 'a t -> 'a t

(** Apply f to all values whose keys (cubes) are subsumed by the given cube. *)
val iter_subsumed : ('a -> unit) -> Ast.Atom.t list -> 'a t -> unit

(** List of all values mapped by the trie *)
val all_vals : 'a t -> 'a list

(** All values whose keys (cubes) are not inconsistent with the given cube. *)
val consistent : Ast.Atom.t list -> 'a t -> 'a list
