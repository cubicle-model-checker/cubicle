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

module type OrderedType = sig
  type t
  val compare : t -> t -> int
end


module Make ( X : OrderedType ) : sig

  type 'a t

  val empty : 'a t
  (** The empty trie. *)

  val is_empty : 'a t -> bool
  (** Test emptyness of a trie *)

  val add : X.t list -> 'a -> 'a t -> 'a t
  (** Add a mapping cube->v to trie *)

  val add_force : X.t list -> 'a -> 'a t -> 'a t
  (** Add a mapping cube->v to trie without checking for subsomption *)

  val mem : X.t list -> 'a t -> 'a option
  (** Is cube subsumed by some cube in the trie? *)

  val iter : ('a -> unit) -> 'a t -> unit
  (** Apply f to all values mapped to in the trie. *)

  val fold : ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b
  (** fold f to all values mapped to in the trie. *)

  val delete : ('a -> bool) -> 'a t -> 'a t
  (** Delete all values which satisfy the predicate p *)

  val iter_sub : ('a -> unit) -> X.t list -> 'a t -> unit
  (** Apply f to all values whose keys (cubes) are subsumed by the given cube. *)

  val all_vals : 'a t -> 'a list
  (** List of all values mapped by the trie *)

  val iter_nodes : (X.t -> unit) -> 'a t -> unit
  val forall_exists : (X.t -> bool) -> 'a t -> bool

end
