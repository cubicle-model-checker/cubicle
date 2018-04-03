
open Channels
open Chanevent
open Types

val filter_rels_array : ArrayAtom.t -> SAtom.t

val filter_rels_set : SAtom.t -> SAtom.t

module Rel : sig
  type t
  val empty : t
  val iter_lt : (H.t -> H.t -> unit) -> t -> unit
  val iter_eq : (H.t -> H.t -> unit) -> t -> unit
  val fold_lt : (H.t -> H.t -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_eq : (H.t -> H.t -> 'a -> 'a) -> t -> 'a -> 'a
  val exists_lt : (H.t -> H.t -> bool) -> t -> bool
  val exists_eq : (H.t -> H.t -> bool) -> t -> bool
  val mem_lt : H.t -> H.t -> t -> bool
  val mem_eq : H.t -> H.t -> t -> bool
  val print_lt : Format.formatter -> t -> unit
  val print_eq : Format.formatter -> t -> unit
  val get_pred : H.t -> t -> HSet.t
  val get_succ : H.t -> t -> HSet.t
  val get_equ : H.t -> t -> HSet.t
  val add_lt : H.t -> H.t -> t -> t
  val add_eq : H.t -> H.t -> t -> t
  val diff : t -> t -> t
  val acyclic : t -> bool
end

val extract_rels_array : ArrayAtom.t -> Rel.t

val extract_rels_set : SAtom.t -> Rel.t
