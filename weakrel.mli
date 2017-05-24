
open Types
open Weakmem
open Weakevent

val filter_rels_array : ArrayAtom.t -> SAtom.t

val filter_rels_set : SAtom.t -> SAtom.t

(* val extract_rels_array : ArrayAtom.t -> H.t HMap.t * H2Set.t * H2Set.t *)

(* val extract_rels_set : SAtom.t -> H.t HMap.t * H2Set.t * H2Set.t *)

(*
val make_ghb :
  ((H.t * H.t * H.t * H.t list) * (cop * Term.t) list) HMap.t ->
    (HSet.t HMap.t * H2Set.t HMap.t * H2Set.t HMap.t *
      H.t list HMap.t * H2Set.t * H.t list HMap.t * HSet.t list) ->
    H2Set.t

val make_scloc :
  ((H.t * H.t * H.t * H.t list) * (cop * Term.t) list) HMap.t ->
    (HSet.t HMap.t * H2Set.t HMap.t * H2Set.t HMap.t *
      H.t list HMap.t * H2Set.t * H.t list HMap.t * HSet.t list) ->
    H2Set.t
 *)


(* val add_pairs_aux : H2Set.t -> H.t -> H.t -> H2Set.t *)

(* val add_pairs : H2Set.t -> H2Set.t -> H.t -> H.t -> H2Set.t *)

(* val get_new_pairs : H2Set.t -> H2Set.t -> H.t -> H.t -> H2Set.t *)

(* val acyclic : H2Set.t -> bool *)
      
(* val acyclic_n : Ast.node_cube -> unit *)



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
  val add_lt : H.t -> H.t -> t -> t
  val add_eq : H.t -> H.t -> t -> t
  val diff : t -> t -> t
  val acyclic : t -> bool
end

val extract_rels_array : ArrayAtom.t -> H.t HMap.t * Rel.t

val extract_rels_set : SAtom.t -> H.t HMap.t * Rel.t

val subst : Variable.subst -> H.t HMap.t * Rel.t -> H.t HMap.t * Rel.t
