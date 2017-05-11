
open Types
open Weakmem
open Weakevent

val filter_rels_array : SAtom.elt array -> SAtom.t

val filter_rels_set : SAtom.t -> SAtom.t

val extract_rels_array :
  ((H.t * H.t * H.t * H.t list) * 'c) HMap.t ->
  ArrayAtom.t ->
    SAtom.t * (HSet.t HMap.t * H2Set.t * HSet.t list)

val extract_rels_set :
  ((H.t * H.t * H.t * H.t list) * 'c) HMap.t ->
  SAtom.t ->
    SAtom.t * (HSet.t HMap.t * H2Set.t * HSet.t list)

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


val add_rel_aux : H2Set.t -> H.t -> H.t -> H2Set.t

val add_rel : HSet.t list -> H2Set.t -> H.t -> H.t -> H2Set.t

val acyclic : H2Set.t -> bool
      
(* val acyclic_n : Ast.node_cube -> unit *)

