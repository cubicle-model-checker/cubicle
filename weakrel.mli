
open Types
open Weakmem
open Weakevent

val filter_rels_array : ArrayAtom.t -> SAtom.t

val filter_rels_set : SAtom.t -> SAtom.t

val extract_rels_array : ArrayAtom.t -> H.t HMap.t * H2Set.t * H2Set.t

val extract_rels_set : SAtom.t -> H.t HMap.t * H2Set.t * H2Set.t

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


val add_pairs_aux : H2Set.t -> H.t -> H.t -> H2Set.t

val add_pairs : H2Set.t -> H2Set.t -> H.t -> H.t -> H2Set.t

val get_new_pairs : H2Set.t -> H2Set.t -> H.t -> H.t -> H2Set.t

val acyclic : H2Set.t -> bool
      
(* val acyclic_n : Ast.node_cube -> unit *)

