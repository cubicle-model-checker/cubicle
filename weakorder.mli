
open Weakmem

module F = Smt.Formula

val extract_events_array :
  Types.SAtom.elt array ->
    Types.SAtom.t *
    (H.t * H.t * H.t * H.t list) HMap.t *
    (H2Set.t HMap.t * H2Set.t HMap.t * H.t list HMap.t *
      H2Set.t * H.t list HMap.t * H.t list HMap.t * HSet.t list)
  
val extract_events_set :
  Types.SAtom.t ->
    Types.SAtom.t *
    (H.t * H.t * H.t * H.t list) HMap.t *
    (H2Set.t HMap.t * H2Set.t HMap.t * H.t list HMap.t *
      H2Set.t * H.t list HMap.t *H.t list HMap.t * HSet.t list)

val make_orders :
  ?fp:bool ->
  (H.t * H.t * H.t * H.t list) HMap.t ->
    (H2Set.t HMap.t * H2Set.t HMap.t * H.t list HMap.t *
      H2Set.t * H.t list HMap.t *H.t list HMap.t * HSet.t list) ->
    F.t option


val make_prop :
  ('a * H.t * H.t * H.t list) HMap.t ->
    (H2Set.t HMap.t * H2Set.t HMap.t * H.t list HMap.t *
      H2Set.t * H.t list HMap.t * H.t list HMap.t * HSet.t list) ->
    H2Set.t
