
open Weakmem

module F = Smt.Formula

val split_events_orders_array :
  Types.SAtom.elt array ->
  Types.SAtom.t *
    (H.t * H.t * H.t list) HMap.t HMap.t HMap.t *
    H.t list HMap.t

val split_events_orders_set :
  Types.SAtom.t ->
  Types.SAtom.t *
    (H.t * H.t * H.t list) HMap.t HMap.t HMap.t *
    H.t list HMap.t

val make_orders :
  ?fp:bool ->
  (H.t * H.t * H.t list) HMap.t HMap.t HMap.t ->
  H.t list HMap.t ->
  F.t
