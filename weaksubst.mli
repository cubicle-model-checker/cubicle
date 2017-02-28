
open Weakmem

val get_evts :
  Types.Atom.t array ->
  ((H.t * H.t * H.t list) * (bool * Types.op_comp * Types.Term.t) list)
  HMap.t HMap.t

val remap_events :
  Types.Atom.t array ->
  Variable.t H2Map.t list ->
  Types.Atom.t array list

val build_event_substs :
  ((H.t * H.t * H.t list) * (bool * Types.op_comp * Types.term) list)
    HMap.t HMap.t ->
  ((H.t * H.t * H.t list) * (bool * Types.op_comp * Types.term) list)
    HMap.t HMap.t ->
  Variable.t H2Map.t list
