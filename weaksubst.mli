

open Weakmem

(* val get_evts : *)
(*   Types.Atom.t array -> *)
(*   ((H.t * H.t * H.t list) * (bool * Types.op_comp * Types.Term.t) list) *)
(*   HMap.t HMap.t *)

val get_evts :
  Types.Atom.t array ->
  ((H.t * H.t * H.t * H.t list) *
    (Weakwrite.cop * Types.Term.t) list) HMap.t

val remap_events :
  Types.Atom.t array ->
  Variable.t HMap.t list ->
  Types.Atom.t array list

(*val build_event_substs :
  ((H.t * H.t * H.t list) * (bool * Types.op_comp * Types.term) list)
    HMap.t HMap.t ->
  ((H.t * H.t * H.t list) * (bool * Types.op_comp * Types.term) list)
    HMap.t HMap.t ->
  Variable.t H2Map.t list*)

val build_event_substs :
  ((H.t * H.t * H.t * H.t list) *
    (Weakwrite.cop * Types.Term.t) list) HMap.t ->
  (H2Set.t HMap.t * H2Set.t HMap.t * H.t list HMap.t *
     H2Set.t * H.t list HMap.t * H.t list HMap.t * HSet.t list) ->
  H2Set.t ->
  H2Set.t ->
  ((H.t * H.t * H.t * H.t list) *
    (Weakwrite.cop * Types.Term.t) list) HMap.t ->
  (H2Set.t HMap.t * H2Set.t HMap.t * H.t list HMap.t *
     H2Set.t * H.t list HMap.t * H.t list HMap.t * HSet.t list) ->
  H2Set.t ->
  H2Set.t ->
      Variable.t HMap.t list

