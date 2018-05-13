
open Channels
open Chanevent
open Types

val remap_events :
  Types.Atom.t array ->
  Variable.t HMap.t list ->
  Types.Atom.t array list

val build_event_substs :
  ((H.t * H.t * H.t * H.t) * (cop * Types.Term.t) list) HMap.t ->
  (Chanrel.Rel.t) ->
  ((H.t * H.t * H.t * H.t) * (cop * Types.Term.t) list) HMap.t ->
  (Chanrel.Rel.t) ->
    H.t HMap.t list

