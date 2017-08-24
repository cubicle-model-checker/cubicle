
open Weakmem
open Weakevent
open Types

val remap_events :
  Types.Atom.t array ->
  Variable.t HMap.t list ->
  Types.Atom.t array list

val build_event_substs :
  ((H.t * H.t * H.t * H.t list) * (cop * Types.Term.t) list) HMap.t ->
  ('a * Weakrel.Rel.t) ->
  ((H.t * H.t * H.t * H.t list) * (cop * Types.Term.t) list) HMap.t ->
  ('a * Weakrel.Rel.t) ->
    H.t HMap.t list

