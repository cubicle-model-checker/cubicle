
open Types
open Weakmem

module Int : sig
  type t = int
  val compare : t -> t -> int
end

module IntSet : Set.S with type elt = Int.t

type cop = CEq | CNeq | CLt | CLe | CGt | CGe

val cop_of_r_op : bool -> Types.op_comp -> cop

val string_of_cop : cop -> string

val extract_events_array :
  ArrayAtom.t ->
   SAtom.t *
   (cop * Term.t) list HEvtMap.t *
   Term.t list HEvtMap.t *
   H.t list *
   IntSet.t HMap.t *
   ((H.t * H.t * H.t * H.t list) * (cop * Term.t) list) HMap.t *
   ((H.t * H.t * H.t * H.t list) * (cop * Term.t) list) HMap.t *
   ((H.t * H.t * H.t * H.t list) * (cop * Term.t) list) HMap.t

val extract_events_set :
  SAtom.t ->
   SAtom.t *
   (cop * Types.Term.t) list HEvtMap.t *
   Term.t list HEvtMap.t *
   H.t list *
   IntSet.t HMap.t *
   ((H.t * H.t * H.t * H.t list) * (cop * Term.t) list) HMap.t *
   ((H.t * H.t * H.t * H.t list) * (cop * Term.t) list) HMap.t *
   ((H.t * H.t * H.t * H.t list) * (cop * Term.t) list) HMap.t
