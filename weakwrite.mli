
open Weakmem
open Weakevent
open Types

val split_event :
  Atom.t ->
  ((H.t * H.t * H.t * (H.t * H.t) list) * (cop * Term.t) list) HMap.t ->
    ((H.t * H.t * H.t * (H.t * H.t) list) * (cop * Term.t) list) HMap.t

val satisfy_reads :
  'a -> SAtom.t -> SAtom.t list
					   
val satisfy_unsatisfied_reads :
  SAtom.t -> SAtom.t
