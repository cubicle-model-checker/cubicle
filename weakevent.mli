
open Weakmem

val make_init_write :
  H.t * Variable.t list ->
  (H.t * H.t * H.t) * Types.term * Types.SAtom.t

val events_of_satom : Types.SAtom.t -> Types.SAtom.t
