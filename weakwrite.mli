
open Weakmem

type cop = CEq | CNeq | CLt | CLe | CGt | CGe

val string_of_cop : cop -> string

val split_event :
  Types.Atom.t ->
  ((H.t * H.t * H.t * (Hstring.t * Hstring.t) list) *
     (cop * Types.Term.t) list) HMap.t ->
  ((H.t * H.t * H.t * (Hstring.t * Hstring.t) list) *
     (cop * Types.Term.t) list) HMap.t

val satisfy_reads :
  'a -> Types.SAtom.t -> Types.SAtom.t list
					   
val satisfy_unsatisfied_reads :
  Types.SAtom.t -> Types.SAtom.t
