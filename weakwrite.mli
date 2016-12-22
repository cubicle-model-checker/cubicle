
open Weakmem

val split_event :
  Types.Atom.t ->
  (H.t * H.t * (Hstring.t * Hstring.t) list *
     (bool * Types.op_comp * Types.Term.t) list) H3Map.t ->
  (H.t * H.t * (Hstring.t * Hstring.t) list *
     (bool * Types.op_comp * Types.Term.t) list) H3Map.t

val satisfy_reads :
  'a -> Types.SAtom.t -> Types.SAtom.t list
					   
val satisfy_unsatisfied_reads :
  Types.SAtom.t -> Types.SAtom.t
