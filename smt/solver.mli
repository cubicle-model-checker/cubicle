
exception Sat
exception Unsat

val solve : unit -> unit
val assume : Literal.LT.t list list -> unit
val clear : unit -> unit
