
type ty= 
  | Tint
  | Tbool
  | Tabstract of Hstring.t
  | Tsum of Hstring.t * Hstring.t list

val hash : ty -> int
val equal : ty -> ty -> bool
val compare : ty -> ty -> int
val print : Format.formatter -> ty -> unit
