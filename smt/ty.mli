
type t = 
  | Tint
  | Tbool
  | Tabstract of Hstring.t
  | Tsum of Hstring.t * Hstring.t list

val hash : t -> int
val equal : t -> t -> bool
val compare : t -> t -> int
val print : Format.formatter -> t -> unit
