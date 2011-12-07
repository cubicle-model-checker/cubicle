
type t
type view = private {f: Symbols.t ; xs: t list; ty: Ty.t; tag : int}

val view : t -> view
val make : Symbols.t -> t list -> Ty.t -> t

val vrai : t
val faux : t
val int : string -> t

val compare : t -> t -> int
val equal : t -> t -> bool
val hash : t -> int

val print : Format.formatter -> t -> unit

module Map : Map.S with type key = t
module Set : Set.S with type elt = t

