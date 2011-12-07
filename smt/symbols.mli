
type operator = 
  | Plus | Minus | Mult | Div | Modulo 

type name_kind = Ac | Constructor | Other

type t = 
  | True 
  | False
  | Name of Hstring.t * name_kind
  | Int of Hstring.t
  | Op of operator
  | Var of Hstring.t

val name : ?kind:name_kind -> Hstring.t -> t
val var : string -> t
val int : string -> t

val is_ac : t -> bool

val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int

val print : Format.formatter -> t -> unit

module Map : Map.S with type key = t
module Set : Set.S with type elt = t

