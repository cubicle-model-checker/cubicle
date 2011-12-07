type t

val init : int -> t
val in_heap : t -> int -> bool
val decrease : (int -> int -> bool) -> t -> int -> unit
(*val increase : (int -> int -> bool) -> t -> int -> unit*)
val size : t -> int
val is_empty : t -> bool
val insert : (int -> int -> bool) -> t -> int -> unit
val grow_to_by_double: t -> int -> unit
(*val update : (int -> int -> bool) -> t -> int -> unit*)
val remove_min : (int -> int -> bool) -> t -> int
val filter : t -> (int -> bool) -> (int -> int -> bool) -> unit
