
type t

type exp

val empty : t

val singleton : Solver_types.atom -> t

val union : t -> t -> t

val merge : t -> t -> t

val iter_atoms : (Solver_types.atom -> unit)  -> t -> unit

val fresh_exp : unit -> int

val remove_fresh : int -> t -> t option

val add_fresh : int -> t -> t

