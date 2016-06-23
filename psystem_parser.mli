exception Found

type tag = Comment | Hover | UndoComment | UndoHover | Var

val buffer_l : int ref
val buffer_c : int ref
val inact_l : (int * int) list ref
val cancel_last_visited : unit -> (tag * int * int) list
val parse_psystem : Ptree.psystem -> (tag * int * int) list
val parse_init : Ptree.psystem -> unit
val parse_linact: Ptree.psystem -> unit
val parse_var : Ptree.psystem -> (tag * int * int) list
val parse_psystem_m : Ptree.psystem -> (tag * int * int) list
val punsafe_length : Ptree.psystem -> int
