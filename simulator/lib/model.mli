open Traces

type variable       = string * string * int   (* name, type, dim *) 
type variable_table = variable list * (unit -> model_state) * (model_state -> unit) (* var_list, state getter, state setter*)

type init = unit -> unit

type transition_req   = (int list -> bool)
type transition_ac    = (int list -> unit)
type transition       = transition_req * transition_ac 

type transition_map   = transition Maps.StringMap.t  
type transition_table = string list Maps.IntMap.t                (* Key is number of argument of transitions, value is name of transition*)
type transitions      = transition_map * transition_table

type unsafe          = (int list -> bool)
type unsafes         = (unsafe list) Maps.IntMap.t

type t =
  { vars  : variable_table;
    init  : unit -> unit;
    trans : transitions;
    unsafe : unsafes;
  }

val empty : t
val add_trans  : Maps.IntMap.key -> Maps.StringMap.key * transition_req * transition_ac -> t -> t 
val add_unsafe : int -> unsafe -> t -> t 

val set_init : init -> t -> t
val set_vars : variable_table -> t -> t


val get_state : t -> model_state
val set_state : t -> model_state -> unit

val get_init  : t -> init
val get_vars  : t -> variable_table
val get_trans : t -> transitions 
val get_unsafe : t -> unsafes

val vuv_to_string : var_unit_value -> string
