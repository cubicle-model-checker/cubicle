open Traces

type variable       = string * string * int   (* name, type, dim *) 
type variable_table = variable list * (unit -> model_state) * (model_state -> unit) (* var_list, state getter, state setter*)

type init = unit -> unit

type transition_req   = (int list -> bool)
type transition_ac    = (int list -> unit)
type transition       = transition_req * transition_ac 

type transition_valtable   = (string, transition) Hashtbl.t (* name -> transition *)
type transition_nametable = (int,    string list) Hashtbl.t (* nb_args -> names   *)
type transitions      = transition_valtable * transition_nametable

type unsafe           = (int list -> bool)
type unsafes          = (int,unsafe list) Hashtbl.t

type t

val create : unit -> t
val add_trans  : Maps.IntMap.key -> Maps.StringMap.key * transition_req * transition_ac -> t -> unit 
val add_unsafe : int -> unsafe -> t -> unit 

val set_init : init -> t -> unit
val set_vars : variable_table -> t -> unit


val get_state : t -> model_state
val set_state : t -> model_state -> unit

val get_init  : t -> init
val get_vars  : t -> variable_table
val get_trans : t -> transitions 
val get_unsafe : t -> unsafes

val vuv_to_string : var_unit_value -> string
