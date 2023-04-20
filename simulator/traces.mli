type var_unit_value = 
  | VInt        of int
  | VFloat      of float
  | VBool       of bool
  | VConstr     of string
  | VLock       of int option
  | VRlock      of int option * int
  | VSemaphore  of int

type var_value = 
  | Val  of var_unit_value
  | Arr  of var_unit_value list
  | Mat  of var_unit_value list list

type model_state = var_value Maps.StringMap.t            (* name of var * value list *)

type tstep = (string * int list) * model_state      (* name of transition taken to get here, args, state adter transition was taken *)
type t 

val current_step : t -> int
val start 	  : t -> int -> unit      (* Recalibrer position *)
val get   	  : t -> tstep				    (* Récup current elem  *)
val next      : t -> unit
val prev      : t -> unit
val add       : t -> tstep -> unit    (* add step at i *)
val empty     : unit -> t
val position  : t -> int              (* récup current position *)
val save      : t -> Format.formatter -> unit             (* Save the current trace in a model that will play the trace *)
