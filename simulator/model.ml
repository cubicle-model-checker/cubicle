module IntMap = Map.Make(struct type t = int let compare : int -> int -> int = Int.compare end) 
module StringMap = Map.Make(struct type t = string let compare : string -> string -> int = String.compare end)

(* Types *)

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

type model_state = ((string * var_value) list)      (* name of var * value list *)

type trace = (string * int list) * model_state      (* name of transition taken to get here, args, state adter transition was taken *)
type full_trace = model_state * trace list          (* initial_state, list of transition taken *)

type variable       = string * string * int   (* name, type, dim *) 
type variable_table = variable list * (unit -> model_state) (* var_list, state getter*)

type init = unit -> unit

type transition_req   = (int list -> bool)
type transition_ac    = (int list -> unit)
type transition       = transition_req * transition_ac 

type transition_map   = transition StringMap.t  
type transition_table = string list IntMap.t                (* Key is number of argument of transitions, value is name of transition*)
type transitions      = transition_map * transition_table

type t = variable_table * init * transitions

let empty : t = (([], fun () -> []), (fun () -> ()), (StringMap.empty, IntMap.empty))

let add_trans nb_arg (trans_name, trans_req, trans_ac)  ((mvars, minit, (mtransmap, mtranstable)) : t) : t = 
  let cur = try IntMap.find nb_arg mtranstable with Not_found -> [] in
  (mvars, minit, (StringMap.add trans_name (trans_req, trans_ac) mtransmap, IntMap.add nb_arg (trans_name::cur) mtranstable))

let set_init minit ((mvars, _, mtrans) : t) : t = 
  (mvars, minit, mtrans)

let set_vars mvars ((_, minit, mtrans) : t) : t =
  (mvars, minit, mtrans)

(* Getters *)

let get_state (((_, state_getter), _, _) : t) : model_state =
  state_getter ()

(* Other *)

let vuv_to_string = function
    | VInt(i) -> Format.sprintf "%d " i
    | VFloat(f) -> Format.sprintf "%f " f
    | VBool(b) -> Format.sprintf "%b " b
    | VConstr(s) -> Format.sprintf "%s " s
    | _ -> "?" (* Missing : VLock, VSemaphore... *)
