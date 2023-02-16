open Maps
open Traces

(* Types *)

type variable       = string * string * int   (* name, type, dim *) 
type variable_table = variable list * (unit -> model_state) * (model_state -> unit) (* var_list, state getter, state setter*)

type init = unit -> unit

type transition_req   = (int list -> bool)
type transition_ac    = (int list -> unit)
type transition       = transition_req * transition_ac 

type transition_map   = transition StringMap.t  
type transition_table = string list IntMap.t                (* Key is number of argument of transitions, value is name of transition*)
type transitions      = transition_map * transition_table

type t = variable_table * init * transitions

let empty : t = 
  let vt = ([], (fun () -> StringMap.empty), (fun _-> ())) in
  let tr = (StringMap.empty, IntMap.empty) in
  (vt, (fun () -> ()), tr)

let add_trans nb_arg (trans_name, trans_req, trans_ac)  ((mvars, minit, (mtransmap, mtranstable)) : t) : t = 
  let cur = try IntMap.find nb_arg mtranstable with Not_found -> [] in
  (mvars, minit, (StringMap.add trans_name (trans_req, trans_ac) mtransmap, IntMap.add nb_arg (trans_name::cur) mtranstable))

let set_init minit ((mvars, _, mtrans) : t) : t = 
  (mvars, minit, mtrans)

let set_vars mvars ((_, minit, mtrans) : t) : t =
  (mvars, minit, mtrans)

(* Getters & Dynamic Setters *)

let get_state (((_, state_getter, _), _, _) : t) : model_state =
  state_getter ()

let set_state (((_, _, state_setter), _,_) : t) (new_state : model_state) =
  state_setter new_state

let get_vars (vars, _, _) = vars
let get_init (_, init, _) =  init
let get_trans (_,_,trans) = trans


(* Other *)

let vuv_to_string = function
    | VInt(i) -> Format.sprintf "%d " i
    | VFloat(f) -> Format.sprintf "%f " f
    | VBool(b) -> Format.sprintf "%b " b
    | VConstr(s) -> Format.sprintf "%s " s
    | _ -> "?" (* Missing : VLock, VSemaphore... *)
