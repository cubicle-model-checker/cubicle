open Maps
open Traces

(* TODO
  - Ne pas avoir un type t persistant : utiliser des Hashtbl plutôt que des maps
*)

type variable       = string * string * int   (* name, type, dim *) 
type variable_table = variable list * (unit -> model_state) * (model_state -> unit) (* var_list, state getter, state setter*)

type init = unit -> unit

type transition_req   = (int list -> bool)
type transition_ac    = (int list -> unit)
type transition       = transition_req * transition_ac 

type transition_map   = transition StringMap.t  
type transition_table = string list IntMap.t                (* Key is number of argument of transitions, value is name of transition*)
type transitions      = transition_map * transition_table

type unsafe           = (int list -> bool)
type unsafes          = (unsafe list) IntMap.t

type t = 
  { 
    vars    : variable_table;
    init    : unit -> unit;
    trans   : transitions;
    unsafe  : unsafes;
  }

let empty : t = 
  {
    vars    = ([], (fun () -> StringMap.empty), (fun _-> ()));
    init    = (fun () -> ());
    trans   = (StringMap.empty, IntMap.empty);
    unsafe  = IntMap.empty;
  }

let add_trans nb_arg (trans_name, trans_req, trans_ac)  (model : t) : t = 
  let (mtransmap, mtranstable) = model.trans in
  let cur = try IntMap.find nb_arg mtranstable with Not_found -> [] in
  let new_trans = (StringMap.add trans_name (trans_req, trans_ac) mtransmap, IntMap.add nb_arg (trans_name::cur) mtranstable) in 
  {
    vars    = model.vars;
    init    = model.init;
    trans   = new_trans;
    unsafe  = model.unsafe;
  }

let add_unsafe nb_arg unsafe_fun (model : t) : t =
  let cur = try IntMap.find nb_arg model.unsafe with Not_found -> []  in
  let new_unsafe = IntMap.add nb_arg (unsafe_fun :: cur) model.unsafe in
  {
    vars    = model.vars;
    init    = model.init;
    trans   = model.trans;
    unsafe  = new_unsafe;
  }

let set_init minit (model : t) : t = 
  { 
    vars    = model.vars;
    trans   = model.trans;
    init    = minit;
    unsafe  = model.unsafe;
  }
let set_vars mvars (model : t) : t =
  {
    vars    = mvars;
    trans   = model.trans;
    init    = model.init;
    unsafe  = model.unsafe;
  }

(* Getters & Dynamic Setters *)
let get_state (model : t) : model_state =
  let (_, state_getter,_) = model.vars in
  state_getter ()

let set_state (model : t) (new_state : model_state) =
  let (_,_,state_setter) = model.vars in
  state_setter new_state

let get_vars    (model : t) = model.vars
let get_init    (model : t) = model.init
let get_trans   (model : t) = model.trans
let get_unsafe  (model : t) = model.unsafe

(* Other *)

let vuv_to_string = function
    | VInt(i) -> Format.sprintf "%d " i
    | VFloat(f) -> Format.sprintf "%f " f
    | VBool(b) -> Format.sprintf "%b " b
    | VConstr(s) -> Format.sprintf "%s " s
    | _ -> "?" (* Missing : VLock, VSemaphore... *)
