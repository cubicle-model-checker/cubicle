open Maps
open Traces

type variable       = string * string * int   (* name, type, dim *) 
type variable_table = variable list * (unit -> model_state) * (model_state -> unit) (* var_list, state getter, state setter*)

type init = unit -> unit

type transition_req   = (int list -> bool)
type transition_ac    = (int list -> unit)
type transition       = transition_req * transition_ac 

type transition_valtable   = (string, transition) Hashtbl.t (* name -> transition *)
type transition_nametable  = (int,    string list) Hashtbl.t (* nb_args -> names   *)
type transitions      = transition_valtable * transition_nametable

type unsafe           = (int list -> bool)
type unsafes          = (int,unsafe list) Hashtbl.t

type t = 
  { 
    vars    : variable_table ref;
    init    : (unit -> unit) ref;
    trans   : transitions;
    unsafe  : unsafes;
  }

let create () = 
  {
    vars    = ref ([], (fun () -> StringMap.empty), (fun _-> ()));
    init    = ref (fun () -> ());
    trans   = (Hashtbl.create 10, Hashtbl.create 10);
    unsafe  = Hashtbl.create 10;
  }

let add_trans nb_arg (trans_name, trans_req, trans_ac)  (model : t) : unit =
  let (valtable, nametable) = model.trans in
  let cur = try Hashtbl.find nametable nb_arg with Not_found -> [] in
  Hashtbl.replace nametable nb_arg (trans_name::cur);
  Hashtbl.replace valtable trans_name (trans_req, trans_ac)

let add_unsafe nb_arg unsafe_fun (model : t) =
  let cur = try Hashtbl.find model.unsafe nb_arg with Not_found -> []  in
  Hashtbl.replace model.unsafe nb_arg (unsafe_fun :: cur)

let set_init minit (model : t) =
  model.init := minit

let set_vars mvars (model : t) =
  model.vars := mvars

(* Getters & Dynamic Setters *)
let get_state (model : t) : model_state =
  let (_, state_getter,_) = !(model.vars) in
  state_getter ()

let set_state (model : t) (new_state : model_state) =
  let (_,_,state_setter) = !(model.vars) in
  state_setter new_state

let get_vars    (model : t) = !(model.vars)
let get_init    (model : t) = !(model.init)
let get_trans   (model : t) = model.trans
let get_unsafe  (model : t) = model.unsafe

(* Other *)

let vuv_to_string = function
    | VInt(i) -> Format.sprintf "%d " i
    | VFloat(f) -> Format.sprintf "%f " f
    | VBool(b) -> Format.sprintf "%b " b
    | VConstr(s) -> Format.sprintf "%s " s
    | _ -> "?" (* Missing : VLock, VSemaphore... *)
