module IntMap = Map.Make(struct type t = int let compare : int -> int -> int = Int.compare end) 

(*
type variable_type  = string * string list (* Nom du type, valeurs possibles *)
type variable_types = variable_type list
*)

(*
  NOTE:
  Est-ce bien nécéssaire de stocker tout ça ? On n'en aura pas réellement besoin pendant la simulation, et l'utilisateur connaît a priori ces informations;
  Il a accès au fichier cubicle.
*)

type variable       = string * string * int                     (* name, type, dim *) 
type variable_table = variable list * (string -> int list -> string) (* var_list, var_as_string *)

type init = unit -> unit

type transition_req   = (int list -> bool)
type transition_ac    = (int list -> unit)
type transition       = string * transition_req * transition_ac 
type transition_table = transition list IntMap.t                (* Key is number of argument of transitions *)

type t = (* variable_types * *) variable_table * init * transition_table 

let empty : t = (([], fun _ -> failwith "Not found"), (fun () -> ()), IntMap.empty )

let add_trans nb_arg trans ((mvars, minit,  mtrans) : t) : t = 
  let cur = try IntMap.find nb_arg mtrans with Not_found -> [] in
  (mvars, minit, IntMap.add nb_arg (trans::cur) mtrans)

let set_init minit ((mvars, _, mtrans) : t) : t = 
  (mvars, minit, mtrans)

let set_vars mvars ((_, minit, mtrans) : t) : t =
  (mvars, minit, mtrans)
