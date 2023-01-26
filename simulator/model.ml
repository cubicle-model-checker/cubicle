module IntMap = Map.Make(struct type t = int let compare : int -> int -> int = Int.compare end) 

type variable_type  = string * string list (* Nom du type, valeurs possibles *)
type variable_types = variable_type list

type variable       = string * string * int (* var_name, var_type, var_dim *)
type variable_table = variable list

type init = unit -> unit

type transition_req   = (int list -> bool)
type transition_ac    = (int list -> unit)
type transition       = string * transition_req * transition_ac 
type transition_table = transition list IntMap.t                (* Key is number of argument of transitions *)

type t = variable_types * variable_table * init * transition_table 

let empty : t = ([], [], (fun () -> ()), IntMap.empty )

let add_trans nb_arg trans ((mtypes, mvars, minit,  mtrans) : t) : t = 
  let cur = try IntMap.find nb_arg mtrans with Not_found -> [] in
  (mtypes, mvars, minit, IntMap.add nb_arg (trans::cur) mtrans)

let set_init minit ((mtypes, mvars, _, mtrans) : t) : t = 
  (mtypes, mvars, minit, mtrans)
