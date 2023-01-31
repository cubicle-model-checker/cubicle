module IntMap = Map.Make(struct type t = int let compare : int -> int -> int = Int.compare end) 

type variable       = string * string * int   (* name, type, dim *) 
type variable_table = variable list * (string -> int list -> string) (* var_list, var_as_string *)

type init = unit -> unit

type transition_req   = (int list -> bool)
type transition_ac    = (int list -> unit)
type transition       = string * transition_req * transition_ac 
(* NOTE : 
  Stocker les transition dans la table de cette façon n'a de sens que pour la simulation, mais si on veut que l'utilisateur accède directement a la fonction,
  il serait intéréssant d'avoir une Hashtbl indexé par un string (nom de fonction) et qui renvoie une paire de fonction (req, ac).
  Une solution simple serait de transformer la transition_table en une table qui renvoie un String, 
  et ensuite si on veut la transition on va regarder dans la Hashtbl stockant les transition.
*)
type transition_table = transition list IntMap.t                (* Key is number of argument of transitions *)


type t = variable_table * init * transition_table 

let empty : t = (([], fun _ -> failwith "Not found"), (fun () -> ()), IntMap.empty )

let add_trans nb_arg trans ((mvars, minit,  mtrans) : t) : t = 
  let cur = try IntMap.find nb_arg mtrans with Not_found -> [] in
  (mvars, minit, IntMap.add nb_arg (trans::cur) mtrans)

let set_init minit ((mvars, _, mtrans) : t) : t = 
  (mvars, minit, mtrans)

let set_vars mvars ((_, minit, mtrans) : t) : t =
  (mvars, minit, mtrans)
