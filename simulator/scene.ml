type obj  = int * int * (unit -> unit)  (* pos_x, pos_y, draw_object_fun *)
type t    = obj list

let empty : t = []

let update (s : t) = List.iter (fun (_,_,up) -> up ()) s
