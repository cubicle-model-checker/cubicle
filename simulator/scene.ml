(* TODO : Draw_object_fun prend en paramètre le contexte (Fenêtre) *)
type obj  = int * int * (int -> int -> unit)  (* pos_x, pos_y, draw_object_fun *)
type t    = obj list

let empty : t = []

let update (s : t) = List.iter (fun (x,y,up) -> up x y) s
