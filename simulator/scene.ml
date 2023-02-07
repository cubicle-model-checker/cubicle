(* 
  pre_init          : Called before model init
  post_init         : Called after model init
  on_model_change   : Called when model changed
  update            : Called each tick. Parameter is time ellapsed since last call
*)
type t    = (unit -> unit) * (unit -> unit) * (unit -> unit) * (float -> unit)  

let empty : t = ((fun () -> ()), (fun () -> ()), (fun () -> ()), (fun _ -> ()))
