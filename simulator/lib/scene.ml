(* 
  pre_init          : Called before model init
  post_init         : Called after model init
  on_model_change   : Called when model changed
  update            : Called each tick. Parameter is time ellapsed since last call
*)
type t = 
  { 
    pre_init        : (unit -> unit);
    post_init       : (unit -> unit);
    on_model_change : (unit -> unit);
    update          : (float -> unit);
  }

let empty : t = 
  { 
    pre_init = (fun () -> ());
    post_init = (fun () -> ());
    on_model_change = (fun () -> ());
    update = (fun _ -> ());
  }
