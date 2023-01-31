(* 
  pre_init          : Appelé avant que le modèle soit initialisé
  post_init         : Appelé après que le modèle soit initialisé
  on_model_change   : Appelé lorsque le modèle est modifié
  update            : Appelé chaque tick
*)
type t    = (unit -> unit) * (unit -> unit) * (unit -> unit) * (float -> unit)  

let empty : t = ((fun () -> ()), (fun () -> ()), (fun () -> ()), (fun _ -> ()))
