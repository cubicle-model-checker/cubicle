open Utils

(* 
  An example scene.
  Does nothing.
*)

let build_scene () =
  
  let pre_init  () = Format.printf "Pre_init : Initialising scene. \n%!"  in

  let post_init () = Format.printf "Post_init : Initialising scene. \n%!" in

  let update dt = Format.printf "I'm updating ! Here is the dt : %f\n%!" dt in

  let on_model_update () = Format.printf "Model just updated.\n%!" in


  let s = (pre_init, post_init, on_model_update, update) in 

  set_scene(s)
