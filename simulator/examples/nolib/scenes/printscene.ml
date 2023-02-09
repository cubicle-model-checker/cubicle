open Utils

(* 
  An example scene.
  Does nothing.
*)

let build_scene () =
  
  let pre_init  () = ()  in

  let post_init () = 
    Format.printf "Init state :\n"; 
    dumper (); 
    Format.printf "\n%!" 
  in

  let update dt = () in 

  let on_model_update () = 
    Format.printf "New state : \n";
    dumper ();
    Format.printf "\n%!"
  in


  let s = (pre_init, post_init, on_model_update, update) in 

  set_scene(s)
