(*                                                      *)
(*  An example scene that should work for any model     *) 
(*  using the petri net scene library.                  *)
(*                                                      *)

open Utils
open Simulator

let build_scene () =

  let on_model_change () = 
    let ((name_of_trans, args), _) = get_last_trace () in 
    if List.length args > 0 then 
      (
      Format.printf "Took %s with args : " name_of_trans;
      print_list_int args;
      )
    else 
      Format.printf "Took %s\n" name_of_trans;

    dumper ();
  in

  let update dt   = () in 
  let post_init   = on_model_change in 
  let pre_init () = () in
  
  let s : Scene.t = {pre_init; post_init; on_model_change; update; } in 
  set_scene(s)
