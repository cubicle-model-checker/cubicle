(*                                     *)
(*  An example scene for "germanish"   *) 
(*  using the petri net scene library. *)
(*                                     *)

open Utils
open Simulator
open Bgraphics

let window_size = 600

let button_request_floor i () =
  Simulator.take_transition "t_request" [i]

let get_asc_level () = 
  match get_vuv "CurFloor" with 
  | Val v -> 
      begin match v with 
      | VInt i -> i 
      | _ -> failwith "Wrong model : Cur_floor is not int"
      end
  | _ -> failwith "Wrong model : No Cur_Floor" 

let build_scene dt =

  let buttons : Button.t list ref = ref [] in
  let cell_size = 100 in
  let actual_size = 75 in
  let cell_count = Utils.get_nb_proc () in

  for i=0 to cell_count - 1 do
    let new_button : Button.t = 
      {
        name= Format.sprintf "Request floor %d" i;
        f = button_request_floor i;
        pos = Composition.col Vector.zero (cell_size) cell_count i; 
        size=actual_size;
      }
    in 
    buttons := new_button::!buttons
  done;

  let pre_init () = 
    let ws = string_of_int window_size in
    open_graph (" "^ws^"x"^ws);
    auto_synchronize false
  in

  let on_model_change () = 
    clear_graph ();
    Utils.dumper ();
    List.iter Renderer.draw_button !buttons;
    (* -- Draw elevator -- *)
    set_color red;
    let asc_center : Vector.t = { x = - cell_size * 2; y = 0 } in
    let asc_pos = Composition.col asc_center (cell_size) cell_count (get_asc_level ()) in
    let center_pos = Vector.sub asc_pos { x = cell_size / 2; y = cell_size / 2 } in 
    fill_rect center_pos.x center_pos.y actual_size actual_size;
    synchronize ()
  in

  let update dt =
    Input.update on_model_change !buttons dt;
  in

  let s : Scene.t = {pre_init; post_init=on_model_change; on_model_change; update; } in 
  set_scene(s)
