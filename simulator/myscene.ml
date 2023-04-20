(*                                     *)
(*  An example scene for "germanish"   *) 
(*  using the petri net scene library. *)
(*                                     *)

open Utils
open Simulator
open Bgraphics
open Traces

let window_size = 600

let get_asc_dir () = 
  match get_vuv "Dir" with 
  | Val v ->
      begin match v with 
      | VConstr s -> s 
      | _ -> failwith "Wrong model : dir is wrongly typed"
      end 
  | _ -> failwith "Wront model : not dir"

let get_asc_level () = 
  match get_vuv "CurFloor" with 
  | Val v -> 
      begin match v with 
      | VInt i -> i 
      | _ -> failwith "Wrong model : Cur_floor is not int"
      end
  | _ -> failwith "Wrong model : No Cur_Floor" 

let indic_requested_floor i () = 
  match get_vuv "Request" with 
  | Arr a -> 
      begin match List.nth a i with 
      | VBool b -> b 
      | _ -> failwith "Wrong model : no request" 
      end 
  | _ -> failwith "Wrong model : no request"

let button_request_floor i () =
  Simulator.take_transition "t_request" [i]

let build_scene dt =

  let buttons    : Button.t list ref = ref [] in
  let indicators : Indicator.t list ref = ref [] in
  let cell_size = 150  in
  let actual_size = 75 in
  let indicator_size = 50 in 
  let cell_count = Utils.get_nb_proc () in

  for i=0 to cell_count - 1 do
    let pos = Composition.col Vector.zero (cell_size) cell_count i in 
    let new_button : Button.t = 
      {
        name  = Format.sprintf "Request floor %d" i;
        f     = button_request_floor i;
        pos;
        size  = actual_size;
      }
    in 
    let pos = Vector.sub pos { x = actual_size; y = 0 } in
    let new_indicator : Indicator.t = 
      {
        name = "";
        f    = indic_requested_floor i;
        pos;
        size=indicator_size;
      }
    in 
    buttons := new_button::!buttons;
    indicators := new_indicator::!indicators
  done;

  let pre_init () = 
    let ws = string_of_int window_size in
    open_graph (" "^ws^"x"^ws);
    auto_synchronize false
  in

  let post_init () = 
    let tmp = ref [] in
    for i = cell_count-1 downto 0 do 
      tmp := (VInt(i+1))::!tmp
    done;
    set_var "Next" (Arr !tmp);
    Simulator.lock_trans "t_request"
  in

  let on_model_change () = 
    clear_graph ();
    List.iter Renderer.draw_button !buttons;
    List.iter (Renderer.draw_indicator green black) !indicators;
    (* -- Draw elevator -- *)
    set_color red;
    let asc_center : Vector.t = { x = - cell_size ; y = 0 } in
    let asc_pos = Composition.col asc_center (cell_size) cell_count (get_asc_level ()) in
    let center_pos = Vector.sub asc_pos { x = actual_size / 2; y = actual_size / 2 } in 
    fill_rect center_pos.x center_pos.y actual_size actual_size;
    set_color black;
    let dir_str = get_asc_dir () in
    let (w, _) = text_size  dir_str in
    moveto (asc_pos.x - (w / 2)) asc_pos.y;
    draw_string dir_str; 
    synchronize ()
  in

  let update dt =
    Input.update on_model_change !buttons dt;
  in

  let s : Scene.t = {pre_init; post_init; on_model_change; update; } in 
  set_scene(s)
