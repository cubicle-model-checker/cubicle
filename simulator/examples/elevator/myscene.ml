(*                                      *)
(*  An example scene for "evelator.cub" *) 
(*                                      *)

open Utils
open Simulator
open Bgraphics
open Traces

let window_size = 600
let button_color_success  = Color.green 
let button_color_failure  = Color.red
let button_color_off      = Color.black 
let button_color_hover    : Color.t = { r=25; g=25; b=25}

let get_asc_dir () = 
  match get_vuv_const "Dir" with 
  | VConstr s -> s 
  | _ -> failwith "Wrong model : dir is wrongly typed"

let get_asc_level () = 
  match get_vuv_const "CurFloor" with 
  | VInt i -> i 
  | _ -> failwith "Wrong model : Cur_floor is not int"

let indic_requested_floor i () = 
  match get_vuv_for_proc "Request" i with 
  | VBool b -> b 
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
  let center : Vector.t = { x = 250; y = 0 } in 

  (*  
    For each process, create a floor. 
    A floor is composed of a button to call the elevator,
    and an indicator showing if the elevator is called on the floor. 
  *)
  for i=0 to cell_count - 1 do
    let pos = Composition.expand_col center (cell_size) cell_count i in 
    let new_button : Button.t = 
      {
        name  = Format.sprintf "Request floor %d" i;
        f     = button_request_floor i;
        pos;
        size  = actual_size;
        color_success=button_color_success;
        color_hover=button_color_hover;
        color_failure=button_color_failure;
        color_off=button_color_off;
      }
    in 
    let pos = Vector.sub pos { x = actual_size; y = 0 } in
    let new_indicator : Indicator.t = 
      {
        name = "";
        f    = indic_requested_floor i;
        pos;
        size=indicator_size;
        color_on=Color.green;
        color_off=Color.black;
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
    (* 
       The only simulation that is interesting 
       on this model is the one where Next[i] = i+1, 
        so we force the value of this variable. 
    *)
    let tmp = ref [] in
    for i = cell_count-1 downto 0 do 
      tmp := (VInt(i+1))::!tmp
    done;
    set_var "Next" (Arr !tmp); 
    Simulator.lock_trans "t_request"; (* Lock transition for request, allowing only the user to call the elevator. *)
    in

  let on_model_change () = 
    clear_graph ();
    List.iter Renderer.draw_button !buttons;
    List.iter Renderer.draw_indicator !indicators;
    (* -- Draw elevator -- *)
    set_color red;
    let asc_center : Vector.t = Vector.sub center { x = cell_size ; y = 0 } in
    let asc_pos = Composition.expand_col asc_center (cell_size) cell_count (get_asc_level ()) in
    let center_pos = Vector.sub asc_pos { x = actual_size / 2; y = actual_size / 2 } in 
    fill_rect center_pos.x center_pos.y actual_size actual_size;
    set_color black;
    let dir_str = get_asc_dir () in
    let (w, _) = text_size  dir_str in
    moveto (asc_pos.x - (w / 2)) asc_pos.y;
    draw_string dir_str; 

    Renderer.draw_ui_all ();

    synchronize ()
  in

  let update dt =
    Input.update on_model_change !buttons dt;
  in

  let s : Scene.t = {pre_init; post_init; on_model_change; update; } in 
  set_scene(s)
