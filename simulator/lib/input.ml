open Graphics

(* Dynamic variable, dont touch *)
let last_registered_pos = ref Vector.zero
let mouse_down          = ref false
let button_last_result  = ref false
let button_clicked      = ref false
let hovering            = ref false
let mouse_speed = 1

(* Camera globals *)
let cam_pos = ref Vector.zero

let get_pressed_key () = if key_pressed () then Some(read_key ()) else None
let handle_input    () = 
  match get_pressed_key () with
  | Some(c) -> 
      begin match c with
      | ' ' -> Format.printf "Toggled pause. \n%!"; Simulator.toggle_pause ()
      | 'a' -> Format.printf "Taking step back...\n%!"; Simulator.take_step_back ()
      | 'z' -> Format.printf "Taking step forward...\n%!"; Simulator.take_step_forward ()
      | 'r' -> Format.printf "Resetting simulation...\n%!"; Simulator.reset ()
      | c   -> Format.printf "Pressed unbound key : '%c'\n%!" c 
      end
  | _ -> ()

let handle_mouse (on_model_change: unit -> unit) (button_list : Button.t list) (dt : float) = (* TODO : Prendre en paramètre une liste de boutons. Nécéssite création d'un fichier pour les boutons *)  
  let (mx, my) = mouse_pos () in 
  let hovering_local = ref false in 
  (* Button interaction *)
    let handle_button (button : Button.t) =
    let bs = button.size / 2 in 
      let rbpos = Vector.add button.pos (!cam_pos) in
      if mx >= rbpos.x - bs && mx <= rbpos.x + bs && my >= rbpos.y - bs && my <= rbpos.y + bs then (
        if button_down () && (not !button_clicked) then 
          (
            button_last_result := button.f ();
            button_clicked := true
          );
        hovering_local := true;
      )
    in 
    List.iter handle_button button_list;
    if !hovering <> !hovering_local then (
        hovering := !hovering_local;
        on_model_change ();
    );

    if button_down () then (
    (* Camera *)
    let mvec = Vector.{x = mx; y = my} in
    if !mouse_down then begin
      let vecdiff = Vector.mult mouse_speed (Vector.sub mvec !last_registered_pos) in
      cam_pos := Vector.add !cam_pos vecdiff;
      on_model_change ()
    end;
    last_registered_pos := mvec;
    mouse_down := true 
  )
  else (
      mouse_down := false;
      button_clicked := false;
  )

let update on_model_change button_list dt  = (* Automatically manage pausing, navigating through the trace, buttons and Camera *)
  handle_input ();
  handle_mouse on_model_change button_list dt