open Bgraphics
open Input 


(* -- Buttons -- *)
let button_text_space = 0 

let draw_button (button : Button.t) =
  let (mx, my) = mouse_pos () in 
  let bs = button.size / 2 in 
  let rbpos = Vector.add button.pos (!cam_pos) in
  let hovered = mx >= rbpos.x - bs && mx <= rbpos.x + bs && my >= rbpos.y - bs && my <= rbpos.y + bs in
  let color = if hovered then 
    (
      if not !button_clicked      then  button.color_hover
      else if !button_last_result then  button.color_success 
      else                              button.color_failure
      ) 
    else button.color_off in
  set_color (Color.to_graphics color);
  fill_rect (button.pos.x - bs) (button.pos.y - bs) button.size button.size;
  let (tsx, tsy) = text_size button.name in
  let nx = button.pos.x - (tsx / 2) in
  let ny = button.pos.y - tsy - button.size - button_text_space in
  moveto nx ny;
  draw_string button.name

(* -- Indicators -- *)

let indic_text_space = 2

let draw_indicator (ind : Indicator.t) =
  let hs = ind.size / 2 in
  let status = ind.f () in
  let color  = if status then ind.color_on else ind.color_off in
  set_color (Color.to_graphics color);
  fill_rect (ind.pos.x - hs) (ind.pos.y - hs) ind.size ind.size;
  let (tsx, tsy) = text_size ind.name in
  let nx = ind.pos.x - (tsx / 2) in
  let ny = ind.pos.y - tsy - ind.size - indic_text_space in
  moveto nx ny;
  draw_string ind.name

(* -- UI -- *)

let draw_ui_pause () = 
  if !Simulator.is_paused then
    (
      set_color black;
      Graphics.moveto (size_x () / 2) 5;
      draw_string "Paused."
    )

let draw_ui_unsafe () = 
  if Simulator.is_unsafe () then 
    (
      set_color red;
      Graphics.moveto (size_x () / 2) (size_y () / 2);
      draw_string "UNSAFE!"
    )

let draw_ui_step () =
  set_color black;
  let step_str = Format.sprintf "Step %d" (Simulator.current_step ()) in 
  
  Graphics.moveto (size_x () / 2) (size_y () - 30);
  draw_string step_str

let draw_ui_all () = 
  draw_ui_pause   ();
  draw_ui_unsafe  ();
  draw_ui_step    ()
