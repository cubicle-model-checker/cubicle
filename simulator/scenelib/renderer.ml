open Bgraphics
open Input 


(* -- Buttons -- *)
let button_text_space = 0 
let button_color_success  = green 
let button_color_failure  = red
let button_color_off      = black 
let button_color_hover    = rgb 50 50 50

let draw_button (button : Button.t) =
  let (mx, my) = mouse_pos () in 
  let bs = button.size / 2 in 
  let rbpos = Vector.add button.pos (!cam_pos) in
  let hovered = mx >= rbpos.x - bs && mx <= rbpos.x + bs && my >= rbpos.y - bs && my <= rbpos.y + bs in
  let color = if hovered then 
    (
      if not !button_clicked then button_color_hover
      else if !button_last_result then button_color_success 
      else button_color_failure
      ) 
    else button_color_off in
  set_color color;
  fill_rect (button.pos.x - bs) (button.pos.y - bs) button.size button.size;
  let (tsx, tsy) = text_size button.name in
  let nx = button.pos.x - (tsx / 2) in
  let ny = button.pos.y - tsy - button.size - button_text_space in
  moveto nx ny;
  draw_string button.name

(* -- Indicators -- *)

let indic_text_space = 2

let draw_indicator on_color off_color (ind : Indicator.t) =
  let hs = ind.size / 2 in
  let status = ind.f () in
  let color  = if status then on_color else off_color in
  set_color color;
  fill_rect (ind.pos.x - hs) (ind.pos.y - hs) ind.size ind.size;
  let (tsx, tsy) = text_size ind.name in
  let nx = ind.pos.x - (tsx / 2) in
  let ny = ind.pos.y - tsy - ind.size - indic_text_space in
  moveto nx ny;
  draw_string ind.name
