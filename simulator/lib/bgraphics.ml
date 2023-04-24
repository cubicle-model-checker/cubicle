(* 
  An expension of the "Graphics" library with some more feature. 
  Include: 
    - Drawing arrow
    - Drawing with a camera. 
  Relies on the "Input" module to handle camera. 
*)
open Input 

(* Point of the arrow settings *)
let arrow_size    = 20  (* Length of the pointy bit *)
let arrow_pointy  = 30  (* How pointy is it ?       *)

(* Functions included for conveniency *)

(* Initializations *)
let open_graph  = Graphics.open_graph 
let close_graph = Graphics.close_graph 
let set_window_title = Graphics.set_window_title 
let resize_window = Graphics.resize_window
let clear_graph = Graphics.clear_graph
let size_x      = Graphics.size_x
let size_y      = Graphics.size_y 

(* Colors *)
let rgb       = Graphics.rgb 
let set_color = Graphics.set_color 

(* Predefined colors *)

let black   = Graphics.black 
let white   = Graphics.white 
let red     = Graphics.red 
let green   = Graphics.green 
let blue    = Graphics.blue 
let yellow  = Graphics.yellow 
let cyan    = Graphics.cyan
let magenta = Graphics.magenta

(* Point and line drawing *)
let moveto x y        = Graphics.moveto (x + !cam_pos.x) (y + !cam_pos.y)
let fill_rect x y w h = Graphics.fill_rect (x + !cam_pos.x) (y + !cam_pos.y) w h
let lineto x y        = Graphics.lineto (x + !cam_pos.x) (y + !cam_pos.y)
let draw_circle x y r = Graphics.draw_circle (x + !cam_pos.x) (y + !cam_pos.y) r 
let fill_circle x y r = Graphics.fill_circle (x + !cam_pos.x) (y + !cam_pos.y) r

let draw_arrow (from : Vector.t) (toward : Vector.t) = 
      let a = Vector.setsize arrow_pointy (Vector.sub from toward) in
      let draw_pointy pointy = 
          let o = Vector.add toward (Vector.setsize arrow_size pointy) in
          let o = Vector.add a o in
          moveto toward.x toward.y;
          lineto o.x o.y
        in
        moveto from.x from.y;
        lineto toward.x toward.y;
        let ort = Vector.orth (Vector.sub toward from) in
        draw_pointy (ort.(0));
        draw_pointy (ort.(1))

(* Point and line drawing, centered *)

let fill_rect_centered x y w h = Graphics.fill_rect (x + !cam_pos.x - (w / 2)) (y + !cam_pos.y - (h / 2)) w h
let draw_circle_centered x y r = Graphics.draw_circle (x + !cam_pos.x - (r/2)) (y + !cam_pos.y - (r/2)) r
let fill_circle_centered x y r = Graphics.fill_circle (x + !cam_pos.x - (r/2)) (y + !cam_pos.y - (r/2)) r

(* Mouse and keyboard polling *)
let auto_synchronize = Graphics.auto_synchronize
let mouse_pos = Graphics.mouse_pos
let button_down = Graphics.button_down
let synchronize = Graphics.synchronize

(* Text drawing *)
let draw_string = Graphics.draw_string 
let draw_char   = Graphics.draw_char
let set_text_size = Graphics.set_text_size
let text_size = Graphics.text_size


