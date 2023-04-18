open Graphics
open Elevator_cub

let dx = 400
let dy = 400
  
let _ =
  let s = Format.sprintf " %dx%d" dx dy in
  open_graph s

let end_user () =
  if key_pressed () then raise Exit

let h = 40
let n = dy /h
    
let show () =
  set_color black;
  fill_rect 130 0 2 dx;
  for i = 1 to n do
    fill_rect 125 (i * h) 10 2;
    let circle =
      if get_request i then fill_circle else draw_circle
    in
    circle 150 ((i-1) * h + h / 2) 10
  done;
  set_color red;
  fill_rect 80 ((get_curFloor () - 1) * h) (h+10) h;
  set_color black;
  let dir = if get_dir () = Up then "Up" else "Down" in
  moveto 85 ((get_curFloor () - 1) * h + 5);
  draw_string dir
        
let event () =
  if button_down () then
    begin
      let s = wait_next_event [Poll] in
      let n = 1 + s.mouse_y / h in
      event (Button n);
    end

let _ =
  (*  auto_synchronize false;*)
  try
    while true do
      clear_graph ();
      show ();
      event();
      
      step ();
      
      synchronize ();
      end_user ()
    done
  with Exit -> ()
