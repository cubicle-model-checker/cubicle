open Utils
open Graphics

(* A Scene library using Graphics. *)

(* Functions for interaction *)
let get_hovered_proc () = () (* TODO *)

(* Function for drawing procs *)
let write_centered_text_in_box txt xbl ybl xtr ytr =
  () (* TODO *)
let draw_square_proc get_proc_text get_proc_color r i x y = 
  set_color (get_proc_color i);
  let lx = x - (r/2) in
  let ly = y - (r/2) in
  draw_rect lx ly r r;
  let txt_list = get_proc_text i in
  let cy = ref (ly+r) in
  let write_text txt =
    let (txt_width, txt_height) = text_size txt in
    cy := (!cy) - txt_height;
    let x_offset = (r - txt_width) / 2 in
    moveto (lx+x_offset) (!cy);
    draw_string txt
  in
  List.iter write_text txt_list

(* Functions for compositions *)

let proc_size_rayon border_size space_perc =
  let proc_size = ((Graphics.size_x ()) - (border_size*2)) / (get_nb_proc ()) in
  let rayon = (proc_size*space_perc) / 200 in
  (proc_size, rayon)

let row_composition border_size proc_size i =
  let x_coord = border_size + (proc_size*i) + (proc_size/2) in
  let y_coord = (size_y ()) / 2 in
  (x_coord, y_coord)

let col_composition border_size proc_size i =
  let y_coord = border_size + (proc_size*i) + (proc_size/2) in
  let x_coord = (size_x ()) / 2 in
  (x_coord, y_coord)

let grid_composition border_size i = 
  () (* TODO *)

(* Functions for interaction *)
let get_pressed_key () = if key_pressed () then Some (read_key ()) else None

(* "Main" function *)
let draw_procs draw_proc composition_function =
  for i = 0 to (get_nb_proc ()-1) do
    let (x_coord, y_coord) = composition_function i in
    draw_proc i x_coord y_coord 
  done
