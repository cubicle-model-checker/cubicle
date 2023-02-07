open Utils
open Model
open Scenelib
open Graphics

(* 
  An simple sample scene:
  Display the current state in a graphical window with:
*)

let border_size = 10
let window_size = 600
let space_perc = 90

let get_proc_text i =
  let pvals = get_vuv_for_proc i in
  let ret = ref [Format.sprintf "%d" i] in
  let write_vars (vname, vvuv) = 
    let vval_string = Model.vuv_to_string(vvuv) in
    ret := (Format.sprintf "%s: %s" vname vval_string)::(!ret)
  in
  List.iter write_vars pvals;
  List.rev (!ret)

let proc_size_rayon () =
  let proc_size = ((Graphics.size_x ()) - (border_size*2)) / (get_nb_proc ()) in
  let rayon = (proc_size*space_perc) / 200 in
  (proc_size, rayon)

let draw_proc i x y r =
  set_color black;
  let lx = x - (r/2) in
  let ly = y - (r/2) in
  draw_rect lx ly r r;
  let txt_list = get_proc_text i in
  let cy = ref (ly+r) in
  let write_text txt =
    let (_, txt_height) = text_size txt in
    cy := (!cy) - txt_height;
    moveto lx (!cy);
    draw_string txt
  in
  List.iter write_text txt_list

let draw_procs () =
  let (proc_size, rayon) = proc_size_rayon () in
  for i = 0 to (get_nb_proc ()-1) do
    let x_coord = border_size + (proc_size*i) + (proc_size/2) in
    let y_coord = (Graphics.size_y ()) / 2 in
    draw_proc i x_coord y_coord rayon
  done

let build_scene () = 
  let pre_init  () =
    let ws = string_of_int window_size in
    open_graph (" "^ws^"x"^ws);
    auto_synchronize false
  in

  let post_init () = 
    clear_graph();
    draw_procs();
    synchronize()
  in

  let update dt = ()
  in

  let on_model_update () =
    clear_graph ();
    draw_procs ();
    synchronize ()
  in


  let s = (pre_init, post_init, on_model_update, update) in 

  set_scene(s)
