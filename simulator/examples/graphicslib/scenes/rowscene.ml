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

let get_proc_color i = black

let draw_procs () = 
  let (proc_size, rayon) = Scenelib.proc_size_rayon border_size space_perc        in
  let compfun     = Scenelib.row_composition border_size proc_size                in
  let drawprocfun = Scenelib.draw_square_proc get_proc_text get_proc_color rayon  in 
  Scenelib.draw_procs drawprocfun compfun

let build_scene () = 
  
  let pre_init  () =
    let ws = string_of_int window_size in
    open_graph (" "^ws^"x"^ws);
    auto_synchronize false
  in

  let post_init () = 
    clear_graph();
    draw_procs ();
    synchronize()
  in

  let update dt = () in

  let on_model_update () =
    clear_graph ();
    draw_procs ();
    synchronize ()
  in


  let s = (pre_init, post_init, on_model_update, update) in 
  set_scene(s)
