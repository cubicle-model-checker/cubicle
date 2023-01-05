open Sutils
open Graphics

(* 
* TODO : écrire l'état des variables globales quelque part
* TODO : écrire l'état de toutes les variables d'un proc dans le proc correspondant
*)

(* Settings *)

let border_size = 10
let window_size = 600
let space_perc = 80 (*Exprimé en %*)

(* Graphics *)

let init () =  
  open_graph (" "^(string_of_int window_size)^"x"^(string_of_int window_size));
  set_window_title "Simulation";
  auto_synchronize false
  
(* Seules ces deux fonctions changent réellement entre deux applications cubicle (En plus des fonctions d'intéractions)*)

let get_proc_color i = black

let get_proc_text i = string_of_int i

(* --------- *)

let proc_size_rayon () =
  let proc_size = (window_size - (border_size*2)) / (get_nb_proc ()) in
  let rayon = (proc_size*space_perc) / 200 in
  (proc_size, rayon)

let draw_proc i x y r =
  set_color (get_proc_color i);
  draw_circle x y r;
  moveto x y;
  draw_string (get_proc_text i)

let get_hovered_proc () =
  let (mouse_x, mouse_y) = mouse_pos () in
  let (proc_size, rayon) = proc_size_rayon () in 
  let x = (mouse_x - border_size) / proc_size in
  let y = abs (mouse_y - (window_size/2)) in
  if y <= rayon then x else -1


let show_procs () =
  let (proc_size, rayon) = proc_size_rayon () in
  for i = 0 to (get_nb_proc ()-1) do
    let x_coord = border_size + (proc_size*i) + (proc_size/2) in
    let y_coord = window_size / 2 in
    draw_proc i  x_coord y_coord rayon
  done

let update () =
  clear_graph ();
  show_procs ();
  synchronize ()

let handle_input () =
  let hovered_proc = get_hovered_proc () in
  if button_down () && hovered_proc >= 0 then
    add_event (Click(hovered_proc))
