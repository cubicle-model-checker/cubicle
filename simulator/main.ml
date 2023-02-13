open Unix
open Format

let _ =
  
  if Array.length Sys.argv <= 2 then (printf "Usage : %s [nb_proc] [sleep_time]\n" Sys.argv.(0); exit 1);
  
  let nbproc = (int_of_string Sys.argv.(1)) in
  if nbproc <= 0 then (printf "Number of proc must be strictly positive."; exit 1);
  Utils.set_nb_proc nbproc;
  Simulator.set_sleep_time (float_of_string Sys.argv.(2));
  let last_time   = ref (time ()) in
  
  Mymodel.build_model ();
  Myscene.build_scene ();

  let (scene_preinit, scene_postinit, scene_onmodelchange, scene_update) = Utils.get_scene () in

  Simulator.set_callbacks (scene_preinit, scene_postinit, scene_onmodelchange);
  Simulator.init ();

  while true do
    let t = time () in
    let delt = t -. (!last_time) in
    scene_update delt;
    if delt >= (Simulator.get_sleep_time ()) then
      (
        Simulator.step ();
        last_time := t
      )
  done
