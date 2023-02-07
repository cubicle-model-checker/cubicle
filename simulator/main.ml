open Unix

let _ =
  if Array.length Sys.argv <= 2 then Format.printf "Usage : ./%s [nb_proc] [sleep_time]\n" Sys.argv.(0);
  Utils.set_nb_proc (int_of_string Sys.argv.(1));
  let sleep_time  = float_of_string Sys.argv.(2)    in
  let last_time   = ref (time ()) in
  
  Mymodel.build_model ();
  Myscene.build_scene ();

  let (scene_preinit, scene_postinit, scene_onmodelchange, scene_update) = Utils.get_scene () in

  scene_preinit ();
  Simulator.init ();
  scene_postinit ();

  while true do
    let t = time () in
    let delt = t -. (!last_time) in
    (*scene_update delt; *)
    if delt > sleep_time then
      (
        Simulator.step ();
        scene_onmodelchange ();
        last_time := t
      )
  done
