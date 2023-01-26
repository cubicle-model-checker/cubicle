open Unix
open Stmp (* Construit et initialise le modèle *)

let _ =
  if Array.length Sys.argv <= 2 then Format.printf "Usage : ./%s [nb_proc] [sleep_time]\n" Sys.argv.(0);
  Utils.set_nb_proc (int_of_string Sys.argv.(1));
  Stmp.build_model ();
  let sleep_time  = float_of_string Sys.argv.(2)    in
  let last_time   = ref (time ()) in
  Simulator.init ();
  while true do
    let t = time () in
    let delt = t -. (!last_time) in
    if delt > sleep_time then
      (
        Simulator.step ();
        last_time := (time ())
      )
  done
