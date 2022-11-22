open Cubicle_usual
open Unix

let _ =
  if Array.length Sys.argv <= 2 then Printf.printf "Usage : ./{name} nb_proc sleep_time \n";
  Cubicle_usual.nb_proc := int_of_string Sys.argv.(1);
  let sleep_time = float_of_string Sys.argv.(2) in
  let last_time = ref (time ()) in
  Cubicle_graphics.init ();
  
  while true do
    Cubicle_graphics.handle_input ();
    
    Cubicle_graphics.update();

    let t = time () in
    let delt = t -. (!last_time) in
    if delt > sleep_time then
      (
        step ();
        last_time := (time ())
      )
  done