open Utils
open Simulator
open Scenelib

(*
  An example scene for Dekker using the petri net scene library
*)

let state_from_proc i = 
  match (get_vuv "Cache") with
  | Arr(a) -> 
      begin match List.nth a i with
      (* Could be done with
      | VConstr(s)  -> s
      But we would lose the error of a wrong model, changing it for an error of a scene.
      *)
      | VConstr("Invalid")    -> "Invalid"
      | VConstr("Shared")     -> "Shared"
      | VConstr("Exclusive")  -> "Exclusive"
      | _                     -> failwith "Wrong model"
      end 
  | _ -> failwith "Wrong Model : No cache"

let build_scene () =

  let pmodel = Petri.empty () in
  Petri.add_state pmodel "Invalid" {x=100; y=100};
  Petri.add_state pmodel "Shared" {x=300;y=500};
  Petri.add_state pmodel "Exclusive" {x=500;y=100};

  (* 
    TODO
    Enter Shared
    Enter Exclusive
    Quit Shared
    Quit Exclusive
  *)


  Petri.add_trans pmodel "req" (["req"], {x=200; y=300});
  Petri.add_trans pmodel "get shared" (["enter"], {x=400; y=300});
  Petri.add_trans pmodel "exit" (["exit"], {x=300;y=100});

  Petri.add_arc pmodel (Petri.StateToTrans("Invalid", "req"));
  Petri.add_arc pmodel (Petri.TransToState("req", "Shared"));

  Petri.add_arc pmodel (Petri.StateToTrans("Shared", "enter"));
  Petri.add_arc pmodel (Petri.TransToState("enter", "Exclusive"));
  Petri.add_arc pmodel (Petri.StateToTrans("Exclusive", "exit"));
  Petri.add_arc pmodel (Petri.TransToState("exit", "Invalid"));

  Petri.set_state_fun pmodel state_from_proc;

  Scenelib.set_petri pmodel;
  
  let s = (pre_init, draw_for_state, draw_for_state, update) in 
  set_scene(s)
