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
      | VConstr("Invalid")    -> 0
      | VConstr("Shared")     -> 1
      | VConstr("Exclusive")  -> 2
      | _                     -> failwith "Wrong model"
      end 
  | _ -> failwith "Wrong Model : No cache"

let build_scene () =
  
  let update dt = () in 

  let pmodel = Petri.empty () in
  Petri.set_state pmodel [(0,{x=100; y=100}); (1,{x=300;y=500}); (2,{x=500;y=100})];

  Petri.add_trans pmodel ("req", {x=200; y=300});
  Petri.add_trans pmodel ("enter", {x=400; y=300});
  Petri.add_trans pmodel ("exit", {x=300;y=100});

  Petri.add_arc pmodel (Petri.In(0, "req"));
  Petri.add_arc pmodel (Petri.Out("req", 1));

  Petri.add_arc pmodel (Petri.In(1, "enter"));
  Petri.add_arc pmodel (Petri.Out("enter", 2));
  Petri.add_arc pmodel (Petri.In(2, "exit"));
  Petri.add_arc pmodel (Petri.Out("exit", 0));

  Petri.set_state_fun pmodel state_from_proc;

  Scenelib.set_petri pmodel;
  
  let s = (pre_init, draw_for_state, draw_for_state, update) in 
  set_scene(s)
