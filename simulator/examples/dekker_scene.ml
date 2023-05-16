(*                                     *)
(*  An example scene for "dekker"      *) 
(*  using the petri net scene library. *)
(*                                     *)
open Utils
open Simulator
open Petrilib

let build_scene () =

  let pmodel = Petri.empty () in

  Petri.add_state pmodel "Idle"    {x=100; y=400};
  Petri.add_state pmodel "Want"      {x=350; y=600};
  Petri.add_state pmodel "Crit"      {x=600;y=400};
  
  let state_from_proc i = 
    match get_vuv_for_proc "Status" i with
    | VConstr c -> c
    | _         -> failwith "Wrong model : Status is not Constr"
  in
  Petri.set_state_fun pmodel state_from_proc;

  (* Create trans *)
  Petri.add_trans pmodel "exit"     (["exit"], {x=350; y=400});
  Petri.add_trans pmodel "enter"    (["enter"], {x=500;y=500});
  Petri.add_trans pmodel "want"     (["req"], {x=200; y=500});

  (* Create arcs *)
  Petri.add_arc pmodel (Petri.StateToTrans("Idle", "want"));
  Petri.add_arc pmodel (Petri.TransToState("want", "Want"));
   
  Petri.add_arc pmodel (Petri.StateToTrans("Crit", "exit"));
  Petri.add_arc pmodel (Petri.TransToState("exit", "Idle"));
  
  Petri.add_arc pmodel (Petri.StateToTrans("Want", "enter"));
  Petri.add_arc pmodel (Petri.TransToState("enter", "Crit"));
  
  (* Create buttons *)
  Simulator.lock_trans "req";
  Simulator.lock_trans  "enter";

  let request_fun () = Simulator.take_transition_if_possible "req" in 
  Petri.add_button pmodel "Enter want"        request_fun {x = 200; y=300};

  let enter_fun () = Simulator.take_transition_if_possible "enter" in
  Petri.add_button pmodel "Try to enter crit" enter_fun  {x = 500; y=300};

  set_petri pmodel;
  let s : Scene.t = {pre_init; post_init=draw_for_state; on_model_change=draw_for_state; update; } in 
  set_scene(s)
