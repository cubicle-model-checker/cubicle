(*                                     *)
(*  An example scene for "dekker"      *) 
(*  using the petri net scene library. *)
(*                                     *)
open Utils
open Simulator
open Petrilib

let state_from_proc i = 
  match get_vuv_for_proc "Crit" i, get_vuv_for_proc "Want" i with
  | VBool crit, VBool want -> if crit then "Crit" else 
                              if want then "Want" else 
                              "Normal"
  | _        -> failwith "Wrong model : Crit or want is not a bool"

let button_request_crit () =
  Simulator.take_transition "req" [(Utils.get_random_proc ())]

let build_scene () =

  let pmodel = Petri.empty () in

  Petri.add_state pmodel "Normal"    {x=100; y=400};
  Petri.add_state pmodel "Want"      {x=350; y=600};
  Petri.add_state pmodel "Crit"      {x=600;y=400};

  Petri.add_button pmodel "Request crit" button_request_crit {x = 350; y = 250};
  
  (* Create trans *)
  Petri.add_trans pmodel "exit"     (["exit"], {x=350; y=400});
  Petri.add_trans pmodel "enter"    (["enter"], {x=500;y=500});
  Petri.add_trans pmodel "want"     (["req"], {x=200; y=500});

  (* Create arcs *)
  Petri.add_arc pmodel (Petri.StateToTrans("Normal", "want"));
  Petri.add_arc pmodel (Petri.TransToState("want", "Want"));
   
  Petri.add_arc pmodel (Petri.StateToTrans("Crit", "exit"));
  Petri.add_arc pmodel (Petri.TransToState("exit", "Normal"));
  
  Petri.add_arc pmodel (Petri.StateToTrans("Want", "enter"));
  Petri.add_arc pmodel (Petri.TransToState("enter", "Crit"));
  
  Petri.set_state_fun pmodel state_from_proc;
  set_petri pmodel;
  let s : Scene.t = {pre_init; post_init=draw_for_state; on_model_change=draw_for_state; update; } in 
  set_scene(s)
