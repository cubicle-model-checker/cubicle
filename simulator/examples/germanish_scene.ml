(*                                     *)
(*  An example scene for "germanish"   *) 
(*  using the petri net scene library. *)
(*                                     *)

open Simulator
open Petrilib

let state_from_proc i = 
  match get_vuv_for_proc "Cache" i with
  | VConstr(s) -> s
  | _          -> failwith "Wrong model : Cache is not a constr"


let indic_someone_want_exclusive () = 
  match get_vuv_const "Curcmd" with  
  | VConstr("Reqe") -> true
  | _               -> false

let indic_someone_want_shared () = 
  match get_vuv_const "Curcmd" with
  | VConstr("Reqs") -> true
  | _ -> false 

let button_request_shared () =
  Simulator.take_transition "req_shared" [(Utils.get_random_proc ())]

let button_request_exclusive () =
  Simulator.take_transition "req_exclusive" [(Utils.get_random_proc ())]

let build_scene () =

  let pmodel = Petri.empty () in

  Petri.add_state pmodel "Invalid" {x=100; y=100};
  Petri.add_state pmodel "Shared" {x=500;y=800};
  Petri.add_state pmodel "Exclusive" {x=900;y=100};

  Petri.add_indic pmodel "Someone want shared" indic_someone_want_shared {x=1000; y = 600}; 
  Petri.add_indic pmodel "Someone want exclusive" indic_someone_want_exclusive {x=1000; y = 500}; 
  Petri.add_button pmodel "Request exclusive" button_request_exclusive {x = 1000; y = 400 };
  Petri.add_button pmodel "Request shared" button_request_shared {x = 1000; y = 300 };

  (* Create trans *)
  Petri.add_trans pmodel "get shared"     (["gnt_shared"], {x=250; y=450});
  Petri.add_trans pmodel "get exclusive"  (["gnt_exclusive"], {x=500; y=200});
  Petri.add_trans pmodel "goto invalid"   (["inv_2"; "inv_1"], {x=500;y=450});

  (* Create arcs *)
  Petri.add_arc pmodel (Petri.StateToTrans("Invalid", "get shared"));
  Petri.add_arc pmodel (Petri.TransToState("get shared", "Shared"));
  
  Petri.add_arc pmodel (Petri.StateToTrans("Invalid", "get exclusive"));
  Petri.add_arc pmodel (Petri.TransToState("get exclusive", "Exclusive"));

  Petri.add_arc pmodel (Petri.TransToState("goto invalid", "Invalid"));
  Petri.add_arc pmodel (Petri.StateToTrans("Exclusive", "goto invalid"));
  Petri.add_arc pmodel (Petri.StateToTrans("Shared", "goto invalid"));

  Petri.set_state_fun pmodel state_from_proc;

  set_petri pmodel;
  
  let s : Scene.t = {pre_init; post_init=draw_for_state; on_model_change=draw_for_state; update; } in 
  set_scene(s)
