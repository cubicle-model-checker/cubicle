(*                                     *)
(*  An example scene for "germanish"   *) 
(*  using the petri net scene library. *)
(*                                     *)

open Utils
open Simulator
open Scenelib

let state_from_proc i = 
  match (get_vuv "Cache") with
  | Arr(a) -> 
      begin match List.nth a i with
      (* Could be done with
      | VConstr(s)  -> s
      But we would lose the error of a wrong model, changing it for an error in the scene.
      *)
      | VConstr("Invalid")    -> "Invalid"
      | VConstr("Shared")     -> "Shared"
      | VConstr("Exclusive")  -> "Exclusive"
      | _                     -> failwith "Wrong model"
      end 
  | _ -> failwith "Wrong Model : No cache"


let indic_someone_want_exclusive () = 
  match (get_vuv "Curcmd") with  
  | Val(v) ->
      begin match v with
      | VConstr("Reqe") -> true
      | _ -> false
      end
  | _ -> failwith "Wrong Model : No Curcmd"

let indic_someone_want_shared () = 
  match (get_vuv "Curcmd") with
  | Val(v) -> 
      begin match v with 
      | VConstr("Reqs") -> true
      | _ -> false 
      end 
  | _ -> failwith "Wrong Model : No Curcmd"

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

  Scenelib.set_petri pmodel;
  
  let s : Scene.t = {pre_init; post_init=draw_for_state; on_model_change=draw_for_state; update; } in 
  set_scene(s)
