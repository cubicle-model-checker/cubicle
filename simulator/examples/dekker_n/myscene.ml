(*                                     *)
(*  An example scene for "dekker_n"   *) 
(*  using the petri net scene library. *)
(*                                     *)

open Utils
open Simulator
open Petrilib

let state_from_proc i = 
  match (get_vuv "P") with
  | Arr(a) -> 
      begin match List.nth a i with
      (* Could be done with
      | VConstr(s)  -> s
      But we would lose the error of a wrong model, changing it for an error in the scene.
      *)
      | VConstr("NCS")    -> "NCS"
      | VConstr("LOOP")   -> "LOOP"
      | VConstr("AWAIT")  -> "AWAIT"
      | VConstr("TURN")   -> "TURN"
      | VConstr("CS")     -> "CS"
      | _                 -> failwith "Wrong model"
      end 
  | _ -> failwith "Wrong Model : No P"


let build_scene () =

  let pmodel = Petri.empty () in

  Petri.add_state pmodel "NCS" {x=200; y=100};
  Petri.add_state pmodel "LOOP" {x=100; y=500};
  Petri.add_state pmodel "AWAIT" {x=450; y=800};
  Petri.add_state pmodel "TURN" {x=800; y=500};
  Petri.add_state pmodel "CS" {x=700; y=100};

  (* Create trans *)
  Petri.add_trans pmodel "start"    (["start"], {x=150; y=300});
  Petri.add_trans pmodel "wait"     (["wait"], {x=275; y=650});
  Petri.add_trans pmodel "enter"    (["enter"], {x=400;y=300});
  Petri.add_trans pmodel "loop"     (["loop"], {x=450;y=100});
  Petri.add_trans pmodel "turn"     (["turn"], {x=450;y=500});
  Petri.add_trans pmodel "awaited"  (["awaited_1"; "awaited_2"], {x=575;y=650});
  
  (* Create arcs *)
  Petri.add_arc pmodel (Petri.StateToTrans("NCS", "start"));
  Petri.add_arc pmodel (Petri.TransToState("start", "LOOP"));
  
  Petri.add_arc pmodel (Petri.StateToTrans("LOOP", "wait"));
  Petri.add_arc pmodel (Petri.TransToState("wait", "AWAIT"));

  Petri.add_arc pmodel (Petri.StateToTrans("LOOP", "enter"));
  Petri.add_arc pmodel (Petri.TransToState("enter", "CS"));
  
  Petri.add_arc pmodel (Petri.StateToTrans("CS", "loop"));
  Petri.add_arc pmodel (Petri.TransToState("loop", "NCS"));

  Petri.add_arc pmodel (Petri.StateToTrans("TURN", "turn"));
  Petri.add_arc pmodel (Petri.TransToState("turn", "LOOP"));
  
  Petri.add_arc pmodel (Petri.StateToTrans("AWAIT", "awaited"));
  Petri.add_arc pmodel (Petri.TransToState("awaited", "TURN"));
  
  Petri.set_state_fun pmodel state_from_proc;

  set_petri pmodel;
  
  let s : Scene.t = {pre_init; post_init=draw_for_state; on_model_change=draw_for_state; update; } in 
  set_scene(s)
