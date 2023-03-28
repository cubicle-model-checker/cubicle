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
      But we would lose the error of a wrong model, changing it for an error of a scene.
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


let build_scene () =

  let pmodel = Petri.empty () in

  Petri.add_state pmodel "Invalid" {x=100; y=100};
  Petri.add_state pmodel "Shared" {x=500;y=800};
  Petri.add_state pmodel "Exclusive" {x=900;y=100};

  Petri.add_indic pmodel "Someone want exclusive" indic_someone_want_exclusive {x=1000; y = 500}; 

  Petri.add_trans pmodel "get shared"     (["gnt_shared"], {x=250; y=450});
  Petri.add_trans pmodel "get exclusive"  (["gnt_exclusive"], {x=500; y=200});
  Petri.add_trans pmodel "quit exclusive" (["inv_2"], {x=500;y=100});
  Petri.add_trans pmodel "quit shared"    (["inv_1"], {x=350;y=300});

  (* TODO : 
  * Create Goto invalid
  *)

  Petri.add_arc pmodel (Petri.StateToTrans("Invalid", "get shared"));
  Petri.add_arc pmodel (Petri.TransToState("get shared", "Shared"));
  
  Petri.add_arc pmodel (Petri.StateToTrans("Invalid", "get exclusive"));
  Petri.add_arc pmodel (Petri.TransToState("get exclusive", "Exclusive"));

  Petri.add_arc pmodel (Petri.TransToState("quit exclusive", "Invalid"));
  Petri.add_arc pmodel (Petri.StateToTrans("Exclusive", "quit exclusive"));
  
  Petri.add_arc pmodel (Petri.TransToState("quit shared", "Invalid"));
  Petri.add_arc pmodel (Petri.StateToTrans("Shared", "quit shared"));

  (*
  Petri.add_trans pmodel "req" (["req"], {x=200; y=300});
  Petri.add_trans pmodel "get shared" (["enter"], {x=400; y=300});
  Petri.add_trans pmodel "exit" (["exit"], {x=300;y=100});

  Petri.add_arc pmodel (Petri.StateToTrans("Invalid", "req"));
  Petri.add_arc pmodel (Petri.TransToState("req", "Shared"));
  *)
  (*
  Petri.add_arc pmodel (Petri.StateToTrans("Shared", "get shared"));
  Petri.add_arc pmodel (Petri.TransToState("get shared", "Exclusive"));
  Petri.add_arc pmodel (Petri.StateToTrans("Exclusive", "exit"));
  Petri.add_arc pmodel (Petri.TransToState("exit", "Invalid"));
  *)
  Petri.set_state_fun pmodel state_from_proc;

  Scenelib.set_petri pmodel;
  
  let s = (pre_init, draw_for_state, draw_for_state, update) in 
  set_scene(s)
