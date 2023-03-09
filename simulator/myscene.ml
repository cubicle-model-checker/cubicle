open Utils
open Simulator
open Scenelib

(*
  An example scene for Dekker using the petri net scene library
*)

let state_from_proc i = 
  let m1 = 
  match (get_vuv "Want") with
  | Arr(a) -> a
  | _ -> failwith "Wrong model : No Want"
  in
  let m2 = 
  match (get_vuv "Crit") with
  | Arr(a) -> a
  | _ -> failwith "Wrong model : No Crit"
  in
  let v1 = match (List.nth m1 i) with
  | VBool(b) -> b
  | _ -> failwith "Wrong model : Want is not vbool"
  in
  let v2 = match (List.nth m2 i) with
  | VBool(b) -> b
  | _ -> failwith "Wrong model : Crit is not vbool"
  in
  if v2 then 2 else
  if v1 then 1 else
  0

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
