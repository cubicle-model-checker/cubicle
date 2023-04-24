open Utils
open Maps
open Model
open Traces
open Format
let build_model () = 

let direction = ["Up" ; "Down"] in

let vCurFloor = ref 0 in
let vMoving = ref true in
let vDir = ref "Up" in
let vG_Clock = ref 0 in
let vRequest = Array.make (get_nb_proc ()) (true) in
let vG_RequestTime = Array.make (get_nb_proc ()) (0) in
let vG_LastVisit = Array.make (get_nb_proc ()) (0) in
let vG_LastStop = Array.make (get_nb_proc ()) (0) in
let vNext = Array.make (get_nb_proc ()) (0) in

let state_getter () = 
	let ret = ref StringMap.empty in 
	let add_to_ret n v = ret := StringMap.add n v (!ret) in 
	add_to_ret "CurFloor" (Val(VInt(!vCurFloor)));
	add_to_ret "Moving" (Val(VBool(!vMoving)));
	add_to_ret "Dir" (Val(VConstr(!vDir)));
	add_to_ret "Request" (Arr(List.map (fun x -> VBool(x)) (Array.to_list vRequest)));
	add_to_ret "G_Clock" (Val(VInt(!vG_Clock)));
	add_to_ret "G_RequestTime" (Arr(List.map (fun x -> VInt(x)) (Array.to_list vG_RequestTime)));
	add_to_ret "G_LastVisit" (Arr(List.map (fun x -> VInt(x)) (Array.to_list vG_LastVisit)));
	add_to_ret "G_LastStop" (Arr(List.map (fun x -> VInt(x)) (Array.to_list vG_LastStop)));
	add_to_ret "Next" (Arr(List.map (fun x -> VInt(x)) (Array.to_list vNext)));
	!ret
in

let state_setter state = 
	let set_vuv vname vval = 
		match vname, vval with 
			| "CurFloor", Val(VInt(v)) -> vCurFloor := v
			| "Moving", Val(VBool(v)) -> vMoving := v
			| "Dir", Val(VConstr(v)) -> vDir := v
			| "Request", Arr(a) -> List.iteri (fun i x -> match x with | VBool(v) -> vRequest.(i) <- v | _ -> failwith "Unknown") a
			| "G_Clock", Val(VInt(v)) -> vG_Clock := v
			| "G_RequestTime", Arr(a) -> List.iteri (fun i x -> match x with | VInt(v) -> vG_RequestTime.(i) <- v | _ -> failwith "Unknown") a
			| "G_LastVisit", Arr(a) -> List.iteri (fun i x -> match x with | VInt(v) -> vG_LastVisit.(i) <- v | _ -> failwith "Unknown") a
			| "G_LastStop", Arr(a) -> List.iteri (fun i x -> match x with | VInt(v) -> vG_LastStop.(i) <- v | _ -> failwith "Unknown") a
			| "Next", Arr(a) -> List.iteri (fun i x -> match x with | VInt(v) -> vNext.(i) <- v | _ -> failwith "Unknown") a
			| _, _ -> failwith "Unknown"
		in
	StringMap.iter set_vuv state
in

let init () = 
	vMoving := false;
	vDir := "Up";
	vCurFloor := get_random_proc ();
	vG_Clock := 1;
	for tmp_0 = 0 to (get_nb_proc () - 1) do 
		vRequest.(tmp_0) <- false;
		vNext.(tmp_0) <- get_random_proc ();
		vG_RequestTime.(tmp_0) <- 0;
		vG_LastVisit.(tmp_0) <- 0;
		vG_LastStop.(tmp_0) <- 0;
	done;
	()
in

let unsafe_0 args = 
	let p = List.nth args 0 in
	!(vMoving) = false &&
	vRequest.(p) = true &&
	vG_RequestTime.(p) < vG_LastVisit.(p) &&
	vG_LastStop.(p) < vG_LastVisit.(p) &&
	true
in

let req_t_change_direction_up args = 
	!(vMoving) = false && !(vDir) = "Down" && 
	(forall_other (fun q -> !(vCurFloor) <= q || vRequest.(q) = false || false) args) && 
	true
in

let ac_t_change_direction_up args = 
	let nDir = "Up" in 
	let nG_Clock = !(vG_Clock) + 1 in 
	vG_Clock := nG_Clock;
	vDir := nDir;
	()
in

let t_change_direction_up = ("t_change_direction_up", req_t_change_direction_up, ac_t_change_direction_up) 
in

let req_t_change_direction_down args = 
	!(vMoving) = false && !(vDir) = "Up" && 
	(forall_other (fun q -> q <= !(vCurFloor) || vRequest.(q) = false || false) args) && 
	true
in

let ac_t_change_direction_down args = 
	let nDir = "Down" in 
	let nG_Clock = !(vG_Clock) + 1 in 
	vG_Clock := nG_Clock;
	vDir := nDir;
	()
in

let t_change_direction_down = ("t_change_direction_down", req_t_change_direction_down, ac_t_change_direction_down) 
in

let req_t_start_move_up args = 
	let q = List.nth args 0 in
	!(vCurFloor) < q && !(vMoving) = false && !(vDir) = "Up" && vRequest.(q) = true && 
	true
in

let ac_t_start_move_up args = 
	let q = List.nth args 0 in
	let nMoving = true in 
	let nG_Clock = !(vG_Clock) + 1 in 
	vMoving := nMoving;
	vG_Clock := nG_Clock;
	()
in

let t_start_move_up = ("t_start_move_up", req_t_start_move_up, ac_t_start_move_up) 
in

let req_t_start_move_down args = 
	let q = List.nth args 0 in
	q < !(vCurFloor) && !(vMoving) = false && !(vDir) = "Down" && vRequest.(q) = true && 
	true
in

let ac_t_start_move_down args = 
	let q = List.nth args 0 in
	let nMoving = true in 
	let nG_Clock = !(vG_Clock) + 1 in 
	vMoving := nMoving;
	vG_Clock := nG_Clock;
	()
in

let t_start_move_down = ("t_start_move_down", req_t_start_move_down, ac_t_start_move_down) 
in

let req_t_request args = 
	let p = List.nth args 0 in
	p <> !(vCurFloor) && vRequest.(p) = false && 
	true
in

let ac_t_request args = 
	let p = List.nth args 0 in
	let nG_Clock = !(vG_Clock) + 1 in 
	let nRequest = Array.make (get_nb_proc ()) (true) in
	for _j1 = 0 to ((get_nb_proc ()) - 1) do 
 		nRequest.(_j1) <- if _j1 = p && true then true else vRequest.(_j1)
	done; 
	let nG_RequestTime = Array.make (get_nb_proc ()) (0) in
	for _j2 = 0 to ((get_nb_proc ()) - 1) do 
 		nG_RequestTime.(_j2) <- if _j2 = p && true then !(vG_Clock) else vG_RequestTime.(_j2)
	done; 
	vG_Clock := nG_Clock;
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vG_RequestTime.(tmp_0) <- nG_RequestTime.(tmp_0);
		vRequest.(tmp_0) <- nRequest.(tmp_0);
	done;
	()
in

let t_request = ("t_request", req_t_request, ac_t_request) 
in

let req_t_stop args = 
	let p = List.nth args 0 in
	p = !(vCurFloor) && !(vMoving) = true && vRequest.(p) = true && 
	true
in

let ac_t_stop args = 
	let p = List.nth args 0 in
	let nMoving = false in 
	let nG_Clock = !(vG_Clock) + 1 in 
	let nRequest = Array.make (get_nb_proc ()) (true) in
	for _j5 = 0 to ((get_nb_proc ()) - 1) do 
 		nRequest.(_j5) <- if _j5 = p && true then false else vRequest.(_j5)
	done; 
	let nG_LastStop = Array.make (get_nb_proc ()) (0) in
	for _j6 = 0 to ((get_nb_proc ()) - 1) do 
 		nG_LastStop.(_j6) <- if _j6 = p && true then !(vG_Clock) else vG_LastStop.(_j6)
	done; 
	vMoving := nMoving;
	vG_Clock := nG_Clock;
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vG_LastStop.(tmp_0) <- nG_LastStop.(tmp_0);
		vRequest.(tmp_0) <- nRequest.(tmp_0);
	done;
	()
in

let t_stop = ("t_stop", req_t_stop, ac_t_stop) 
in

let req_t_move_up args = 
	let p = List.nth args 0 in
	let q = List.nth args 1 in
	p = !(vCurFloor) && q = vNext.(p) && !(vMoving) = true && !(vDir) = "Up" && vRequest.(p) = false && 
	true
in

let ac_t_move_up args = 
	let p = List.nth args 0 in
	let q = List.nth args 1 in
	let nCurFloor = vNext.(p) in 
	let nG_Clock = !(vG_Clock) + 1 in 
	let nG_LastVisit = Array.make (get_nb_proc ()) (0) in
	for _j3 = 0 to ((get_nb_proc ()) - 1) do 
 		nG_LastVisit.(_j3) <- if _j3 = q && true then !(vG_Clock) + 1 else vG_LastVisit.(_j3)
	done; 
	vG_Clock := nG_Clock;
	vCurFloor := nCurFloor;
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vG_LastVisit.(tmp_0) <- nG_LastVisit.(tmp_0);
	done;
	()
in

let t_move_up = ("t_move_up", req_t_move_up, ac_t_move_up) 
in

let req_t_move_down args = 
	let p = List.nth args 0 in
	let q = List.nth args 1 in
	p = !(vCurFloor) && p = vNext.(q) && !(vMoving) = true && !(vDir) = "Down" && vRequest.(p) = false && 
	true
in

let ac_t_move_down args = 
	let p = List.nth args 0 in
	let q = List.nth args 1 in
	let nCurFloor = q in 
	let nG_Clock = !(vG_Clock) + 1 in 
	let nG_LastVisit = Array.make (get_nb_proc ()) (0) in
	for _j4 = 0 to ((get_nb_proc ()) - 1) do 
 		nG_LastVisit.(_j4) <- if _j4 = q && true then !(vG_Clock) + 1 else vG_LastVisit.(_j4)
	done; 
	vG_Clock := nG_Clock;
	vCurFloor := nCurFloor;
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vG_LastVisit.(tmp_0) <- nG_LastVisit.(tmp_0);
	done;
	()
in

let t_move_down = ("t_move_down", req_t_move_down, ac_t_move_down) 
in


let mymodel = ref Model.empty in

mymodel := Model.add_trans 0 t_change_direction_up (!mymodel);
mymodel := Model.add_trans 0 t_change_direction_down (!mymodel);
mymodel := Model.add_trans 1 t_start_move_up (!mymodel);
mymodel := Model.add_trans 1 t_start_move_down (!mymodel);
mymodel := Model.add_trans 1 t_request (!mymodel);
mymodel := Model.add_trans 1 t_stop (!mymodel);
mymodel := Model.add_trans 2 t_move_up (!mymodel);
mymodel := Model.add_trans 2 t_move_down (!mymodel);
mymodel := Model.add_unsafe 1 unsafe_0 (!mymodel);
mymodel := Model.set_init init (!mymodel);
mymodel := Model.set_vars ([], state_getter, state_setter) (!mymodel);
set_model (!mymodel)
