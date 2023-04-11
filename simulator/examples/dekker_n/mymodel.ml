open Utils
open Maps
open Model
open Traces
open Format

let build_model () =
let location = ["NCS" ; "LOOP" ; "AWAIT" ; "TURN" ; "CS"] in

let vT = ref 0 in
let vT_set = ref true in
let vP = Array.make (get_nb_proc ()) ("NCS") in
let vX = Array.make (get_nb_proc ()) (true) in

let state_getter () = 
	let ret = ref StringMap.empty in 
	let add_to_ret n v = ret := StringMap.add n v (!ret) in 
	add_to_ret "P" (Arr(List.map (fun x -> VConstr(x)) (Array.to_list vP)));
	add_to_ret "X" (Arr(List.map (fun x -> VBool(x)) (Array.to_list vX)));
	add_to_ret "T" (Val(VInt(!vT)));
	add_to_ret "T_set" (Val(VBool(!vT_set)));
	!ret
in

let state_setter state = 
	let set_vuv vname vval = 
		match vname, vval with 
			| "P", Arr(a) -> List.iteri (fun i x -> match x with | VConstr(v) -> vP.(i) <- v | _ -> failwith "Unknown") a
			| "X", Arr(a) -> List.iteri (fun i x -> match x with | VBool(v) -> vX.(i) <- v | _ -> failwith "Unknown") a
			| "T", Val(VInt(v)) -> vT := v
			| "T_set", Val(VBool(v)) -> vT_set := v
			| _, _ -> failwith "Unknown"
		in
	StringMap.iter set_vuv state
in

let init () = 
	vT_set := false;
	vT := get_random_proc ();
	for tmp_0 = 0 to (get_nb_proc () - 1) do 
		vX.(tmp_0) <- false;
		vP.(tmp_0) <- "NCS";
	done;
	()
in

let unsafe_0 args = 
	let i = List.nth args 0 in
	let j = List.nth args 1 in
	vP.(i) = "CS" &&
	vP.(j) = "CS" &&
	true
in

let req_awaited_1 args = 
	let i = List.nth args 0 in
	!(vT_set) = false && vP.(i) = "AWAIT" && 
	true
in

let ac_awaited_1 args = 
	let i = List.nth args 0 in
	let nP = Array.make (get_nb_proc ()) ("NCS") in
	for _j6 = 0 to ((get_nb_proc ()) - 1) do 
 		nP.(_j6) <- if _j6 = i && true then "TURN" else vP.(_j6)
	done; 
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vP.(tmp_0) <- nP.(tmp_0);
	done;
	()
in

let awaited_1 = ("awaited_1", req_awaited_1, ac_awaited_1) 
in

let req_awaited_2 args = 
	let i = List.nth args 0 in
	!(vT) = i && !(vT_set) = true && vP.(i) = "AWAIT" && 
	true
in

let ac_awaited_2 args = 
	let i = List.nth args 0 in
	let nP = Array.make (get_nb_proc ()) ("NCS") in
	for _j7 = 0 to ((get_nb_proc ()) - 1) do 
 		nP.(_j7) <- if _j7 = i && true then "TURN" else vP.(_j7)
	done; 
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vP.(tmp_0) <- nP.(tmp_0);
	done;
	()
in

let awaited_2 = ("awaited_2", req_awaited_2, ac_awaited_2) 
in

let req_enter args = 
	let i = List.nth args 0 in
	vP.(i) = "LOOP" && 
	(forall_other (fun j -> vX.(j) = false && true) args) && 
	true
in

let ac_enter args = 
	let i = List.nth args 0 in
	let nP = Array.make (get_nb_proc ()) ("NCS") in
	for _j5 = 0 to ((get_nb_proc ()) - 1) do 
 		nP.(_j5) <- if _j5 = i && true then "CS" else vP.(_j5)
	done; 
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vP.(tmp_0) <- nP.(tmp_0);
	done;
	()
in

let enter = ("enter", req_enter, ac_enter) 
in

let req_start args = 
	let i = List.nth args 0 in
	vP.(i) = "NCS" && 
	true
in

let ac_start args = 
	let i = List.nth args 0 in
	let nP = Array.make (get_nb_proc ()) ("NCS") in
	for _j1 = 0 to ((get_nb_proc ()) - 1) do 
 		nP.(_j1) <- if _j1 = i && true then "LOOP" else vP.(_j1)
	done; 
	let nX = Array.make (get_nb_proc ()) (true) in
	for _j2 = 0 to ((get_nb_proc ()) - 1) do 
 		nX.(_j2) <- if _j2 = i && true then true else vX.(_j2)
	done; 
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vX.(tmp_0) <- nX.(tmp_0);
		vP.(tmp_0) <- nP.(tmp_0);
	done;
	()
in

let start = ("start", req_start, ac_start) 
in

let req_turn args = 
	let i = List.nth args 0 in
	vP.(i) = "TURN" && 
	true
in

let ac_turn args = 
	let i = List.nth args 0 in
	let nT_set = true in 
	let nT = i in 
	let nP = Array.make (get_nb_proc ()) ("NCS") in
	for _j8 = 0 to ((get_nb_proc ()) - 1) do 
 		nP.(_j8) <- if _j8 = i && true then "LOOP" else vP.(_j8)
	done; 
	let nX = Array.make (get_nb_proc ()) (true) in
	for _j9 = 0 to ((get_nb_proc ()) - 1) do 
 		nX.(_j9) <- if _j9 = i && true then true else vX.(_j9)
	done; 
	vT_set := nT_set;
	vT := nT;
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vX.(tmp_0) <- nX.(tmp_0);
		vP.(tmp_0) <- nP.(tmp_0);
	done;
	()
in

let turn = ("turn", req_turn, ac_turn) 
in

let req_loop args = 
	let i = List.nth args 0 in
	vP.(i) = "CS" && 
	true
in

let ac_loop args = 
	let i = List.nth args 0 in
	let nT_set = false in 
	let nP = Array.make (get_nb_proc ()) ("NCS") in
	for _j10 = 0 to ((get_nb_proc ()) - 1) do 
 		nP.(_j10) <- if _j10 = i && true then "NCS" else vP.(_j10)
	done; 
	let nX = Array.make (get_nb_proc ()) (true) in
	for _j11 = 0 to ((get_nb_proc ()) - 1) do 
 		nX.(_j11) <- if _j11 = i && true then false else vX.(_j11)
	done; 
	vT_set := nT_set;
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vX.(tmp_0) <- nX.(tmp_0);
		vP.(tmp_0) <- nP.(tmp_0);
	done;
	()
in

let loop = ("loop", req_loop, ac_loop) 
in

let req_wait args = 
	let i = List.nth args 0 in
	let j = List.nth args 1 in
	vP.(i) = "LOOP" && vX.(j) = true && 
	true
in

let ac_wait args = 
	let i = List.nth args 0 in
	let j = List.nth args 1 in
	let nP = Array.make (get_nb_proc ()) ("NCS") in
	for _j3 = 0 to ((get_nb_proc ()) - 1) do 
 		nP.(_j3) <- if _j3 = i && true then "AWAIT" else vP.(_j3)
	done; 
	let nX = Array.make (get_nb_proc ()) (true) in
	for _j4 = 0 to ((get_nb_proc ()) - 1) do 
 		nX.(_j4) <- if _j4 = i && true then false else vX.(_j4)
	done; 
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vX.(tmp_0) <- nX.(tmp_0);
		vP.(tmp_0) <- nP.(tmp_0);
	done;
	()
in

let wait = ("wait", req_wait, ac_wait) 
in


let mymodel = ref Model.empty in

mymodel := Model.add_trans 1 awaited_1 (!mymodel);
mymodel := Model.add_trans 1 awaited_2 (!mymodel);
mymodel := Model.add_trans 1 enter (!mymodel);
mymodel := Model.add_trans 1 start (!mymodel);
mymodel := Model.add_trans 1 turn (!mymodel);
mymodel := Model.add_trans 1 loop (!mymodel);
mymodel := Model.add_trans 2 wait (!mymodel);
mymodel := Model.add_unsafe 2 unsafe_0 (!mymodel);
mymodel := Model.set_init init (!mymodel);
mymodel := Model.set_vars ([], state_getter, state_setter) (!mymodel);
set_model (!mymodel)
