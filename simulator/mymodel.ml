open Utils
open Model
open Format

let build_model () =

let vTurn = ref 0 in
let vWant = Array.make (get_nb_proc ()) (true) in
let vCrit = Array.make (get_nb_proc ()) (true) in

let state_getter () = 
	let ret = ref StringMap.empty in 
	let add_to_ret n v = ret := StringMap.add n v (!ret) in 
	add_to_ret "Turn" (Val(VInt(!vTurn)));
	add_to_ret "Want" (Arr(List.map (fun x -> VBool(x)) (Array.to_list vWant)));
	add_to_ret "Crit" (Arr(List.map (fun x -> VBool(x)) (Array.to_list vCrit)));
	!ret
in

let state_setter state = 
	let set_vuv vname vval = 
		match vname, vval with 
			| "Turn", Val(VInt(v)) -> vTurn := v
			| "Want", Arr(a) -> List.iteri (fun i x -> match x with | VBool(v) -> vWant.(i) <- v | _ -> failwith "Unknown") a
			| "Crit", Arr(a) -> List.iteri (fun i x -> match x with | VBool(v) -> vCrit.(i) <- v | _ -> failwith "Unknown") a
			| _, _ -> failwith "Unknown"
		in
	StringMap.iter set_vuv state
in

let init () = 
	vTurn := get_random_proc ();
	for tmp_0 = 0 to (get_nb_proc () - 1) do 
		vWant.(tmp_0) <- false;
		vCrit.(tmp_0) <- false;
	done;
	()
in

let req_req args = 
	let i = List.nth args 0 in
	vWant.(i) = false && 
	true
in

let ac_req args = 
	let i = List.nth args 0 in
	let nWant = Array.make (get_nb_proc ()) (true) in
	for _j1 = 0 to ((get_nb_proc ()) - 1) do 
 		nWant.(_j1) <- if _j1 = i && true then true else vWant.(_j1)
	done; 
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vWant.(tmp_0) <- nWant.(tmp_0);
	done;
	()
in

let req = ("req", req_req, ac_req) 
in

let req_enter args = 
	let i = List.nth args 0 in
	!(vTurn) = i && vWant.(i) = true && vCrit.(i) = false && 
	true
in

let ac_enter args = 
	let i = List.nth args 0 in
	let nCrit = Array.make (get_nb_proc ()) (true) in
	for _j2 = 0 to ((get_nb_proc ()) - 1) do 
 		nCrit.(_j2) <- if _j2 = i && true then true else vCrit.(_j2)
	done; 
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vCrit.(tmp_0) <- nCrit.(tmp_0);
	done;
	()
in

let enter = ("enter", req_enter, ac_enter) 
in

let req_exit args = 
	let i = List.nth args 0 in
	vCrit.(i) = true && 
	true
in

let ac_exit args = 
	let i = List.nth args 0 in
	let nTurn = get_random_proc () in
	let nCrit = Array.make (get_nb_proc ()) (true) in
	for _j3 = 0 to ((get_nb_proc ()) - 1) do 
 		nCrit.(_j3) <- if _j3 = i && true then false else vCrit.(_j3)
	done; 
	let nWant = Array.make (get_nb_proc ()) (true) in
	for _j4 = 0 to ((get_nb_proc ()) - 1) do 
 		nWant.(_j4) <- if _j4 = i && true then false else vWant.(_j4)
	done; 
	vTurn := nTurn;
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vWant.(tmp_0) <- nWant.(tmp_0);
		vCrit.(tmp_0) <- nCrit.(tmp_0);
	done;
	()
in

let exit = ("exit", req_exit, ac_exit) 
in


let mymodel = ref Model.empty in

mymodel := Model.add_trans 1 req (!mymodel);
mymodel := Model.add_trans 1 enter (!mymodel);
mymodel := Model.add_trans 1 exit (!mymodel);
mymodel := Model.set_init init (!mymodel);
mymodel := Model.set_vars ([], state_getter, state_setter) (!mymodel);
set_model (!mymodel)
