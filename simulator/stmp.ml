open Shelp

let vTurn = ref 0
let vWant = Array.make (get_nb_proc ()) true
let vCrit = Array.make (get_nb_proc ()) true

let init () = 
	for z = 0 to get_nb_proc () do 
		vWant.(z) <- false;
 		vCrit.(z) <- false;
 	done;
	vTurn := get_random_proc ();
	()

let req_req args = 
	let i = find_ieme args 0 in
	vWant.(i) = false

let ac_req args = 
	let i = find_ieme args 0 in
	for j = 0 to (get_nb_proc ()) do 
 		let newval = 
			if i=j then true
			else vWant.(j)
		in vWant.(j) <- newval
	done; 
	()

let req = ("req", req_req, ac_req) 

let req_enter args = 
	let i = find_ieme args 0 in
	(!vTurn) = i && vWant.(i) = true && vCrit.(i) = false

let ac_enter args = 
	let i = find_ieme args 0 in
	for j = 0 to (get_nb_proc ()) do 
 		let newval = 
			if i=j then true
			else vCrit.(j)
		in vCrit.(j) <- newval
	done; 
	()

let enter = ("enter", req_enter, ac_enter) 

let req_exit args = 
	let i = find_ieme args 0 in
	vCrit.(i) = true

let ac_exit args = 
	let i = find_ieme args 0 in
	vTurn := get_random_proc ();
	for j = 0 to (get_nb_proc ()) do 
 		let newval = 
			if i=j then false
			else vCrit.(j)
		in vCrit.(j) <- newval
	done; 
	for j = 0 to (get_nb_proc ()) do 
 		let newval = 
			if i=j then false
			else vWant.(j)
		in vWant.(j) <- newval
	done; 
	()

let exit = ("exit", req_exit, ac_exit) 


let build_table = 
	add_req_acc 1 req;
	add_req_acc 1 enter;
	add_req_acc 1 exit;

