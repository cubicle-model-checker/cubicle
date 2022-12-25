open Shelp
type t = A | B

let vX = ref A
let vY = ref A
let vZ = ref 0
let vE = ref 0
let vF = ref true
let vHello = Array.make (get_nb_proc ()) A
let vBonjour = Array.make (get_nb_proc ()) A

let init () = 
	vX := A;
	vZ := 2;
	vY := get_random_in_list [A; B];
	vE := get_random_proc ();
	vF := Random.bool ()
let req_t2 args = 
	let i = find_ieme args 0 in
	(!vX) = B && (!vZ) = 2
let ac_t2 args = 
	let i = find_ieme args 0 in
	let assign () =
		vX := A
	in
	let nondets () =
		vY := get_random_in_list [A; B]
	in
	let update () = 
		()
	in
 assign (); nondets (); update ()
let t2 = ("t2", req_t2, ac_t2) 

let req_t1 args = 
	let i = find_ieme args 0 in
	let j = find_ieme args 1 in
	(!vX) = A
let ac_t1 args = 
	let i = find_ieme args 0 in
	let j = find_ieme args 1 in
	let assign () =
		vX := B;
		vY := A;
		vE := i
	in
	let nondets () =
		()
	in
	let update () = 
		let val = in vHello.(_j1) <- val
A _j1j
vHello.(_j1) let val = in vBonjour.(_j2) <- val
B _j2i
vBonjour.(_j2) 
	in
 assign (); nondets (); update ()
let t1 = ("t1", req_t1, ac_t1) 


let build_table = 
	add_req_acc 1 t2;
	add_req_acc 2 t1;

